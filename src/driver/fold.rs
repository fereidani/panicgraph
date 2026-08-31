//! Constant folding of the branches a build cannot take.
//!
//! MIR is generic. The standard library keeps one body per function, so a
//! check written against `size_of::<T>()` is still a live branch there even
//! though it settles to a constant for every real `T`. Codegen resolves it
//! per instantiation and never emits the failing arm; an analysis that walks
//! the arm anyway reports a panic no binary contains.
//!
//! This pass answers the same two questions codegen does, for one body at a
//! time: which blocks does this instantiation reach, and which of its checks
//! cannot fail. It only ever claims a value it can prove, so a body it
//! cannot follow is left exactly as it was found.
//!
//! A value the body did not compute itself is followed as far as it goes.
//! Where two arms of a branch meet, what they agree on survives as a range
//! rather than being given up, and a call is read for what its body returns,
//! so `right.max(1)` is known nonzero and the division below it raises
//! nothing.

use rustc_middle::{
    mir::{self, BasicBlock, BinOp, TerminatorKind, UnwindAction},
    ty::{self, Instance, Ty, TyCtxt, TypeVisitableExt, TypingEnv},
};

use crate::{
    sinks::SinkTable,
    state::{
        Compared, STEPS, State, Subject, Work, escaping, forget, refined,
        root_of, unwind_to, writes,
    },
    value::{self, Against, Bounds, Fact, Known, LenRel, Value, truncate},
};

/// How far a chain of calls is followed for the value it returns.
///
/// Each step is one more body on the stack, and the calls worth reading a
/// value out of sit shallow: `cmp::max` is one step above `Ord::max`, which
/// is the deepest of them.
const DEPTH: u32 = 3;

/// How many blocks folding one body may spend on the callees it reads
/// values out of.
///
/// A summary is only asked for where the answer would settle a check, so
/// the budget is rarely touched. It is what keeps a body that calls into a
/// wide subgraph from paying for all of it.
const BUDGET: u32 = 4096;

/// What one instantiation of a body reaches.
pub struct Reach {
    live: Vec<bool>,
    settled: Vec<bool>,
    quiet: Vec<bool>,
}

impl Reach {
    /// A verdict that assumes nothing, which is what an unfoldable body gets.
    fn everything(blocks: usize) -> Self {
        Self {
            live: vec![true; blocks],
            settled: vec![false; blocks],
            quiet: vec![false; blocks],
        }
    }

    /// Whether the compiler will generate code for a block.
    pub fn is_live(&self, bb: BasicBlock) -> bool {
        self.live.get(bb.as_usize()).copied().unwrap_or(true)
    }

    /// Whether a block's `Assert` was proved unable to fail.
    pub fn is_settled(&self, bb: BasicBlock) -> bool {
        self.settled.get(bb.as_usize()).copied().unwrap_or(false)
    }

    /// Whether a block's call was proved to raise nothing.
    ///
    /// The callee was walked with what this call site knows about its
    /// arguments, and every block the compiler will generate for it was
    /// found unable to raise. It says nothing about the callee anywhere
    /// else, which is why the callee is still analysed on its own.
    pub fn is_quiet(&self, bb: BasicBlock) -> bool {
        self.quiet.get(bb.as_usize()).copied().unwrap_or(false)
    }
}

/// Works out what one instantiation of a body reaches.
pub fn reachable<'tcx>(
    tcx: TyCtxt<'tcx>,
    inst: Instance<'tcx>,
    env: TypingEnv<'tcx>,
    mir: &mir::Body<'tcx>,
) -> Reach {
    let mut folder = Folder::new(tcx, inst, env, mir, 0, BUDGET);
    let entry = vec![Fact::default(); mir.local_decls.len()];
    folder.run(entry)
}

/// What every path out of a body was found to return.
#[derive(Debug, Clone, Copy)]
enum Returns<'tcx> {
    /// No path that returns has been walked.
    Never,
    /// Every such path leaves a value this claim admits.
    Held(Value<'tcx>),
    /// Nothing definite.
    Anything,
}

impl<'tcx> Returns<'tcx> {
    /// Adds what one path out of the body leaves behind.
    fn met(self, value: Option<Value<'tcx>>) -> Self {
        match (self, value) {
            (Self::Anything, _) | (_, None) => Self::Anything,
            (Self::Never, Some(found)) => Self::Held(found),
            (Self::Held(held), Some(found)) => {
                held.join(found).map_or(Self::Anything, Self::Held)
            }
        }
    }

    /// The claim every path agrees on.
    ///
    /// A body no path returns from has none: the call never comes back, so
    /// there is no value for the caller to read.
    const fn claim(self) -> Option<Value<'tcx>> {
        match self {
            Self::Held(value) => Some(value),
            Self::Never | Self::Anything => None,
        }
    }
}

/// The parts of a call the walk reads.
#[derive(Clone, Copy)]
struct Call<'a, 'tcx> {
    func: &'a mir::Operand<'tcx>,
    args: &'a [rustc_span::Spanned<mir::Operand<'tcx>>],
    destination: mir::Place<'tcx>,
    target: Option<BasicBlock>,
    unwind: UnwindAction,
}

/// What folding a callee at one call site found.
#[derive(Debug, Clone, Copy, Default)]
struct Found<'tcx> {
    /// The value every path out of the callee leaves behind.
    value: Option<Value<'tcx>>,
    /// Whether the callee, walked with these arguments, can still raise.
    quiet: bool,
}

/// The claim, when it means the same thing outside the body it was read in.
///
/// A length names a local of that body, so it says nothing anywhere else.
const fn portable(value: Value<'_>) -> Option<Value<'_>> {
    match value {
        Value::Exact(_) | Value::Other(_) | Value::Within(_) => Some(value),
        Value::Length(_) => None,
    }
}

/// Folds one body against the arguments it was instantiated with.
struct Folder<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    inst: Instance<'tcx>,
    env: TypingEnv<'tcx>,
    mir: &'a mir::Body<'tcx>,
    escaped: Vec<bool>,
    /// How many callees deep this body sits below the one being analysed.
    depth: u32,
    /// Blocks left to spend on callees, shared with every fold below this
    /// one so the whole chain costs what one body is allowed.
    budget: u32,
    /// What the walk has found the body to return.
    returns: Returns<'tcx>,
}

impl<'a, 'tcx> Folder<'a, 'tcx> {
    /// Prepares to fold one body.
    fn new(
        tcx: TyCtxt<'tcx>,
        inst: Instance<'tcx>,
        env: TypingEnv<'tcx>,
        mir: &'a mir::Body<'tcx>,
        depth: u32,
        budget: u32,
    ) -> Self {
        Self {
            tcx,
            inst,
            env,
            mir,
            escaped: escaping(mir),
            depth,
            budget,
            returns: Returns::Never,
        }
    }

    /// Whether a pointer could be aimed at a local, so its value is never
    /// assumed. A local the walk has never heard of is treated as escaping.
    fn escapes(&self, local: mir::Local) -> bool {
        self.escaped.get(local.as_usize()).copied().unwrap_or(true)
    }

    /// Runs the walk to a fixpoint.
    fn run(&mut self, entry: State<'tcx>) -> Reach {
        let blocks = self.mir.basic_blocks.len();
        let locals = self.mir.local_decls.len();
        let mut reach = Reach {
            live: vec![false; blocks],
            settled: vec![false; blocks],
            quiet: vec![false; blocks],
        };
        let mut work = Work::new(blocks);
        work.merge(mir::START_BLOCK, entry);

        // A block is recorded once and afterwards only widens, and one
        // local's claim widens at most `STEPS` times, so a block is queued
        // at most `locals * STEPS + 1` times and the walk ends within the
        // bound below.
        let bound = blocks
            .saturating_mul(locals.saturating_mul(STEPS).saturating_add(1))
            .saturating_add(blocks)
            .saturating_add(1);
        for _ in 0..bound {
            if work.is_drained() {
                return reach;
            }
            if self.budget == 0 {
                break;
            }
            self.budget = self.budget.saturating_sub(1);
            if let Some((bb, state)) = work.pop() {
                self.visit(bb, state, &mut reach, &mut work);
            }
        }
        // The bound is a proof rather than a guess, so exhausting it means
        // the walk is not shrinking as it should. Report the body as it was
        // found instead of a verdict that assumed away an unsettled branch,
        // and say nothing about what it returns: a walk cut short has not
        // seen every path out.
        self.returns = Returns::Anything;
        Reach::everything(blocks)
    }

    /// Walks one block, recording what it reaches.
    fn visit(
        &mut self,
        bb: BasicBlock,
        mut state: State<'tcx>,
        reach: &mut Reach,
        work: &mut Work<'tcx>,
    ) {
        // A block is visited again whenever a further predecessor makes its
        // state less definite, and the last visit is the one that holds. A
        // verdict about the block's own check is therefore replaced rather
        // than added to: settling it on one path says nothing about the
        // block once another path reaches it with a different value.
        if let Some(slot) = reach.settled.get_mut(bb.as_usize()) {
            *slot = false;
        }
        if let Some(slot) = reach.quiet.get_mut(bb.as_usize()) {
            *slot = false;
        }
        // The body outlives the walk, so reading it through a copy of the
        // reference leaves the walk free to record what it finds.
        let mir: &'a mir::Body<'tcx> = self.mir;
        let block = &mir.basic_blocks[bb];
        for stmt in &block.statements {
            if !self.statement(&mut state, stmt) {
                // An assumption this build contradicts. The compiler drops
                // the block, so nothing it leads to runs either.
                return;
            }
        }
        if let Some(slot) = reach.live.get_mut(bb.as_usize()) {
            *slot = true;
        }
        let Some(term) = &block.terminator else {
            return;
        };
        self.terminator(bb, &term.kind, state, reach, work);
    }

    /// Applies one statement, returning whether the block still runs.
    fn statement(
        &self,
        state: &mut State<'tcx>,
        stmt: &mir::Statement<'tcx>,
    ) -> bool {
        match &stmt.kind {
            mir::StatementKind::Assign(pair) => {
                let (place, rvalue) = &**pair;
                match place.as_local() {
                    Some(local) if !self.escapes(local) => {
                        // The value is read before the write is applied, so
                        // an rvalue naming the target reads its old value.
                        let mut fact = self.rvalue(state, rvalue);
                        forget(state, local);
                        if fact.same == Some(local) {
                            // A link to the local being written says
                            // nothing.
                            fact.same = None;
                        }
                        if let Some(slot) = state.get_mut(local.as_usize()) {
                            *slot = fact;
                        }
                    }
                    // A write into part of a place, or through a pointer.
                    // Only the base can change, since a local whose address
                    // escaped is never tracked in the first place.
                    _ => forget(state, place.local),
                }
            }
            mir::StatementKind::SetDiscriminant { place, .. } => {
                forget(state, place.local);
            }
            mir::StatementKind::StorageLive(local)
            | mir::StatementKind::StorageDead(local) => {
                forget(state, *local);
            }
            mir::StatementKind::Intrinsic(intrinsic) => {
                if let mir::NonDivergingIntrinsic::Assume(operand) =
                    &**intrinsic
                    && self
                        .exact(state, operand)
                        .is_some_and(|value| !value.truth())
                {
                    return false;
                }
            }
            mir::StatementKind::FakeRead(..)
            | mir::StatementKind::PlaceMention(..)
            | mir::StatementKind::AscribeUserType(..)
            | mir::StatementKind::Coverage(..)
            | mir::StatementKind::ConstEvalCounter
            | mir::StatementKind::Nop
            | mir::StatementKind::BackwardIncompatibleDropHint { .. } => {}
        }
        true
    }

    /// Follows a terminator into the blocks it can reach.
    fn terminator(
        &mut self,
        bb: BasicBlock,
        kind: &TerminatorKind<'tcx>,
        state: State<'tcx>,
        reach: &mut Reach,
        work: &mut Work<'tcx>,
    ) {
        match kind {
            TerminatorKind::Goto { target } => work.merge(*target, state),
            TerminatorKind::SwitchInt { discr, targets } => {
                self.branched(bb, discr, targets, state, work);
            }
            TerminatorKind::Assert {
                cond,
                expected,
                target,
                unwind,
                ..
            } => self.assertion(
                bb,
                (cond, *expected, *target),
                *unwind,
                state,
                reach,
                work,
            ),
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
                ..
            } => self.called(
                bb,
                Call {
                    func,
                    args,
                    destination: *destination,
                    target: *target,
                    unwind: *unwind,
                },
                &state,
                reach,
                work,
            ),
            TerminatorKind::Drop {
                place,
                target,
                unwind,
                drop,
                ..
            } => {
                let mut after = state.clone();
                forget(&mut after, place.local);
                work.merge(*target, after.clone());
                if let Some(drop) = *drop {
                    work.merge(drop, after);
                }
                unwind_to(*unwind, &state, work);
            }
            // What a body leaves behind is read here rather than after the
            // walk, since a local's claim only stands where it was made.
            TerminatorKind::Return => {
                let left = Self::known_at(&state, mir::RETURN_PLACE)
                    .value
                    .and_then(portable);
                self.returns = self.returns.met(left);
            }
            _ => Self::onward(kind, state, work),
        }
    }

    /// Follows a branch into each of its arms, carrying what taking that
    /// arm proves.
    fn branched(
        &self,
        bb: BasicBlock,
        discr: &mir::Operand<'tcx>,
        targets: &mir::SwitchTargets,
        state: State<'tcx>,
        work: &mut Work<'tcx>,
    ) {
        if let Some(value) = self.exact(&state, discr) {
            work.merge(targets.target_for_value(value.bits), state);
            return;
        }
        let subject = self.subject_of(bb, discr, &state);
        let mut taken = Vec::new();
        for (value, target) in targets.iter() {
            taken.push(value);
            work.merge(target, refined(&state, subject, Some(value), true));
        }
        // The fallback covers every value not listed, so it settles the
        // condition only when one value is left over.
        let rest = match taken.as_slice() {
            [only] => Some(*only),
            _ => None,
        };
        work.merge(targets.otherwise(), refined(&state, subject, rest, false));
    }

    /// Follows a call, recording what walking the callee found.
    fn called(
        &mut self,
        bb: BasicBlock,
        call: Call<'_, 'tcx>,
        state: &State<'tcx>,
        reach: &mut Reach,
        work: &mut Work<'tcx>,
    ) {
        let mut after = state.clone();
        forget(&mut after, call.destination.local);
        let found = self.inspect(state, call.func, call.args, call.destination);
        if found.quiet
            && let Some(slot) = reach.quiet.get_mut(bb.as_usize())
        {
            *slot = true;
        }
        if let Some(value) = found.value
            && let Some(local) = call.destination.as_local()
            && !self.escapes(local)
            && let Some(slot) = after.get_mut(local.as_usize())
        {
            *slot = Fact::of(value);
        }
        if let Some(target) = call.target {
            work.merge(target, after);
        }
        unwind_to(call.unwind, state, work);
    }

    /// Follows the terminators that write nothing this walk reads.
    fn onward(
        kind: &TerminatorKind<'tcx>,
        state: State<'tcx>,
        work: &mut Work<'tcx>,
    ) {
        match kind {
            TerminatorKind::FalseEdge {
                real_target,
                imaginary_target,
            } => {
                work.merge(*real_target, state.clone());
                work.merge(*imaginary_target, state);
            }
            TerminatorKind::FalseUnwind {
                real_target,
                unwind,
            } => {
                work.merge(*real_target, state.clone());
                unwind_to(*unwind, &state, work);
            }
            TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(_)
            | TerminatorKind::Unreachable
            | TerminatorKind::CoroutineDrop
            | TerminatorKind::TailCall { .. } => {}
            // A yield or an inline assembly block writes through operands
            // this walk does not read, so nothing survives it.
            _ => {
                let blank = vec![Fact::default(); state.len()];
                for succ in kind.successors() {
                    work.merge(succ, blank.clone());
                }
            }
        }
    }

    /// What a call was found to do.
    ///
    /// A contract answers first, since it holds for every implementation
    /// the resolution can reach and costs nothing to read. Anything else is
    /// answered by folding the callee, which is what carries a value
    /// through a call the caller cannot see past, and what proves that a
    /// precondition the caller satisfies leaves the callee nothing to
    /// raise.
    fn inspect(
        &mut self,
        state: &State<'tcx>,
        func: &mir::Operand<'tcx>,
        args: &[rustc_span::Spanned<mir::Operand<'tcx>>],
        destination: mir::Place<'tcx>,
    ) -> Found<'tcx> {
        let Some(ty) =
            self.monomorphize(func.ty(&self.mir.local_decls, self.tcx))
        else {
            return Found::default();
        };
        if let Some(value) = self.contracted(state, ty, args, destination) {
            return Found {
                value: Some(value),
                quiet: false,
            };
        }
        if !self.worth_folding(state, args, destination) {
            return Found::default();
        }
        self.folded(state, ty, args)
    }

    /// Whether folding a callee could tell this call site anything.
    ///
    /// A call the walk knows nothing about the arguments of folds to what
    /// the callee does everywhere, which the graph it belongs to already
    /// accounts for. What earns the walk is an argument carrying a fact
    /// into the callee, or a result a check downstream can read.
    fn worth_folding(
        &self,
        state: &State<'tcx>,
        args: &[rustc_span::Spanned<mir::Operand<'tcx>>],
        destination: mir::Place<'tcx>,
    ) -> bool {
        let known = |arg: &rustc_span::Spanned<mir::Operand<'tcx>>| {
            self.fact(state, &arg.node)
                .value
                .and_then(portable)
                .is_some()
        };
        if args.iter().any(known) {
            return true;
        }
        let result = destination.ty(&self.mir.local_decls, self.tcx).ty;
        self.monomorphize(result)
            .and_then(|ty| self.width(ty))
            .is_some()
    }

    /// The value a call returns by the contract of what it calls.
    ///
    /// Only functions whose result the checks downstream consume are
    /// listed, and only ones whose contract guarantees the claim for every
    /// implementation the resolution can reach: a slice's length is its
    /// metadata, and a nonzero wrapper's validity invariant keeps what it
    /// yields apart from zero.
    fn contracted(
        &self,
        state: &State<'tcx>,
        func: Ty<'tcx>,
        args: &[rustc_span::Spanned<mir::Operand<'tcx>>],
        destination: mir::Place<'tcx>,
    ) -> Option<Value<'tcx>> {
        let ty::FnDef(did, _) = *func.kind() else {
            return None;
        };
        if self.tcx.crate_name(did.krate).as_str() != "core" {
            return None;
        }
        match SinkTable::def_path(self.tcx, did).as_str() {
            "slice::len" => {
                let receiver = args.first()?;
                let (mir::Operand::Copy(place) | mir::Operand::Move(place)) =
                    &receiver.node
                else {
                    return None;
                };
                let local = root_of(state, place.as_local()?);
                if self.escapes(local) {
                    return None;
                }
                Some(Value::Length(local))
            }
            // Picking the larger or the smaller of two numbers is what
            // pins a value away from the end of its range, and the two are
            // read here rather than folded because the body compares
            // through references the walk does not follow. A primitive
            // cannot carry another crate's implementation of the trait, so
            // the body reached is the one this claim describes.
            "cmp::Ord::max" => self.picked(state, true, args),
            "cmp::Ord::min" => self.picked(state, false, args),
            "num::nonzero::get" => {
                let receiver = args.first()?;
                let source = self.monomorphize(
                    receiver.node.ty(&self.mir.local_decls, self.tcx),
                )?;
                if !self.is_nonzero(source) {
                    return None;
                }
                self.apart_from_zero(
                    destination.ty(&self.mir.local_decls, self.tcx).ty,
                )
            }
            _ => None,
        }
    }

    /// What a call does, worked out by folding the callee.
    ///
    /// The callee is walked the way this body is, told what the call site
    /// knows about each argument. Every path out of it has to agree on the
    /// value it leaves, which is what settles a check written against the
    /// result of a call: `right.max(1)` returns either the argument or a
    /// value above it, so it is never zero and the division below it raises
    /// nothing. Every block the compiler will generate for it has to be one
    /// that cannot raise, which is what clears a caller whose arguments
    /// satisfy a precondition the callee checks.
    ///
    /// The walk is bounded twice over. `DEPTH` caps how far a chain of
    /// calls is followed, which bounds the stack, and the budget is spent
    /// across every callee one body reaches, which bounds the work.
    fn folded(
        &mut self,
        state: &State<'tcx>,
        func: Ty<'tcx>,
        args: &[rustc_span::Spanned<mir::Operand<'tcx>>],
    ) -> Found<'tcx> {
        let Some(callee) = self.target(func) else {
            return Found::default();
        };
        let mir = self.tcx.instance_mir(callee.def);
        // A shim rearranges what it was passed, so its parameters are not
        // the operands at the call site.
        if mir.arg_count != args.len() {
            return Found::default();
        }
        let mut folder = Folder::new(
            self.tcx,
            callee,
            TypingEnv::fully_monomorphized(),
            mir,
            self.depth.saturating_add(1),
            self.budget,
        );
        let entry = self.carried(state, &folder, args);
        let reach = folder.run(entry);
        self.budget = folder.budget;
        Found {
            value: folder.returns.claim(),
            quiet: Self::silent(mir, &reach),
        }
    }

    /// The body a call runs, when this walk may read it.
    fn target(&self, func: Ty<'tcx>) -> Option<Instance<'tcx>> {
        if self.depth >= DEPTH || self.budget == 0 {
            return None;
        }
        let ty::FnDef(did, generics) = *func.kind() else {
            return None;
        };
        // A signature with a lifetime still bound names no one target.
        let generics = generics.no_bound_vars()?;
        if generics.has_param() {
            return None;
        }
        let callee = Instance::try_resolve(self.tcx, self.env, did, generics)
            .ok()
            .flatten()?;
        // A body that calls itself would be folded against the same
        // arguments forever, and it is the depth that stops the longer
        // cycles.
        if callee == self.inst {
            return None;
        }
        let ty::InstanceKind::Item(def) = callee.def else {
            return None;
        };
        self.tcx.is_mir_available(def).then_some(callee)
    }

    /// Whether a body walked this way has nothing left that can raise.
    ///
    /// Every block the compiler will generate for it has to carry a
    /// terminator with nowhere to raise from, or a check the walk settled.
    /// A call or a drop is not one of them: what either runs is a body this
    /// walk did not read.
    fn silent(mir: &mir::Body<'tcx>, reach: &Reach) -> bool {
        for (bb, data) in mir.basic_blocks.iter_enumerated() {
            if !reach.is_live(bb) {
                continue;
            }
            let Some(term) = &data.terminator else {
                return false;
            };
            let silent = match &term.kind {
                TerminatorKind::Assert { .. } => reach.is_settled(bb),
                TerminatorKind::Goto { .. }
                | TerminatorKind::SwitchInt { .. }
                | TerminatorKind::Return
                | TerminatorKind::Unreachable
                | TerminatorKind::FalseEdge { .. }
                | TerminatorKind::FalseUnwind { .. } => true,
                _ => false,
            };
            if !silent {
                return false;
            }
        }
        true
    }

    /// The state a callee is entered with.
    ///
    /// A parameter is told only what the call site knows about the operand
    /// it was passed, and only where the claim means the same thing there:
    /// one written at another type describes a value the callee never sees.
    fn carried(
        &self,
        state: &State<'tcx>,
        callee: &Folder<'_, 'tcx>,
        args: &[rustc_span::Spanned<mir::Operand<'tcx>>],
    ) -> State<'tcx> {
        let mut entry = vec![Fact::default(); callee.mir.local_decls.len()];
        for (index, arg) in args.iter().enumerate() {
            let local = mir::Local::from_usize(index.saturating_add(1));
            if callee.escapes(local) {
                continue;
            }
            let Some(value) =
                self.fact(state, &arg.node).value.and_then(portable)
            else {
                continue;
            };
            let Some(decl) = callee.mir.local_decls.get(local) else {
                continue;
            };
            if callee.monomorphize(decl.ty) != value.ty() {
                continue;
            }
            if let Some(slot) = entry.get_mut(local.as_usize()) {
                *slot = Fact::of(value);
            }
        }
        entry
    }

    /// The range a call that picks one of two numbers leaves behind.
    ///
    /// Both ends move together: the larger of two values is at least the
    /// larger of their lower ends and never above the larger of their upper
    /// ends. That is what keeps `right.max(1)` away from zero whatever the
    /// argument holds, and what bounds `right.min(9)` from above.
    fn picked(
        &self,
        state: &State<'tcx>,
        larger: bool,
        args: &[rustc_span::Spanned<mir::Operand<'tcx>>],
    ) -> Option<Value<'tcx>> {
        let [left, right] = args else {
            return None;
        };
        let left = self.spread(state, &left.node)?;
        let right = self.spread(state, &right.node)?;
        let pick = |a: Known<'tcx>, b: Known<'tcx>| {
            let above = a.order(b)? == std::cmp::Ordering::Greater;
            Some(if above == larger { a } else { b })
        };
        Bounds::new(pick(left.lo, right.lo)?, pick(left.hi, right.hi)?)
            .map(Value::Within)
    }

    /// The range an operand lies in, which is its type's own range when
    /// nothing narrower is known.
    fn spread(
        &self,
        state: &State<'tcx>,
        operand: &mir::Operand<'tcx>,
    ) -> Option<Bounds<'tcx>> {
        let ty =
            self.monomorphize(operand.ty(&self.mir.local_decls, self.tcx))?;
        if !matches!(ty.kind(), ty::Int(_) | ty::Uint(_)) {
            return None;
        }
        let seed = Known {
            bits: 0,
            ty,
            width: self.width(ty)?,
        };
        let whole = Bounds::new(seed.type_min(), seed.type_max())?;
        let Some(value) = self.fact(state, operand).value else {
            return Some(whole);
        };
        // A claim written at another type describes another value.
        if value.ty() != Some(ty) {
            return Some(whole);
        }
        Some(
            Value::Within(whole)
                .refined(value)
                .bounds()
                .unwrap_or(whole),
        )
    }

    /// Whether a type is the standard library's nonzero wrapper.
    fn is_nonzero(&self, ty: Ty<'tcx>) -> bool {
        let ty::Adt(def, _) = ty.kind() else {
            return false;
        };
        self.tcx.get_diagnostic_item(rustc_span::sym::NonZero)
            == Some(def.did())
    }

    /// A value of an integer type that is known not to be zero.
    fn apart_from_zero(&self, ty: Ty<'tcx>) -> Option<Value<'tcx>> {
        let ty = self.monomorphize(ty)?;
        let width = self.width(ty)?;
        Some(Value::other_than(Known { bits: 0, ty, width }))
    }

    /// What a branch reads, when an arm of it proves something.
    ///
    /// Only the branching block is read, so nothing outside it can make the
    /// answer wrong, and a comparison has to still be standing when the
    /// branch is reached.
    fn subject_of(
        &self,
        bb: BasicBlock,
        discr: &mir::Operand<'tcx>,
        state: &State<'tcx>,
    ) -> Option<Subject<'tcx>> {
        let (mir::Operand::Copy(place) | mir::Operand::Move(place)) = discr
        else {
            return None;
        };
        let read = place.as_local()?;
        if self.escapes(read) {
            return None;
        }
        let ty =
            self.monomorphize(discr.ty(&self.mir.local_decls, self.tcx))?;
        Some(Subject {
            read,
            ty,
            width: self.width(ty)?,
            compared: ty
                .is_bool()
                .then(|| self.comparison_behind(bb, read, state))
                .flatten(),
        })
    }

    /// The comparison that produced a boolean a branch reads.
    fn comparison_behind(
        &self,
        bb: BasicBlock,
        result: mir::Local,
        state: &State<'tcx>,
    ) -> Option<Compared<'tcx>> {
        let block = &self.mir.basic_blocks[bb];
        let at = block.statements.iter().rposition(|s| writes(s, result))?;
        let mir::StatementKind::Assign(pair) = &block.statements[at].kind
        else {
            return None;
        };
        if pair.0.as_local() != Some(result) {
            return None;
        }
        let mir::Rvalue::BinaryOp(op, operands) = &pair.1 else {
            return None;
        };
        if !matches!(
            op,
            BinOp::Eq
                | BinOp::Ne
                | BinOp::Lt
                | BinOp::Le
                | BinOp::Gt
                | BinOp::Ge
        ) {
            return None;
        }
        let measured = self.compared(state, *op, &operands.0, &operands.1)?;
        let raw = measured.local;
        let local = root_of(state, raw);
        if self.escapes(local) {
            return None;
        }
        // The facts read at the branch have to be the ones that stood when
        // the comparison ran, so nothing it involved may change in between.
        let after = &block.statements[at.saturating_add(1)..];
        let touched = |s: &mir::Statement<'_>| {
            writes(s, local)
                || writes(s, raw)
                || writes(s, result)
                || measured.source.is_some_and(|of| writes(s, of))
                || match measured.against {
                    Against::Constant(_) => false,
                    Against::Length(of) => writes(s, of),
                }
        };
        if after.iter().any(touched) {
            return None;
        }
        Some(Compared { local, ..measured })
    }

    /// Splits a comparison into the local it measures, what it is measured
    /// against, and the operator read with the local on the left.
    fn compared(
        &self,
        state: &State<'tcx>,
        op: BinOp,
        left: &mir::Operand<'tcx>,
        right: &mir::Operand<'tcx>,
    ) -> Option<Compared<'tcx>> {
        let read = |operand: &mir::Operand<'tcx>| match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                place.as_local()
            }
            _ => None,
        };
        let measure = |operand: &mir::Operand<'tcx>| {
            if let mir::Operand::Constant(konst) = operand {
                return Some((Against::Constant(self.constant(konst)?), None));
            }
            let held = read(operand)?;
            match self.fact(state, operand).value? {
                Value::Length(of) => Some((Against::Length(of), Some(held))),
                // A local the walk has settled measures the same as the
                // constant that could have been written in its place, which
                // is how a value the caller passed in is read.
                Value::Exact(known) => {
                    Some((Against::Constant(known), Some(held)))
                }
                _ => None,
            }
        };
        if let (Some(local), Some((against, source))) =
            (read(left), measure(right))
        {
            return Some(Compared {
                op,
                local,
                against,
                source,
            });
        }
        let (local, (against, source)) = (read(right)?, measure(left)?);
        Some(Compared {
            op: value::from_left(op),
            local,
            against,
            source,
        })
    }

    /// Follows an `Assert`, recording it when its condition cannot fail.
    fn assertion(
        &self,
        bb: BasicBlock,
        assert: (&mir::Operand<'tcx>, bool, BasicBlock),
        unwind: UnwindAction,
        state: State<'tcx>,
        reach: &mut Reach,
        work: &mut Work<'tcx>,
    ) {
        let (cond, expected, target) = assert;
        // Passing the check proves what it was testing, which is what makes
        // a second division by the same divisor free.
        let proved = self.subject_of(bb, cond, &state);
        let held = Some(u128::from(expected));
        match self.exact(&state, cond).map(Known::truth) {
            Some(actual) if actual == expected => {
                if let Some(slot) = reach.settled.get_mut(bb.as_usize()) {
                    *slot = true;
                }
                work.merge(target, state);
            }
            // The check fails every time, so only the panic path continues.
            Some(_) => unwind_to(unwind, &state, work),
            None => {
                work.merge(target, refined(&state, proved, held, true));
                unwind_to(unwind, &state, work);
            }
        }
    }

    /// Evaluates an rvalue against what the locals are known about.
    fn rvalue(
        &self,
        state: &State<'tcx>,
        rvalue: &mir::Rvalue<'tcx>,
    ) -> Fact<'tcx> {
        let value = match rvalue {
            mir::Rvalue::Use(operand, _) => {
                return self.traced(state, operand);
            }
            mir::Rvalue::Cast(mir::CastKind::IntToInt, operand, ty) => {
                self.cast(state, operand, *ty)
            }
            // Reading a nonzero wrapper at its plain type is how its value
            // gets out, and the validity invariant keeps it apart from
            // zero.
            mir::Rvalue::Cast(mir::CastKind::Transmute, operand, ty) => self
                .monomorphize(operand.ty(&self.mir.local_decls, self.tcx))
                .filter(|source| self.is_nonzero(*source))
                .and_then(|_| self.apart_from_zero(*ty)),
            mir::Rvalue::BinaryOp(op, pair) => {
                let left = self.fact(state, &pair.0);
                let right = self.fact(state, &pair.1);
                // The remainder of an unsigned value by the length of a
                // slice lands below that length, which is what the slice's
                // own bounds check asks. The length is nonzero wherever
                // this runs, since the remainder's own check has passed to
                // get here.
                if *op == BinOp::Rem
                    && let Some(Value::Length(of)) = right.value
                    && self.unsigned(&pair.0)
                {
                    return Fact {
                        order: Some((LenRel::Below, of)),
                        ..Fact::default()
                    };
                }
                self.binary(*op, left, right)
            }
            mir::Rvalue::UnaryOp(mir::UnOp::Not, operand) => {
                self.exact(state, operand).map(|value| {
                    let bits = if value.ty.is_bool() {
                        u128::from(!value.truth())
                    } else {
                        truncate(!value.bits, value.width)
                    };
                    Value::Exact(Known { bits, ..value })
                })
            }
            mir::Rvalue::UnaryOp(mir::UnOp::PtrMetadata, operand) => {
                self.length_of(state, operand)
            }
            _ => None,
        };
        Fact {
            value,
            ..Fact::default()
        }
    }

    /// Whether an operand is read as an unsigned integer.
    fn unsigned(&self, operand: &mir::Operand<'tcx>) -> bool {
        self.monomorphize(operand.ty(&self.mir.local_decls, self.tcx))
            .is_some_and(|ty| matches!(ty.kind(), ty::Uint(_)))
    }

    /// The length a wide pointer carries, when the pointee is a slice.
    fn length_of(
        &self,
        state: &State<'tcx>,
        operand: &mir::Operand<'tcx>,
    ) -> Option<Value<'tcx>> {
        let (mir::Operand::Copy(place) | mir::Operand::Move(place)) = operand
        else {
            return None;
        };
        let local = root_of(state, place.as_local()?);
        if self.escapes(local) {
            return None;
        }
        let ty =
            self.monomorphize(operand.ty(&self.mir.local_decls, self.tcx))?;
        let pointee = match ty.kind() {
            ty::Ref(_, inner, _) | ty::RawPtr(inner, _) => *inner,
            _ => return None,
        };
        if !matches!(pointee.kind(), ty::Slice(_) | ty::Str) {
            return None;
        }
        Some(Value::Length(local))
    }

    /// Reads an operand, when its value is settled.
    fn exact(
        &self,
        state: &State<'tcx>,
        operand: &mir::Operand<'tcx>,
    ) -> Option<Known<'tcx>> {
        self.fact(state, operand).value?.exact()
    }

    /// Reads everything known about an operand, reading through its link
    /// of sameness.
    ///
    /// A link always names a local that carries no link of its own, so one
    /// step is all there ever is. A claim held locally and one held at the
    /// source were both true when made and neither has been swept, so
    /// whichever exists is usable.
    fn fact(
        &self,
        state: &State<'tcx>,
        operand: &mir::Operand<'tcx>,
    ) -> Fact<'tcx> {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                place.as_local().map_or_else(Fact::default, |local| {
                    Self::known_at(state, local)
                })
            }
            mir::Operand::Constant(konst) => self
                .constant(konst)
                .map(Value::Exact)
                .map_or_else(Fact::default, Fact::of),
            // Whether a check is on is settled by the session compiling the
            // crate, which is what makes a standard library block vanish in
            // a build that turns the check off.
            mir::Operand::RuntimeChecks(check) => self
                .boolean(check.value(self.tcx.sess))
                .map(Value::Exact)
                .map_or_else(Fact::default, Fact::of),
        }
    }

    /// Everything known about one local, read through its link of
    /// sameness.
    fn known_at(state: &State<'tcx>, local: mir::Local) -> Fact<'tcx> {
        let Some(own) = state.get(local.as_usize()).copied() else {
            return Fact::default();
        };
        let held = own.same.map_or(own, |root| {
            let at_root =
                state.get(root.as_usize()).copied().unwrap_or_default();
            Fact {
                value: own.value.or(at_root.value),
                order: own.order.or(at_root.order),
                ..own
            }
        });
        let Some(Value::Length(of)) = held.value else {
            return held;
        };
        Fact {
            extent: state.get(of.as_usize()).and_then(|slot| slot.extent),
            ..held
        }
    }

    /// Reads an operand for an assignment, recording where a copy of a
    /// plain local came from.
    ///
    /// The link is kept even when the value itself is known: a fact the
    /// source learns later still has to reach the checks that read the
    /// copy, and the link is how it travels.
    fn traced(
        &self,
        state: &State<'tcx>,
        operand: &mir::Operand<'tcx>,
    ) -> Fact<'tcx> {
        let mut fact = self.fact(state, operand);
        let (mir::Operand::Copy(place) | mir::Operand::Move(place)) = operand
        else {
            return fact;
        };
        let Some(local) = place.as_local() else {
            return fact;
        };
        if self.escapes(local) {
            return fact;
        }
        let root = root_of(state, local);
        if !self.escapes(root) {
            fact.same = Some(root);
        }
        fact
    }

    /// Evaluates a constant for the arguments this body was reached with.
    fn constant(&self, konst: &mir::ConstOperand<'tcx>) -> Option<Known<'tcx>> {
        if self.inst.args.has_param() {
            // Only a monomorphic body has definite values. An associated
            // constant such as `<T as SizedTypeProperties>::SIZE` is exactly
            // what the interesting checks compare against, and it has no
            // value until `T` has one.
            return None;
        }
        let konst = self
            .inst
            .try_instantiate_mir_and_normalize_erasing_regions(
                self.tcx,
                self.env,
                ty::EarlyBinder::bind(self.tcx, konst.const_),
            )
            .ok()?;
        let ty = konst.ty();
        let width = self.width(ty)?;
        let bits = konst.try_eval_bits(self.tcx, self.env)?;
        Some(Known {
            bits: truncate(bits, width),
            ty,
            width,
        })
    }

    /// Widens or narrows a value to another integer type.
    fn cast(
        &self,
        state: &State<'tcx>,
        operand: &mir::Operand<'tcx>,
        ty: Ty<'tcx>,
    ) -> Option<Value<'tcx>> {
        let value = self.fact(state, operand).value?;
        let ty = self.monomorphize(ty)?;
        let width = self.width(ty)?;
        match value {
            Value::Exact(known) => {
                Some(Value::Exact(Self::converted(known, ty, width)))
            }
            // A cast that cannot lose information keeps values apart, so
            // whatever the source differs from, the result differs from too.
            Value::Other(known) if width >= known.width => {
                Some(Value::other_than(Self::converted(known, ty, width)))
            }
            // A range survives a cast only when both ends keep their
            // mathematical value, which is when the map is order preserving.
            Value::Within(bounds) => {
                let lo = Self::preserved(bounds.lo, ty, width)?;
                let hi = Self::preserved(bounds.hi, ty, width)?;
                Bounds::new(lo, hi).map(Value::Within)
            }
            _ => None,
        }
    }

    /// Reads a value at another integer type, when the value fits.
    fn preserved(
        value: Known<'tcx>,
        ty: Ty<'tcx>,
        width: u32,
    ) -> Option<Known<'tcx>> {
        let semantic = |known: Known<'tcx>| {
            if known.is_signed() {
                Some(known.as_signed())
            } else {
                i128::try_from(known.bits).ok()
            }
        };
        let converted = Self::converted(value, ty, width);
        (semantic(value)? == semantic(converted)?).then_some(converted)
    }

    /// Reads a value at another integer type.
    ///
    /// Narrowing keeps the low bits and widening copies the sign of the
    /// source, which is what the machine does.
    fn converted(value: Known<'tcx>, ty: Ty<'tcx>, width: u32) -> Known<'tcx> {
        let extended = if value.is_signed() {
            value.as_signed().cast_unsigned()
        } else {
            value.bits
        };
        Known {
            bits: truncate(extended, width),
            ty,
            width,
        }
    }

    /// Applies an operator the folder can evaluate.
    ///
    /// Arithmetic is followed only where every end of the result lands
    /// inside its type. Past that the machine wraps and the arithmetic does
    /// not, and a claim drawn from the wrong one drops a panic that is
    /// real. The remaining two bound their result by construction: a
    /// remainder by a constant and a masked value cannot leave the range the
    /// operator itself defines.
    fn binary(
        &self,
        op: BinOp,
        left: Fact<'tcx>,
        right: Fact<'tcx>,
    ) -> Option<Value<'tcx>> {
        if let Some(truth) = value::compare(op, left, right) {
            return self.boolean(truth).map(Value::Exact);
        }
        if let (Some(Value::Exact(l)), Some(Value::Exact(r))) =
            (left.value, right.value)
            && let Some(known) = Self::settled(op, l, r)
        {
            return Some(Value::Exact(known));
        }
        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul => {
                Self::spanned(op, left.value?.bounds()?, right.value?.bounds()?)
            }
            // The remainder of anything by a positive constant lies below
            // it. Negative operands are signed, and a signed remainder can
            // be negative, so only unsigned types make the claim.
            BinOp::Rem => {
                let divisor = right.value?.exact()?;
                if divisor.is_signed() || divisor.bits == 0 {
                    return None;
                }
                let hi = divisor.predecessor()?;
                Bounds::new(divisor.type_min(), hi).map(Value::Within)
            }
            // A mask with no sign bit pins the result between zero and
            // itself, whatever the other operand held.
            BinOp::BitAnd => {
                let ((Some(mask), _) | (None, Some(mask))) = (
                    left.value.and_then(Value::exact),
                    right.value.and_then(Value::exact),
                ) else {
                    return None;
                };
                if mask.is_signed() && mask.as_signed() < 0 {
                    return None;
                }
                let zero = Known { bits: 0, ..mask };
                Bounds::new(zero, mask).map(Value::Within)
            }
            _ => None,
        }
    }

    /// The range an arithmetic operator leaves behind.
    ///
    /// Each end is worked out as arithmetic rather than as the machine does
    /// it, and an end that would leave its type abandons the claim, so a
    /// result that wraps is never described by a range that cannot hold it.
    fn spanned(
        op: BinOp,
        left: Bounds<'tcx>,
        right: Bounds<'tcx>,
    ) -> Option<Value<'tcx>> {
        match op {
            BinOp::Add => Bounds::covering(&[
                left.lo.arith(op, right.lo)?,
                left.hi.arith(op, right.hi)?,
            ]),
            BinOp::Sub => Bounds::covering(&[
                left.lo.arith(op, right.hi)?,
                left.hi.arith(op, right.lo)?,
            ]),
            // With a sign in play the extreme can come from any pairing of
            // ends, so every corner has to land inside the type before any
            // of them describes the result.
            BinOp::Mul => Bounds::covering(&[
                left.lo.arith(op, right.lo)?,
                left.lo.arith(op, right.hi)?,
                left.hi.arith(op, right.lo)?,
                left.hi.arith(op, right.hi)?,
            ]),
            _ => None,
        }
        .map(Value::Within)
    }

    /// Applies an operator to two settled values.
    fn settled(
        op: BinOp,
        left: Known<'tcx>,
        right: Known<'tcx>,
    ) -> Option<Known<'tcx>> {
        if left.ty != right.ty || left.width != right.width {
            return None;
        }
        let bits = match op {
            BinOp::BitAnd => left.bits & right.bits,
            BinOp::BitOr => left.bits | right.bits,
            BinOp::BitXor => left.bits ^ right.bits,
            _ => return None,
        };
        Some(Known {
            bits: truncate(bits, left.width),
            ..left
        })
    }

    /// A `bool` the folder is certain of.
    fn boolean(&self, value: bool) -> Option<Known<'tcx>> {
        let ty = self.tcx.types.bool;
        Some(Known {
            bits: u128::from(value),
            ty,
            width: self.width(ty)?,
        })
    }

    /// The width of a type whose values are plain integers.
    ///
    /// Anything else is refused, so a float or a pointer never reaches the
    /// comparisons, where its bits would not mean what they say.
    fn width(&self, ty: Ty<'tcx>) -> Option<u32> {
        if !matches!(ty.kind(), ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_))
        {
            return None;
        }
        let layout = self.tcx.layout_of(self.env.as_query_input(ty)).ok()?;
        u32::try_from(layout.size.bits()).ok()
    }

    /// Resolves a type written in the body against this instantiation.
    fn monomorphize(&self, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
        self.inst
            .try_instantiate_mir_and_normalize_erasing_regions(
                self.tcx,
                self.env,
                ty::EarlyBinder::bind(self.tcx, ty),
            )
            .ok()
    }
}
