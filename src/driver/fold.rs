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
//! cannot fail. It only ever claims to know a value it can compute exactly,
//! so a body it cannot follow is left exactly as it was found.

use std::collections::VecDeque;

use rustc_middle::{
    mir::{self, BasicBlock, BinOp, TerminatorKind, UnwindAction},
    ty::{self, Instance, Ty, TyCtxt, TypeVisitableExt, TypingEnv},
};

use crate::{
    sinks::SinkTable,
    value::{self, Against, Bounds, Fact, Known, Taught, Value, truncate},
};

/// What one instantiation of a body reaches.
pub struct Reach {
    live: Vec<bool>,
    settled: Vec<bool>,
}

impl Reach {
    /// A verdict that assumes nothing, which is what an unfoldable body gets.
    fn everything(blocks: usize) -> Self {
        Self {
            live: vec![true; blocks],
            settled: vec![false; blocks],
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
}

/// Works out what one instantiation of a body reaches.
pub fn reachable<'tcx>(
    tcx: TyCtxt<'tcx>,
    inst: Instance<'tcx>,
    env: TypingEnv<'tcx>,
    mir: &mir::Body<'tcx>,
) -> Reach {
    Folder {
        tcx,
        inst,
        env,
        mir,
        escaped: escaping(mir),
    }
    .run()
}

/// What every local is known about at one point.
type State<'tcx> = Vec<Fact<'tcx>>;

/// What a branch reads, and what its arms therefore prove.
#[derive(Debug, Clone, Copy)]
struct Subject<'tcx> {
    /// The local the branch reads, which every arm settles.
    read: mir::Local,
    ty: Ty<'tcx>,
    width: u32,
    /// The comparison it stands for, when it is a boolean holding one.
    compared: Option<Compared<'tcx>>,
}

/// A comparison a branch turns into a fact about the local it measured.
#[derive(Debug, Clone, Copy)]
struct Compared<'tcx> {
    /// The operator, read with the measured local on the left.
    op: BinOp,
    local: mir::Local,
    against: Against<'tcx>,
}

/// The blocks still to visit, and what each is entered with.
struct Work<'tcx> {
    entry: Vec<Option<State<'tcx>>>,
    queued: Vec<bool>,
    queue: VecDeque<BasicBlock>,
}

impl<'tcx> Work<'tcx> {
    /// Prepares a worklist over a body of `blocks` blocks.
    fn new(blocks: usize) -> Self {
        Self {
            entry: vec![None; blocks],
            queued: vec![false; blocks],
            queue: VecDeque::new(),
        }
    }

    /// Records what a block is entered with, queueing it if that changed.
    ///
    /// A block is first recorded with whatever its predecessor knew, and
    /// afterwards only ever loses a local: two predecessors that disagree
    /// leave nothing behind. That is what bounds the walk.
    fn merge(&mut self, bb: BasicBlock, incoming: State<'tcx>) {
        let Some(slot) = self.entry.get_mut(bb.as_usize()) else {
            return;
        };
        match slot {
            None => *slot = Some(incoming),
            Some(existing) => {
                let mut changed = false;
                for (held, arriving) in existing.iter_mut().zip(&incoming) {
                    let next = held.agreed(*arriving);
                    if next != *held {
                        *held = next;
                        changed = true;
                    }
                }
                if !changed {
                    return;
                }
            }
        }
        if let Some(queued) = self.queued.get_mut(bb.as_usize())
            && !*queued
        {
            *queued = true;
            self.queue.push_back(bb);
        }
    }

    /// Whether every block has been visited with its settled state.
    fn is_drained(&self) -> bool {
        self.queue.is_empty()
    }

    /// Takes the next block to visit, with the state it is entered with.
    ///
    /// A block is queued only once its state is recorded, so the state is
    /// always there; the walk simply skips a block if it ever is not, rather
    /// than ending early and leaving the rest of the body unvisited.
    fn pop(&mut self) -> Option<(BasicBlock, State<'tcx>)> {
        let bb = self.queue.pop_front()?;
        if let Some(queued) = self.queued.get_mut(bb.as_usize()) {
            *queued = false;
        }
        let state = self.entry.get(bb.as_usize())?.clone()?;
        Some((bb, state))
    }
}

/// Locals a pointer could be aimed at.
///
/// A write through a pointer can reach any of these, so their value is never
/// assumed. Every other local can only be written by naming it, which the
/// walk sees.
fn escaping(mir: &mir::Body<'_>) -> Vec<bool> {
    let mut escaped = vec![false; mir.local_decls.len()];
    for block in mir.basic_blocks.iter() {
        for stmt in &block.statements {
            let mir::StatementKind::Assign(pair) = &stmt.kind else {
                continue;
            };
            let (mir::Rvalue::Ref(_, _, place)
            | mir::Rvalue::RawPtr(_, place)
            | mir::Rvalue::Reborrow(_, _, place)) = &pair.1
            else {
                continue;
            };
            if let Some(slot) = escaped.get_mut(place.local.as_usize()) {
                *slot = true;
            }
        }
    }
    escaped
}

/// Folds one body against the arguments it was instantiated with.
struct Folder<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    inst: Instance<'tcx>,
    env: TypingEnv<'tcx>,
    mir: &'a mir::Body<'tcx>,
    escaped: Vec<bool>,
}

impl<'tcx> Folder<'_, 'tcx> {
    /// Whether a pointer could be aimed at a local, so its value is never
    /// assumed. A local the walk has never heard of is treated as escaping.
    fn escapes(&self, local: mir::Local) -> bool {
        self.escaped.get(local.as_usize()).copied().unwrap_or(true)
    }

    /// Runs the walk to a fixpoint.
    fn run(&self) -> Reach {
        let blocks = self.mir.basic_blocks.len();
        let locals = self.mir.local_decls.len();
        let mut reach = Reach {
            live: vec![false; blocks],
            settled: vec![false; blocks],
        };
        let mut work = Work::new(blocks);
        work.merge(mir::START_BLOCK, vec![Fact::default(); locals]);

        // A block is recorded once and afterwards only loses locals, so it
        // is queued at most `locals + 1` times and the walk ends within the
        // bound below.
        let bound = blocks
            .saturating_mul(locals.saturating_add(1))
            .saturating_add(blocks)
            .saturating_add(1);
        for _ in 0..bound {
            if work.is_drained() {
                return reach;
            }
            if let Some((bb, state)) = work.pop() {
                self.visit(bb, state, &mut reach, &mut work);
            }
        }
        // The bound is a proof rather than a guess, so exhausting it means
        // the walk is not shrinking as it should. Report the body as it was
        // found instead of a verdict that assumed away an unsettled branch.
        Reach::everything(blocks)
    }

    /// Walks one block, recording what it reaches.
    fn visit(
        &self,
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
        let block = &self.mir.basic_blocks[bb];
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
        &self,
        bb: BasicBlock,
        kind: &TerminatorKind<'tcx>,
        state: State<'tcx>,
        reach: &mut Reach,
        work: &mut Work<'tcx>,
    ) {
        match kind {
            TerminatorKind::Goto { target } => work.merge(*target, state),
            TerminatorKind::SwitchInt { discr, targets } => {
                if let Some(value) = self.exact(&state, discr) {
                    work.merge(targets.target_for_value(value.bits), state);
                    return;
                }
                let subject = self.subject_of(bb, discr, &state);
                let mut taken = Vec::new();
                for (value, target) in targets.iter() {
                    taken.push(value);
                    work.merge(
                        target,
                        refined(&state, subject, Some(value), true),
                    );
                }
                // The fallback covers every value not listed, so it settles
                // the condition only when one value is left over.
                let rest = match taken.as_slice() {
                    [only] => Some(*only),
                    _ => None,
                };
                work.merge(
                    targets.otherwise(),
                    refined(&state, subject, rest, false),
                );
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
            } => {
                let mut after = state.clone();
                forget(&mut after, destination.local);
                if let Some(value) =
                    self.call_summary(&state, func, args, *destination)
                    && let Some(local) = destination.as_local()
                    && !self.escapes(local)
                    && let Some(slot) = after.get_mut(local.as_usize())
                {
                    *slot = Fact::of(value);
                }
                if let Some(target) = target {
                    work.merge(*target, after);
                }
                unwind_to(*unwind, &state, work);
            }
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
            _ => Self::onward(kind, state, work),
        }
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
            TerminatorKind::Return
            | TerminatorKind::UnwindResume
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

    /// The value the call being made is known to return.
    ///
    /// Only functions whose result the checks downstream consume are
    /// summarized, and only ones whose contract guarantees the claim for
    /// every implementation the resolution can reach: a slice's length is
    /// its metadata, and a nonzero wrapper's validity invariant keeps what
    /// it yields apart from zero.
    fn call_summary(
        &self,
        state: &State<'tcx>,
        func: &mir::Operand<'tcx>,
        args: &[rustc_span::Spanned<mir::Operand<'tcx>>],
        destination: mir::Place<'tcx>,
    ) -> Option<Value<'tcx>> {
        let ty = self.monomorphize(func.ty(&self.mir.local_decls, self.tcx))?;
        let ty::FnDef(did, _) = *ty.kind() else {
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
        let (op, raw, against) =
            self.compared(state, *op, &operands.0, &operands.1)?;
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
                || match against {
                    Against::Constant(_) => false,
                    Against::Length(of) => writes(s, of),
                }
        };
        if after.iter().any(touched) {
            return None;
        }
        Some(Compared { op, local, against })
    }

    /// Splits a comparison into the local it measures, what it is measured
    /// against, and the operator read with the local on the left.
    fn compared(
        &self,
        state: &State<'tcx>,
        op: BinOp,
        left: &mir::Operand<'tcx>,
        right: &mir::Operand<'tcx>,
    ) -> Option<(BinOp, mir::Local, Against<'tcx>)> {
        let read = |operand: &mir::Operand<'tcx>| match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                place.as_local()
            }
            _ => None,
        };
        let measure = |operand: &mir::Operand<'tcx>| {
            if let mir::Operand::Constant(konst) = operand {
                return self.constant(konst).map(Against::Constant);
            }
            match self.fact(state, operand).value {
                Some(Value::Length(of)) => Some(Against::Length(of)),
                _ => None,
            }
        };
        if let (Some(local), Some(against)) = (read(left), measure(right)) {
            return Some((op, local, against));
        }
        let (local, against) = (read(right)?, measure(left)?);
        Some((value::from_left(op), local, against))
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
            order: None,
            same: None,
        }
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
                let Some(local) = place.as_local() else {
                    return Fact::default();
                };
                let Some(own) = state.get(local.as_usize()).copied() else {
                    return Fact::default();
                };
                let Some(root) = own.same else {
                    return own;
                };
                let at_root =
                    state.get(root.as_usize()).copied().unwrap_or_default();
                Fact {
                    value: own.value.or(at_root.value),
                    order: own.order.or(at_root.order),
                    same: own.same,
                }
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
    /// General arithmetic is deliberately absent. The checks worth folding
    /// compare a value against a bound, and every further operator is
    /// another chance to disagree with the machine and drop a panic that is
    /// real. The two exceptions bound their result by construction: a
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

/// The local a local's link of sameness points at, or the local itself.
fn root_of(state: &State<'_>, local: mir::Local) -> mir::Local {
    state
        .get(local.as_usize())
        .and_then(|fact| fact.same)
        .unwrap_or(local)
}

/// Applies what taking one arm of a branch proves.
///
/// `matched` says whether the arm was reached by naming `value` or by being
/// the fallback that everything except `value` avoids. The local the branch
/// read is settled either way, and a boolean standing for a comparison
/// settles the local that was compared as well.
fn refined<'tcx>(
    state: &State<'tcx>,
    subject: Option<Subject<'tcx>>,
    value: Option<u128>,
    matched: bool,
) -> State<'tcx> {
    let mut next = state.clone();
    let (Some(subject), Some(value)) = (subject, value) else {
        return next;
    };
    let read = Known {
        bits: truncate(value, subject.width),
        ty: subject.ty,
        width: subject.width,
    };
    learn(
        &mut next,
        subject.read,
        Taught::Value(settle(read, matched)),
    );
    if let Some(compared) = subject.compared {
        // A boolean has two arms, so the fallback settles the comparison
        // just as firmly as naming its value does.
        let truth = if matched { value == 1 } else { value == 0 };
        if let Some(fact) = value::fact_of(compared.op, compared.against, truth)
        {
            learn(&mut next, compared.local, fact);
        }
    }
    next
}

/// A value a branch either confirmed or ruled out.
fn settle(known: Known<'_>, holds: bool) -> Value<'_> {
    if holds {
        Value::Exact(known)
    } else {
        Value::other_than(known)
    }
}

/// Records what a branch taught, leaving anything already settled alone.
///
/// A settled claim cannot be improved on, and disagreeing with it would
/// mean the arm is unreachable, which this pass does not claim. The two
/// planes fill independently: a counter that is exactly zero can still
/// learn that it is below a length.
fn learn<'tcx>(
    state: &mut State<'tcx>,
    local: mir::Local,
    taught: Taught<'tcx>,
) {
    let Some(slot) = state.get_mut(local.as_usize()) else {
        return;
    };
    match taught {
        Taught::Value(value) => {
            if slot.value.is_none() {
                slot.value = Some(value);
            }
        }
        Taught::Order(rel, of) => {
            if slot.order.is_none() {
                slot.order = Some((rel, of));
            }
        }
    }
}

/// Whether a statement can change a local.
///
/// Anything not modelled is treated as able to write anywhere, so a fact
/// never outlives the value it was drawn from.
fn writes(stmt: &mir::Statement<'_>, local: mir::Local) -> bool {
    match &stmt.kind {
        mir::StatementKind::Assign(pair) => pair.0.local == local,
        mir::StatementKind::SetDiscriminant { place, .. } => {
            place.local == local
        }
        mir::StatementKind::StorageLive(other)
        | mir::StatementKind::StorageDead(other) => *other == local,
        mir::StatementKind::FakeRead(..)
        | mir::StatementKind::PlaceMention(..)
        | mir::StatementKind::AscribeUserType(..)
        | mir::StatementKind::Coverage(..)
        | mir::StatementKind::ConstEvalCounter
        | mir::StatementKind::Nop
        | mir::StatementKind::BackwardIncompatibleDropHint { .. } => false,
        // Copying between pointers can land anywhere.
        mir::StatementKind::Intrinsic(_) => true,
    }
}

/// Drops what is known about one local, along with every claim that leans
/// on it.
///
/// A claim of sameness or one measured against a slice is only as good as
/// the local it names, so writing that local sweeps those claims with it.
/// Each plane is swept on its own: an ordering against an untouched slice
/// outlives the loss of the value it was learned beside.
fn forget(state: &mut State<'_>, local: mir::Local) {
    for slot in state.iter_mut() {
        if slot.value.is_some_and(|value| value.leans_on(local)) {
            slot.value = None;
        }
        if slot.order.is_some_and(|(_, of)| of == local) {
            slot.order = None;
        }
        if slot.same == Some(local) {
            // The copied value itself stands; only the claim of still
            // being the same as the source dies with the write.
            slot.same = None;
        }
    }
    if let Some(slot) = state.get_mut(local.as_usize()) {
        *slot = Fact::default();
    }
}

/// Follows the cleanup path a terminator can take.
fn unwind_to<'tcx>(
    unwind: UnwindAction,
    state: &State<'tcx>,
    work: &mut Work<'tcx>,
) {
    if let UnwindAction::Cleanup(target) = unwind {
        work.merge(target, state.clone());
    }
}
