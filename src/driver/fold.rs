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

/// A value the folder is certain of.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Known<'tcx> {
    /// The value, zero extended from the bit pattern of its type.
    bits: u128,
    /// The type it was read at, which decides how the bits compare.
    ty: Ty<'tcx>,
    /// The width of that type, in bits.
    width: u32,
}

impl Known<'_> {
    /// Whether the type reads its top bit as a sign.
    fn is_signed(self) -> bool {
        matches!(self.ty.kind(), ty::Int(_))
    }

    /// The value read as a signed integer.
    ///
    /// The bits are held zero extended, so the sign has to be put back by
    /// shifting the value up to the top of the word and down again.
    const fn as_signed(self) -> i128 {
        let Some(shift) = 128u32.checked_sub(self.width) else {
            return self.bits.cast_signed();
        };
        if shift == 0 || shift == 128 {
            return self.bits.cast_signed();
        }
        (self.bits << shift).cast_signed() >> shift
    }

    /// Whether the value is the one a branch treats as true.
    const fn truth(self) -> bool {
        self.bits != 0
    }
}

/// Masks a value to the width of its type.
const fn truncate(bits: u128, width: u32) -> u128 {
    match 1u128.checked_shl(width) {
        Some(above) => bits & above.wrapping_sub(1),
        None => bits,
    }
}

/// What a local is known about.
///
/// A branch teaches the arm it guards something its condition never states
/// outright: past `if rhs != 0`, the divisor is not zero, which is the fact
/// the division's own check is asking for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Value<'tcx> {
    /// Exactly this value.
    Exact(Known<'tcx>),
    /// Anything but this value.
    Other(Known<'tcx>),
}

impl<'tcx> Value<'tcx> {
    /// The value, when it is settled.
    const fn exact(self) -> Option<Known<'tcx>> {
        match self {
            Self::Exact(known) => Some(known),
            Self::Other(_) => None,
        }
    }

    /// Records that a value is anything but `known`.
    ///
    /// A `bool` has only two values, so ruling one out settles the other.
    fn other_than(known: Known<'tcx>) -> Self {
        if known.ty.is_bool() && known.bits <= 1 {
            return Self::Exact(Known {
                bits: 1 - known.bits,
                ..known
            });
        }
        Self::Other(known)
    }
}

/// What every local is known about at one point.
type State<'tcx> = Vec<Option<Value<'tcx>>>;

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
    /// Whether the comparison asked for equality or difference.
    equality: bool,
    local: mir::Local,
    against: Known<'tcx>,
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
                    if held.is_some() && held != arriving {
                        *held = None;
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
    /// Runs the walk to a fixpoint.
    fn run(&self) -> Reach {
        let blocks = self.mir.basic_blocks.len();
        let locals = self.mir.local_decls.len();
        let mut reach = Reach {
            live: vec![false; blocks],
            settled: vec![false; blocks],
        };
        let mut work = Work::new(blocks);
        work.merge(mir::START_BLOCK, vec![None; locals]);

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
                    Some(local)
                        if !self
                            .escaped
                            .get(local.as_usize())
                            .copied()
                            .unwrap_or(true) =>
                    {
                        let value = self.rvalue(state, rvalue);
                        if let Some(slot) = state.get_mut(local.as_usize()) {
                            *slot = value;
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
                let subject = self.subject_of(bb, discr);
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
                destination,
                target,
                unwind,
                ..
            } => {
                let mut after = state.clone();
                forget(&mut after, destination.local);
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
                let blank = vec![None; state.len()];
                for succ in kind.successors() {
                    work.merge(succ, blank.clone());
                }
            }
        }
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
    ) -> Option<Subject<'tcx>> {
        let (mir::Operand::Copy(place) | mir::Operand::Move(place)) = discr
        else {
            return None;
        };
        let read = place.as_local()?;
        if self.escaped.get(read.as_usize()).copied().unwrap_or(true) {
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
                .then(|| self.comparison_behind(bb, read))
                .flatten(),
        })
    }

    /// The comparison that produced a boolean a branch reads.
    fn comparison_behind(
        &self,
        bb: BasicBlock,
        result: mir::Local,
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
        let equality = match op {
            BinOp::Eq => true,
            BinOp::Ne => false,
            _ => return None,
        };
        let (local, against) = self.compared(&operands.0, &operands.1)?;
        if self.escaped.get(local.as_usize()).copied().unwrap_or(true) {
            return None;
        }
        let after = &block.statements[at.saturating_add(1)..];
        if after.iter().any(|s| writes(s, local) || writes(s, result)) {
            return None;
        }
        Some(Compared {
            equality,
            local,
            against,
        })
    }

    /// Splits a comparison into the local it reads and the value it is
    /// measured against, in whichever order they were written.
    fn compared(
        &self,
        left: &mir::Operand<'tcx>,
        right: &mir::Operand<'tcx>,
    ) -> Option<(mir::Local, Known<'tcx>)> {
        let read = |operand: &mir::Operand<'tcx>| match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                place.as_local()
            }
            _ => None,
        };
        let value = |operand: &mir::Operand<'tcx>| match operand {
            mir::Operand::Constant(konst) => self.constant(konst),
            _ => None,
        };
        match (read(left), value(right)) {
            (Some(local), Some(against)) => Some((local, against)),
            _ => Some((read(right)?, value(left)?)),
        }
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
        let proved = self.subject_of(bb, cond);
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
    ) -> Option<Value<'tcx>> {
        match rvalue {
            mir::Rvalue::Use(operand, _) => self.operand(state, operand),
            mir::Rvalue::Cast(mir::CastKind::IntToInt, operand, ty) => {
                self.cast(state, operand, *ty)
            }
            mir::Rvalue::BinaryOp(op, pair) => {
                let left = self.operand(state, &pair.0)?;
                let right = self.operand(state, &pair.1)?;
                self.binary(*op, left, right)
            }
            mir::Rvalue::UnaryOp(mir::UnOp::Not, operand) => {
                let value = self.exact(state, operand)?;
                let bits = if value.ty.is_bool() {
                    u128::from(!value.truth())
                } else {
                    truncate(!value.bits, value.width)
                };
                Some(Value::Exact(Known { bits, ..value }))
            }
            _ => None,
        }
    }

    /// Reads an operand, when its value is settled.
    fn exact(
        &self,
        state: &State<'tcx>,
        operand: &mir::Operand<'tcx>,
    ) -> Option<Known<'tcx>> {
        self.operand(state, operand)?.exact()
    }

    /// Reads an operand.
    fn operand(
        &self,
        state: &State<'tcx>,
        operand: &mir::Operand<'tcx>,
    ) -> Option<Value<'tcx>> {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                let local = place.as_local()?;
                *state.get(local.as_usize())?
            }
            mir::Operand::Constant(konst) => {
                self.constant(konst).map(Value::Exact)
            }
            // Whether a check is on is settled by the session compiling the
            // crate, which is what makes a standard library block vanish in
            // a build that turns the check off.
            mir::Operand::RuntimeChecks(check) => {
                self.boolean(check.value(self.tcx.sess)).map(Value::Exact)
            }
        }
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
        let value = self.operand(state, operand)?;
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
            Value::Other(_) => None,
        }
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

    /// Applies an operator the folder can evaluate exactly.
    ///
    /// Arithmetic is deliberately absent. The checks worth folding compare a
    /// size against a bound, and every further operator is another chance to
    /// disagree with the machine and drop a panic that is real.
    fn binary(
        &self,
        op: BinOp,
        left: Value<'tcx>,
        right: Value<'tcx>,
    ) -> Option<Value<'tcx>> {
        match (left, right) {
            (Value::Exact(left), Value::Exact(right)) => {
                self.settled(op, left, right).map(Value::Exact)
            }
            // One side is known to differ from exactly the value the other
            // side holds, which answers an equality and nothing else.
            (Value::Exact(known), Value::Other(ruled_out))
            | (Value::Other(ruled_out), Value::Exact(known))
                if known == ruled_out =>
            {
                match op {
                    BinOp::Eq => self.boolean(false).map(Value::Exact),
                    BinOp::Ne => self.boolean(true).map(Value::Exact),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Applies an operator to two settled values.
    fn settled(
        &self,
        op: BinOp,
        left: Known<'tcx>,
        right: Known<'tcx>,
    ) -> Option<Known<'tcx>> {
        if left.ty != right.ty || left.width != right.width {
            return None;
        }
        if matches!(op, BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor) {
            let bits = match op {
                BinOp::BitAnd => left.bits & right.bits,
                BinOp::BitOr => left.bits | right.bits,
                _ => left.bits ^ right.bits,
            };
            return Some(Known {
                bits: truncate(bits, left.width),
                ..left
            });
        }
        let order = if left.is_signed() {
            left.as_signed().cmp(&right.as_signed())
        } else {
            left.bits.cmp(&right.bits)
        };
        let verdict = match op {
            BinOp::Eq => order.is_eq(),
            BinOp::Ne => order.is_ne(),
            BinOp::Lt => order.is_lt(),
            BinOp::Le => order.is_le(),
            BinOp::Gt => order.is_gt(),
            BinOp::Ge => order.is_ge(),
            _ => return None,
        };
        self.boolean(verdict)
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
    learn(&mut next, subject.read, settle(read, matched));
    if let Some(compared) = subject.compared {
        // A boolean has two arms, so the fallback settles the comparison
        // just as firmly as naming its value does.
        let held = if matched { value == 1 } else { value == 0 };
        learn(
            &mut next,
            compared.local,
            settle(compared.against, held == compared.equality),
        );
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

/// Records a fact, leaving anything already settled alone.
///
/// A settled value cannot be improved on, and disagreeing with it would mean
/// the arm is unreachable, which this pass does not claim.
fn learn<'tcx>(state: &mut State<'tcx>, local: mir::Local, value: Value<'tcx>) {
    if let Some(slot) = state.get_mut(local.as_usize())
        && slot.is_none()
    {
        *slot = Some(value);
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

/// Drops what is known about one local.
fn forget(state: &mut State<'_>, local: mir::Local) {
    if let Some(slot) = state.get_mut(local.as_usize()) {
        *slot = None;
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
