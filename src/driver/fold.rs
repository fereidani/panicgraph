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

/// What every local is known to hold at one point.
type State<'tcx> = Vec<Option<Known<'tcx>>>;

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
                        .operand(state, operand)
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
                if let Some(value) = self.operand(&state, discr) {
                    work.merge(targets.target_for_value(value.bits), state);
                    return;
                }
                for target in targets.all_targets() {
                    work.merge(*target, state.clone());
                }
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
        match self.operand(&state, cond).map(Known::truth) {
            Some(actual) if actual == expected => {
                if let Some(slot) = reach.settled.get_mut(bb.as_usize()) {
                    *slot = true;
                }
                work.merge(target, state);
            }
            // The check fails every time, so only the panic path continues.
            Some(_) => unwind_to(unwind, &state, work),
            None => {
                work.merge(target, state.clone());
                unwind_to(unwind, &state, work);
            }
        }
    }

    /// Evaluates an rvalue against what the locals are known to hold.
    fn rvalue(
        &self,
        state: &State<'tcx>,
        rvalue: &mir::Rvalue<'tcx>,
    ) -> Option<Known<'tcx>> {
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
                let value = self.operand(state, operand)?;
                let bits = if value.ty.is_bool() {
                    u128::from(!value.truth())
                } else {
                    truncate(!value.bits, value.width)
                };
                Some(Known { bits, ..value })
            }
            _ => None,
        }
    }

    /// Reads an operand.
    fn operand(
        &self,
        state: &State<'tcx>,
        operand: &mir::Operand<'tcx>,
    ) -> Option<Known<'tcx>> {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                let local = place.as_local()?;
                *state.get(local.as_usize())?
            }
            mir::Operand::Constant(konst) => self.constant(konst),
            // Whether a check is on is settled by the session compiling the
            // crate, which is what makes a standard library block vanish in
            // a build that turns the check off.
            mir::Operand::RuntimeChecks(check) => {
                self.boolean(check.value(self.tcx.sess))
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
    ) -> Option<Known<'tcx>> {
        let value = self.operand(state, operand)?;
        let ty = self.monomorphize(ty)?;
        let width = self.width(ty)?;
        // Narrowing keeps the low bits and widening copies the sign of the
        // source, which is what the machine does.
        let extended = if value.is_signed() {
            value.as_signed().cast_unsigned()
        } else {
            value.bits
        };
        Some(Known {
            bits: truncate(extended, width),
            ty,
            width,
        })
    }

    /// Applies an operator the folder can evaluate exactly.
    ///
    /// Arithmetic is deliberately absent. The checks worth folding compare a
    /// size against a bound, and every further operator is another chance to
    /// disagree with the machine and drop a panic that is real.
    fn binary(
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
