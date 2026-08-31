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
    state::{
        Compared, Path, Places, STEPS, State, Subject, Work, escaping, forget,
        refined, root_of, sweep_aliased, sweep_base, unwind_to, writes,
    },
    summary::{BUDGET, Returns, portable},
    value::{self, Against, Bounds, Fact, Known, LenRel, Value, truncate},
};

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
    let entry = folder.blank();
    folder.run(entry)
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

/// Folds one body against the arguments it was instantiated with.
pub struct Folder<'a, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub inst: Instance<'tcx>,
    pub env: TypingEnv<'tcx>,
    pub mir: &'a mir::Body<'tcx>,
    pub escaped: Vec<bool>,
    /// The places this body is tracked at, past its locals.
    pub places: Places,
    /// How many callees deep this body sits below the one being analysed.
    pub depth: u32,
    /// Blocks left to spend on callees, shared with every fold below this
    /// one so the whole chain costs what one body is allowed.
    pub budget: u32,
    /// What the walk has found the body to return.
    pub returns: Returns<'tcx>,
}

impl<'a, 'tcx> Folder<'a, 'tcx> {
    /// Prepares to fold one body.
    pub fn new(
        tcx: TyCtxt<'tcx>,
        inst: Instance<'tcx>,
        env: TypingEnv<'tcx>,
        mir: &'a mir::Body<'tcx>,
        depth: u32,
        budget: u32,
    ) -> Self {
        let places = Places::of(mir);
        let mut escaped = escaping(mir);
        // A place is tracked whatever its base does, since what a pointer
        // could reach is swept where the write happens instead.
        escaped
            .resize(mir.local_decls.len().saturating_add(places.len()), false);
        Self {
            tcx,
            inst,
            env,
            mir,
            escaped,
            places,
            depth,
            budget,
            returns: Returns::Never,
        }
    }

    /// A state with nothing known, one claim wide for every local and every
    /// place the body is tracked at.
    pub fn blank(&self) -> State<'tcx> {
        let width =
            self.mir.local_decls.len().saturating_add(self.places.len());
        vec![Fact::default(); width]
    }

    /// Where a place's claim is recorded, when the walk records one.
    pub fn slot_of(&self, place: &mir::Place<'tcx>) -> Option<mir::Local> {
        let slot = match place.as_local() {
            Some(local) => local,
            None => self.places.slot(place)?,
        };
        (!self.escapes(slot)).then_some(slot)
    }

    /// Whether a write through a pointer could land on a place.
    fn aliased(&self, path: Path) -> bool {
        path.behind_pointer()
            || self
                .escaped
                .get(path.base.as_usize())
                .copied()
                .unwrap_or(true)
    }

    /// Whether a statement can change what a slot holds.
    fn touches(&self, stmt: &mir::Statement<'tcx>, slot: mir::Local) -> bool {
        let Some(path) = self.places.path(slot) else {
            return writes(stmt, slot);
        };
        match &stmt.kind {
            mir::StatementKind::Assign(pair) => {
                pair.0.local == path.base
                    || (pair.0.is_indirect() && self.aliased(path))
            }
            mir::StatementKind::SetDiscriminant { place, .. } => {
                place.local == path.base
                    || (place.is_indirect() && self.aliased(path))
            }
            mir::StatementKind::StorageLive(other)
            | mir::StatementKind::StorageDead(other) => *other == path.base,
            mir::StatementKind::Intrinsic(_) => true,
            _ => false,
        }
    }

    /// Whether a pointer could be aimed at a local, so its value is never
    /// assumed. A local the walk has never heard of is treated as escaping.
    pub fn escapes(&self, local: mir::Local) -> bool {
        self.escaped.get(local.as_usize()).copied().unwrap_or(true)
    }

    /// Runs the walk to a fixpoint.
    pub fn run(&mut self, entry: State<'tcx>) -> Reach {
        let blocks = self.mir.basic_blocks.len();
        let locals =
            self.mir.local_decls.len().saturating_add(self.places.len());
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
                // The value is read before the write is applied, so an
                // rvalue naming the target reads its old value, and the
                // slot is found before the write sweeps it.
                let mut fact = self.rvalue(state, rvalue);
                let target = self.slot_of(place);
                self.overwrite(state, place);
                if fact.same == target {
                    // A link to the place being written says nothing.
                    fact.same = None;
                }
                if let Some(slot) = target
                    && let Some(cell) = state.get_mut(slot.as_usize())
                {
                    *cell = fact;
                }
            }
            mir::StatementKind::SetDiscriminant {
                place,
                variant_index,
            } => {
                let tag = self.enum_at(place).and_then(|ty| match ty.kind() {
                    ty::Adt(def, _) => Some(
                        def.discriminant_for_variant(self.tcx, *variant_index)
                            .val,
                    ),
                    _ => None,
                });
                let slot = self.slot_of(place);
                self.overwrite(state, place);
                if let Some(slot) = slot
                    && let Some(cell) = state.get_mut(slot.as_usize())
                {
                    cell.tag = tag;
                }
            }
            mir::StatementKind::StorageLive(local)
            | mir::StatementKind::StorageDead(local) => {
                forget(state, *local);
                sweep_base(state, &self.places, *local);
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
                // Copying between pointers lands wherever one is aimed.
                sweep_aliased(state, &self.places, &self.escaped);
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

    /// Applies a write to a place, forgetting whatever it could reach.
    ///
    /// A write into part of a place can land anywhere inside it, so every
    /// place reached from the same local goes with it; a write through a
    /// pointer can land wherever a pointer could be aimed, so those go too.
    fn overwrite(&self, state: &mut State<'tcx>, place: &mir::Place<'tcx>) {
        forget(state, place.local);
        sweep_base(state, &self.places, place.local);
        if place.is_indirect() {
            sweep_aliased(state, &self.places, &self.escaped);
        }
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
                self.overwrite(&mut after, place);
                // Glue runs a body this walk did not read, and it holds a
                // pointer to what it drops.
                sweep_aliased(&mut after, &self.places, &self.escaped);
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
        let tagged = self.tagged(bb, discr, &state);
        let mut taken = Vec::new();
        for (value, target) in targets.iter() {
            taken.push(value);
            let mut arm = refined(&state, subject, Some(value), true);
            Self::teach_tag(&mut arm, tagged, Some(value));
            work.merge(target, arm);
        }
        // The fallback covers every value not listed, so it settles the
        // condition only when one value is left over.
        let rest = match taken.as_slice() {
            [only] => Some(*only),
            _ => None,
        };
        let mut arm = refined(&state, subject, rest, false);
        Self::teach_tag(&mut arm, tagged, self.leftover(tagged, &taken));
        work.merge(targets.otherwise(), arm);
    }

    /// The place a branch's discriminant was read from.
    ///
    /// Only this block is read, and the reading may not be undone before
    /// the branch, so what the arm proves is about the value it branched
    /// on.
    fn tagged(
        &self,
        bb: BasicBlock,
        discr: &mir::Operand<'tcx>,
        state: &State<'tcx>,
    ) -> Option<(mir::Local, Ty<'tcx>)> {
        let (mir::Operand::Copy(place) | mir::Operand::Move(place)) = discr
        else {
            return None;
        };
        let read = place.as_local()?;
        let block = &self.mir.basic_blocks[bb];
        let at = block.statements.iter().rposition(|s| writes(s, read))?;
        let mir::StatementKind::Assign(pair) = &block.statements[at].kind
        else {
            return None;
        };
        if pair.0.as_local() != Some(read) {
            return None;
        }
        let mir::Rvalue::Discriminant(of) = &pair.1 else {
            return None;
        };
        let slot = self.slot_of(of)?;
        let ty = self.enum_at(of)?;
        let after = &block.statements[at.saturating_add(1)..];
        if after
            .iter()
            .any(|s| self.touches(s, read) || self.touches(s, slot))
        {
            return None;
        }
        Some((root_of(state, slot), ty))
    }

    /// The one tag a fallback arm proves, when every other is named.
    fn leftover(
        &self,
        tagged: Option<(mir::Local, Ty<'tcx>)>,
        taken: &[u128],
    ) -> Option<u128> {
        let ty::Adt(def, _) = tagged?.1.kind() else {
            return None;
        };
        let mut left = None;
        for variant in def.variants().indices() {
            let tag = def.discriminant_for_variant(self.tcx, variant).val;
            if taken.contains(&tag) {
                continue;
            }
            if left.is_some() {
                return None;
            }
            left = Some(tag);
        }
        left
    }

    /// Records the tag an arm proves the enum carries.
    fn teach_tag(
        state: &mut State<'tcx>,
        tagged: Option<(mir::Local, Ty<'tcx>)>,
        tag: Option<u128>,
    ) {
        let (Some((slot, _)), Some(tag)) = (tagged, tag) else {
            return;
        };
        if let Some(cell) = state.get_mut(slot.as_usize()) {
            cell.tag = Some(tag);
        }
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
        let target = self.slot_of(&call.destination);
        self.overwrite(&mut after, &call.destination);
        // What the callee was handed a pointer to is not read by this walk.
        sweep_aliased(&mut after, &self.places, &self.escaped);
        let found = self.inspect(state, call.func, call.args, call.destination);
        if found.quiet
            && let Some(slot) = reach.quiet.get_mut(bb.as_usize())
        {
            *slot = true;
        }
        if let Some(value) = found.value
            && let Some(slot) = target
            && let Some(cell) = after.get_mut(slot.as_usize())
        {
            *cell = Fact::of(value);
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
        let read = root_of(state, self.slot_of(place)?);
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
        let touched = |s: &mir::Statement<'tcx>| {
            self.touches(s, local)
                || self.touches(s, raw)
                || self.touches(s, result)
                || measured.source.is_some_and(|of| self.touches(s, of))
                || match measured.against {
                    Against::Constant(_) => false,
                    Against::Length(of) => self.touches(s, of),
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
                self.slot_of(place)
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
            op: value::mirrored(op),
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
            mir::Rvalue::Cast(
                mir::CastKind::Transmute
                | mir::CastKind::PointerExposeProvenance
                | mir::CastKind::PtrToPtr,
                operand,
                ty,
            ) => return self.reinterpreted(state, operand, *ty),
            mir::Rvalue::BinaryOp(op, pair) => {
                return self.operated(state, *op, pair);
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
            // A place has an address, so a pointer taken of one is never
            // null however the place was reached.
            mir::Rvalue::Ref(..) | mir::Rvalue::RawPtr(..) => {
                return Fact {
                    address: true,
                    ..Fact::default()
                };
            }
            // Reading the discriminant of an enum the walk has settled is
            // what folds the match below it.
            mir::Rvalue::Discriminant(place) => self.tag_read(state, place),
            mir::Rvalue::Aggregate(kind, _) => {
                let mir::AggregateKind::Adt(did, variant, args, ..) = &**kind
                else {
                    return Fact::default();
                };
                return Fact {
                    tag: self.tag_of(*did, args, *variant),
                    ..Fact::default()
                };
            }
            _ => None,
        };
        Fact {
            value,
            ..Fact::default()
        }
    }

    /// Reads a value out at another type without changing its bits.
    ///
    /// An address and the value inside a nonzero wrapper both come out this
    /// way, and neither of them is zero.
    fn reinterpreted(
        &self,
        state: &State<'tcx>,
        operand: &mir::Operand<'tcx>,
        ty: Ty<'tcx>,
    ) -> Fact<'tcx> {
        if self.fact(state, operand).address {
            return Fact {
                address: true,
                value: self.apart_from_zero(ty),
                ..Fact::default()
            };
        }
        let value = self
            .monomorphize(operand.ty(&self.mir.local_decls, self.tcx))
            .filter(|source| self.is_nonzero(*source))
            .and_then(|_| self.apart_from_zero(ty));
        Fact {
            value,
            ..Fact::default()
        }
    }

    /// Applies a binary operator to what its operands are known about.
    fn operated(
        &self,
        state: &State<'tcx>,
        op: BinOp,
        pair: &(mir::Operand<'tcx>, mir::Operand<'tcx>),
    ) -> Fact<'tcx> {
        let left = self.fact(state, &pair.0);
        let right = self.fact(state, &pair.1);
        // The remainder of an unsigned value by the length of a slice lands
        // below that length, which is what the slice's own bounds check
        // asks. The length is nonzero wherever this runs, since the
        // remainder's own check has passed to get here.
        if op == BinOp::Rem
            && let Some(Value::Length(of)) = right.value
            && self.unsigned(&pair.0)
        {
            return Fact {
                order: Some((LenRel::Below, of)),
                ..Fact::default()
            };
        }
        Fact {
            value: self.binary(op, left, right),
            ..Fact::default()
        }
    }

    /// Whether an operand is read as an unsigned integer.
    fn unsigned(&self, operand: &mir::Operand<'tcx>) -> bool {
        self.monomorphize(operand.ty(&self.mir.local_decls, self.tcx))
            .is_some_and(|ty| matches!(ty.kind(), ty::Uint(_)))
    }

    /// The value the discriminant of a settled place reads as.
    fn tag_read(
        &self,
        state: &State<'tcx>,
        place: &mir::Place<'tcx>,
    ) -> Option<Value<'tcx>> {
        let slot = self.slot_of(place)?;
        let tag = Self::known_at(state, slot).tag?;
        let ty = self.enum_at(place)?;
        let ty::Adt(def, _) = ty.kind() else {
            return None;
        };
        for variant in def.variants().indices() {
            let discr = def.discriminant_for_variant(self.tcx, variant);
            if discr.val != tag {
                continue;
            }
            let width = self.width(discr.ty)?;
            return Some(Value::Exact(Known {
                bits: truncate(discr.val, width),
                ty: discr.ty,
                width,
            }));
        }
        None
    }

    /// The tag one variant of an enum carries.
    fn tag_of(
        &self,
        did: rustc_span::def_id::DefId,
        args: ty::GenericArgsRef<'tcx>,
        variant: rustc_abi::VariantIdx,
    ) -> Option<u128> {
        let ty = self.monomorphize(Ty::new_adt(
            self.tcx,
            self.tcx.adt_def(did),
            args,
        ))?;
        let ty::Adt(def, _) = ty.kind() else {
            return None;
        };
        if !def.is_enum() {
            return None;
        }
        Some(def.discriminant_for_variant(self.tcx, variant).val)
    }

    /// The enum type of a place, when it is one.
    fn enum_at(&self, place: &mir::Place<'tcx>) -> Option<Ty<'tcx>> {
        let ty =
            self.monomorphize(place.ty(&self.mir.local_decls, self.tcx).ty)?;
        matches!(ty.kind(), ty::Adt(def, _) if def.is_enum()).then_some(ty)
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
        let local = root_of(state, self.slot_of(place)?);
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
    pub fn fact(
        &self,
        state: &State<'tcx>,
        operand: &mir::Operand<'tcx>,
    ) -> Fact<'tcx> {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                let mut held =
                    self.slot_of(place).map_or_else(Fact::default, |slot| {
                        Self::known_at(state, slot)
                    });
                if matches!(
                    operand.ty(&self.mir.local_decls, self.tcx).kind(),
                    ty::Ref(..)
                ) {
                    held.address = true;
                }
                held
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
    pub fn known_at(state: &State<'tcx>, local: mir::Local) -> Fact<'tcx> {
        let Some(own) = state.get(local.as_usize()).copied() else {
            return Fact::default();
        };
        let held = own.same.map_or(own, |root| {
            let at_root =
                state.get(root.as_usize()).copied().unwrap_or_default();
            Fact {
                value: own.value.or(at_root.value),
                order: own.order.or(at_root.order),
                address: own.address || at_root.address,
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
        let Some(local) = self.slot_of(place) else {
            return fact;
        };
        let root = root_of(state, local);
        if !self.escapes(root) {
            fact.same = Some(root);
        }
        fact
    }

    /// Evaluates a constant for the arguments this body was reached with.
    ///
    /// A body still carrying parameters has no value for a constant written
    /// against one: `<T as SizedTypeProperties>::SIZE` is exactly what the
    /// interesting checks compare against, and it has none until `T` has
    /// one. A constant that names no parameter is the same in every
    /// instantiation, so it is read where it stands.
    fn constant(&self, konst: &mir::ConstOperand<'tcx>) -> Option<Known<'tcx>> {
        let konst = if self.inst.args.has_param() {
            if konst.const_.has_param() {
                return None;
            }
            konst.const_
        } else {
            self.inst
                .try_instantiate_mir_and_normalize_erasing_regions(
                    self.tcx,
                    self.env,
                    ty::EarlyBinder::bind(self.tcx, konst.const_),
                )
                .ok()?
        };
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
    ///
    /// A value nothing is known about still lies inside its own type, and
    /// that is the whole claim where the source is narrow: a byte read into
    /// an index is below two hundred and fifty six wherever it came from.
    fn cast(
        &self,
        state: &State<'tcx>,
        operand: &mir::Operand<'tcx>,
        ty: Ty<'tcx>,
    ) -> Option<Value<'tcx>> {
        let source =
            self.monomorphize(operand.ty(&self.mir.local_decls, self.tcx))?;
        let held = self.fact(state, operand).value;
        if matches!(held, Some(Value::Length(_))) {
            return None;
        }
        let value = match held {
            Some(value) if value.ty() == Some(source) => value,
            _ => Value::Within(self.whole(source)?),
        };
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
    pub fn width(&self, ty: Ty<'tcx>) -> Option<u32> {
        if !matches!(ty.kind(), ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_))
        {
            return None;
        }
        let layout = self.tcx.layout_of(self.env.as_query_input(ty)).ok()?;
        u32::try_from(layout.size.bits()).ok()
    }

    /// Resolves a type written in the body against this instantiation.
    pub fn monomorphize(&self, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
        self.inst
            .try_instantiate_mir_and_normalize_erasing_regions(
                self.tcx,
                self.env,
                ty::EarlyBinder::bind(self.tcx, ty),
            )
            .ok()
    }
}
