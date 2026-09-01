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
    ty::{self, Instance, Ty, TyCtxt, TypingEnv},
};

use crate::{
    state::{
        Compared, Path, Places, READINGS, STEPS, State, Subject, Work,
        escaping, forget, refined, retire, root_of, sweep_aliased, sweep_base,
        sweep_indexed, unwind_to, writes,
    },
    summary::{BUDGET, Returns, portable},
    value::{self, Against, Fact, Known, Ranks, Thresholds, Value},
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

/// What one side of a comparison measures the other against, with the local
/// it was read from.
type Measured<'tcx> = Option<(Against<'tcx>, Option<mir::Local>)>;

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
    /// What it leaves in the places it tracks below the return place, so a
    /// caller reading a field of what it was handed reads the value the
    /// body put there.
    pub returned: Vec<(Path, Fact<'tcx>)>,
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
        let places = Places::of(tcx, mir);
        let mut escaped = escaping(tcx, env, mir);
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
            returns: Returns::default(),
            returned: Vec::new(),
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
                    || path.indexed_by(pair.0.local)
                    || (pair.0.is_indirect() && self.aliased(path))
            }
            mir::StatementKind::SetDiscriminant { place, .. } => {
                place.local == path.base
                    || (place.is_indirect() && self.aliased(path))
            }
            mir::StatementKind::StorageLive(other)
            | mir::StatementKind::StorageDead(other) => {
                *other == path.base || path.indexed_by(*other)
            }
            mir::StatementKind::Intrinsic(intrinsic) => {
                !matches!(&**intrinsic, mir::NonDivergingIntrinsic::Assume(..))
            }
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
        let mut work = Work::new(blocks, self.stops());
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
        self.returns = Returns::given_up();
        Reach::everything(blocks)
    }

    /// The values this body compares against.
    ///
    /// They are where a widening step stops, so a counter a loop keeps
    /// below one of them keeps that bound instead of being given the whole
    /// of its type. The value a comparison rules in sits next to the one it
    /// names, so both are recorded.
    fn stops(&self) -> Thresholds {
        let mut stops = Thresholds::none();
        for block in self.mir.basic_blocks.iter() {
            for stmt in &block.statements {
                let mir::StatementKind::Assign(pair) = &stmt.kind else {
                    continue;
                };
                let mir::Rvalue::BinaryOp(op, operands) = &pair.1 else {
                    continue;
                };
                if !matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge)
                {
                    continue;
                }
                for operand in [&operands.0, &operands.1] {
                    let mir::Operand::Constant(konst) = operand else {
                        continue;
                    };
                    let Some(known) = self.constant(konst) else {
                        continue;
                    };
                    stops.add(known.bits);
                    if let Some(under) = known.predecessor() {
                        stops.add(under.bits);
                    }
                    if let Some(over) = known.successor() {
                        stops.add(over.bits);
                    }
                }
            }
        }
        stops
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
                self.constructed(state, place, rvalue);
                self.sized_by(state, place, rvalue);
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
            mir::StatementKind::StorageLive(local) => {
                forget(state, *local);
                sweep_base(state, &self.places, *local);
                sweep_indexed(state, &self.places, *local);
            }
            mir::StatementKind::StorageDead(local) => {
                retire(state, *local);
                sweep_base(state, &self.places, *local);
                sweep_indexed(state, &self.places, *local);
            }
            mir::StatementKind::Intrinsic(intrinsic) => {
                // An assumption is a note to the optimizer, not a write, so
                // what the walk holds about memory survives it. The library
                // states one about a vector's length on the way out of
                // `len`, between the guard reading that length and the
                // check reading it again.
                if let mir::NonDivergingIntrinsic::Assume(operand) =
                    &**intrinsic
                {
                    if self
                        .exact(state, operand)
                        .is_some_and(|value| !value.truth())
                    {
                        return false;
                    }
                } else {
                    // Copying between pointers lands wherever one is aimed.
                    sweep_aliased(state, &self.places, &self.escaped);
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

    /// Records what a constructor put in each of its fields.
    ///
    /// A value handed to a constructor is still that value where the field
    /// is read back, which is what carries a loop counter through the
    /// `Some` an iterator wraps it in, and a constant through the structure
    /// that holds it. Only the fields this body reads somewhere are
    /// recorded, since those are the only ones the walk has a slot for.
    fn constructed(
        &self,
        state: &mut State<'tcx>,
        place: &mir::Place<'tcx>,
        rvalue: &mir::Rvalue<'tcx>,
    ) {
        let mir::Rvalue::Aggregate(kind, fields) = rvalue else {
            return;
        };
        // A write through a pointer lands wherever the pointer is aimed,
        // and the sweep that follows it has already taken these claims.
        if place.is_indirect()
            || !self.places.each().any(|(_, path)| path.base == place.local)
        {
            return;
        }
        let variant = match &**kind {
            mir::AggregateKind::Tuple => None,
            mir::AggregateKind::Adt(did, variant, ..) => {
                let def = self.tcx.adt_def(*did);
                if def.is_union() {
                    return;
                }
                def.is_enum().then_some(*variant)
            }
            _ => return,
        };
        for (index, operand) in fields.iter_enumerated() {
            // An operand reaching into the place being written was read
            // before the write, and says nothing about it afterwards.
            if operand
                .place()
                .is_some_and(|from| from.local == place.local)
            {
                continue;
            }
            let fact = self.fact(state, operand);
            if fact == Fact::default() {
                continue;
            }
            let ty = operand.ty(&self.mir.local_decls, self.tcx);
            let step = mir::ProjectionElem::Field(index, ty);
            let field = variant.map_or_else(
                || place.project_deeper(&[step], self.tcx),
                |at| {
                    place.project_deeper(
                        &[mir::ProjectionElem::Downcast(None, at), step],
                        self.tcx,
                    )
                },
            );
            if let Some(slot) = self.slot_of(&field)
                && let Some(cell) = state.get_mut(slot.as_usize())
            {
                *cell = fact;
            }
        }
    }

    /// Records that the length a slice was built from is that slice's
    /// length.
    ///
    /// A fat pointer takes its metadata from a local, so from there on that
    /// local holds how long what it points at is. Saying so is what makes
    /// two slices cut to one length compare equal, which is the check a
    /// copy between them writes.
    fn sized_by(
        &self,
        state: &mut State<'tcx>,
        place: &mir::Place<'tcx>,
        rvalue: &mir::Rvalue<'tcx>,
    ) {
        let mir::Rvalue::Aggregate(kind, fields) = rvalue else {
            return;
        };
        if !matches!(&**kind, mir::AggregateKind::RawPtr(..)) {
            return;
        }
        let Some(mir::Operand::Copy(from) | mir::Operand::Move(from)) =
            fields.iter().nth(1)
        else {
            return;
        };
        let (Some(local), Some(slot)) = (from.as_local(), self.slot_of(place))
        else {
            return;
        };
        // A local the walk already reads as something says more than this.
        if self.escapes(local)
            || state
                .get(local.as_usize())
                .is_none_or(|held| held.value.is_some())
        {
            return;
        }
        if let Some(cell) = state.get_mut(local.as_usize()) {
            *cell = Fact {
                same: cell.same,
                ..Self::measuring(Value::Length(slot))
            };
        }
    }

    /// Applies a write to a place, forgetting whatever it could reach.
    ///
    /// A write into part of a place can land anywhere inside it, so every
    /// place reached from the same local goes with it; a write through a
    /// pointer can land wherever a pointer could be aimed, so those go too.
    fn overwrite(&self, state: &mut State<'tcx>, place: &mir::Place<'tcx>) {
        // A write through a pointer lands where the pointer aims, not on
        // the local holding it, so the reference stands and so does every
        // claim measured against it: storing into `v[i]` cannot change how
        // long `v` is. What the write could reach is swept below.
        if place.projection.first() != Some(&mir::ProjectionElem::Deref) {
            forget(state, place.local);
            sweep_base(state, &self.places, place.local);
        }
        sweep_indexed(state, &self.places, place.local);
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
                self.branched(bb, discr, targets, &state, work);
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
                    work.merge(drop, after.clone());
                }
                // Glue that unwinds part way through has still run part
                // way, so the cleanup path inherits the same losses.
                unwind_to(*unwind, &after, work);
            }
            // What a body leaves behind is read here rather than after the
            // walk, since a local's claim only stands where it was made.
            TerminatorKind::Return => {
                // The planes that name a local of this body describe
                // nothing outside it, so they are dropped rather than
                // handed to a caller that would read them as its own.
                let first = self.returns.is_new();
                self.left_behind(&state, first);
                let held = Self::known_at(&state, mir::RETURN_PLACE);
                self.returns = self.returns.met(Self::abroad(held));
            }
            _ => Self::onward(kind, state, work),
        }
    }

    /// The claim as it reads outside the body it was made in.
    ///
    /// The planes that name a local describe nothing anywhere else, so a
    /// caller is handed what is left rather than a claim about one of its
    /// own locals that happens to share a number.
    pub fn abroad(held: Fact<'tcx>) -> Fact<'tcx> {
        Fact {
            value: held.value.and_then(portable),
            order: Ranks::none_held(),
            same: None,
            paired: None,
            spans: None,
            over: None,
            ..held
        }
    }

    /// Records what the parts of the return place hold on one path out.
    ///
    /// A structure handed back carries what was put in it, so a field the
    /// caller reads holds what this body wrote there. Every path out has to
    /// agree, the way the return place itself does.
    fn left_behind(&mut self, state: &State<'tcx>, first: bool) {
        let count = self.places.len();
        let base = self.mir.local_decls.len();
        for index in 0..count {
            let slot = mir::Local::from_usize(base.saturating_add(index));
            let Some(path) = self.places.path(slot) else {
                continue;
            };
            if path.base != mir::RETURN_PLACE || !path.portable() {
                continue;
            }
            let fact = Self::abroad(Self::known_at(state, slot));
            match self.returned.iter_mut().find(|(held, _)| *held == path) {
                Some((_, held)) => *held = held.joined(fact),
                None if first => self.returned.push((path, fact)),
                None => {}
            }
        }
    }

    /// Follows a branch into each of its arms, carrying what taking that
    /// arm proves.
    fn branched(
        &self,
        bb: BasicBlock,
        discr: &mir::Operand<'tcx>,
        targets: &mir::SwitchTargets,
        state: &State<'tcx>,
        work: &mut Work<'tcx>,
    ) {
        // A settled condition rules the other arms out; it does not make
        // the arm it does take teach any less. A first turn of a loop that
        // settles the guard has to leave the same claim behind as the
        // turns after it, or what the two agree on is nothing.
        let settled = self.exact(state, discr).map(|known| known.bits);
        let subject = self.subject_of(bb, discr, state);
        let tagged = self.tagged(bb, discr, state);
        let mut taken = Vec::new();
        for (value, target) in targets.iter() {
            taken.push(value);
            if settled.is_some_and(|held| held != value) {
                continue;
            }
            let mut arm = refined(state, subject.as_ref(), Some(value), true);
            Self::teach_tag(&mut arm, tagged, Some(value));
            work.merge(target, arm);
        }
        if settled.is_some_and(|held| taken.contains(&held)) {
            return;
        }
        // A branch whose arms already name every value the condition can
        // hold leaves the fallback nothing to cover.
        if self.covered(state, discr, &taken) {
            return;
        }
        // The fallback covers every value not listed, so it settles the
        // condition only when one value is left over.
        let rest = match taken.as_slice() {
            [only] => Some(*only),
            _ => None,
        };
        let mut arm = refined(state, subject.as_ref(), rest, false);
        Self::teach_tag(&mut arm, tagged, self.leftover(tagged, &taken));
        work.merge(targets.otherwise(), arm);
    }

    /// Whether the arms name every value the condition can hold.
    ///
    /// A value narrowed to a range, by a mask or by arithmetic, reaches the
    /// fallback arm only through a value outside that range. Where the
    /// named arms cover the range there is no such value, and the arm the
    /// compiler writes down anyway is dead. The standard library's bit
    /// packed IO error is decoded this way: two bits are masked off and all
    /// four of them are named.
    fn covered(
        &self,
        state: &State<'tcx>,
        discr: &mir::Operand<'tcx>,
        taken: &[u128],
    ) -> bool {
        let Some(span) = self.spread(state, discr) else {
            return false;
        };
        // Read as bit patterns, which is how the arms are written. A range
        // starting below zero is left alone rather than reasoned about in
        // the wrong order.
        if !span.lo.nonnegative() {
            return false;
        }
        let Some(width) = span
            .hi
            .bits
            .checked_sub(span.lo.bits)
            .and_then(|held| held.checked_add(1))
        else {
            return false;
        };
        // Covering a range takes at least one arm per value in it, which
        // bounds the walk below by the arms the branch was written with.
        let Ok(count) = u128::try_from(taken.len()) else {
            return false;
        };
        if width > count {
            return false;
        }
        (0..width).all(|step| {
            span.lo
                .bits
                .checked_add(step)
                .is_some_and(|value| taken.contains(&value))
        })
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
        let found = self.inspect(
            state,
            call.func,
            call.args,
            call.destination,
            &mut after,
        );
        if found.quiet
            && let Some(slot) = reach.quiet.get_mut(bb.as_usize())
        {
            *slot = true;
        }
        if found.left != Fact::default()
            && let Some(slot) = target
            && let Some(cell) = after.get_mut(slot.as_usize())
        {
            *cell = found.left;
        }
        if let Some(target) = call.target {
            work.merge(target, after);
        }
        // A callee that cannot raise cannot unwind, so nothing reaches the
        // cleanup path through it.
        if let UnwindAction::Cleanup(cleanup) = call.unwind
            && !found.quiet
        {
            // The callee can write through a pointer it was handed and
            // unwind afterwards, so what escaped cannot be read in the
            // cleanup block either. The destination is left alone: a call
            // that unwound never wrote one.
            let mut unwound = state.clone();
            sweep_aliased(&mut unwound, &self.places, &self.escaped);
            work.merge(cleanup, unwound);
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
            compared: if ty.is_bool() {
                self.comparison_behind(bb, read, state)
            } else {
                [None; READINGS]
            },
        })
    }

    /// The comparison that produced a boolean a branch reads.
    fn comparison_behind(
        &self,
        bb: BasicBlock,
        result: mir::Local,
        state: &State<'tcx>,
    ) -> [Option<Compared<'tcx>>; READINGS] {
        let none = [None; READINGS];
        let block = &self.mir.basic_blocks[bb];
        let Some(at) = block.statements.iter().rposition(|s| writes(s, result))
        else {
            return none;
        };
        let mir::StatementKind::Assign(pair) = &block.statements[at].kind
        else {
            return none;
        };
        if pair.0.as_local() != Some(result) {
            return none;
        }
        let mir::Rvalue::BinaryOp(op, operands) = &pair.1 else {
            return none;
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
            return none;
        }
        let after = &block.statements[at.saturating_add(1)..];
        let mut found = self.compared(state, *op, &operands.0, &operands.1);
        for slot in &mut found {
            let Some(measured) = *slot else {
                continue;
            };
            *slot = self.standing(result, after, state, measured);
        }
        found
    }

    /// The claim, rewritten against the place it belongs to, when nothing
    /// between the comparison and the branch has undone it.
    ///
    /// The facts read at the branch have to be the ones that stood when the
    /// comparison ran, so nothing it involved may change in between. Ending
    /// the life of the temporary that was compared, or of the boolean it
    /// produced, is not such a change: the claim is recorded against the
    /// place behind them, which outlives both.
    fn standing(
        &self,
        result: mir::Local,
        after: &[mir::Statement<'tcx>],
        state: &State<'tcx>,
        measured: Compared<'tcx>,
    ) -> Option<Compared<'tcx>> {
        let raw = measured.local;
        let local = root_of(state, raw);
        if self.escapes(local) {
            return None;
        }
        let transient = |s: &mir::Statement<'tcx>| {
            let (mir::StatementKind::StorageLive(of)
            | mir::StatementKind::StorageDead(of)) = s.kind
            else {
                return false;
            };
            if measured.source == Some(of) {
                return false;
            }
            if let Against::Length(len) = measured.against
                && len == of
            {
                return false;
            }
            of == raw || of == result || of == local
        };
        let touched = |s: &mir::Statement<'tcx>| {
            !transient(s)
                && (self.touches(s, local)
                    || self.touches(s, raw)
                    || self.touches(s, result)
                    || measured.source.is_some_and(|of| self.touches(s, of))
                    || match measured.against {
                        Against::Constant(_) => false,
                        Against::Length(of) | Against::Place(of) => {
                            self.touches(s, of)
                        }
                    })
        };
        if after.iter().any(touched) {
            return None;
        }
        Some(Compared { local, ..measured })
    }

    /// The slot an operand was read from, when it names a place.
    fn slot_read(&self, operand: &mir::Operand<'tcx>) -> Option<mir::Local> {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                self.slot_of(place)
            }
            _ => None,
        }
    }

    /// What an operand measures, when the walk can name its value.
    fn named(
        &self,
        state: &State<'tcx>,
        operand: &mir::Operand<'tcx>,
    ) -> Measured<'tcx> {
        if let mir::Operand::Constant(konst) = operand {
            return Some((Against::Constant(self.constant(konst)?), None));
        }
        let held = self.slot_read(operand)?;
        match self.fact(state, operand).value {
            Some(Value::Length(of)) => Some((Against::Length(of), Some(held))),
            // A local the walk has settled measures the same as the
            // constant that could have been written in its place, which is
            // how a value the caller passed in is read.
            Some(Value::Exact(known)) => {
                Some((Against::Constant(known), Some(held)))
            }
            _ => None,
        }
    }

    /// What an operand measures, named by the place it was read from.
    ///
    /// A quantity the walk cannot settle is still one value, and a place
    /// read twice without a write in between reads the same both times.
    /// Naming the place is what carries a guard on a container's length
    /// field to the check that reads the field again, which is how a vector
    /// indexed under `at < v.len()` folds.
    fn sited(
        &self,
        state: &State<'tcx>,
        operand: &mir::Operand<'tcx>,
    ) -> Measured<'tcx> {
        let held = self.slot_read(operand)?;
        let of = root_of(state, held);
        self.places
            .path(of)
            .map(|_| (Against::Place(of), Some(held)))
    }

    /// The length an operand is itself measured by.
    ///
    /// A value below one that is itself measured against a length is below
    /// that length too, which is what a pair of guards written one inside
    /// the other proves. Only the two operators that carry over are read:
    /// the rest say nothing about the length.
    fn chained_to(
        &self,
        state: &State<'tcx>,
        operand: &mir::Operand<'tcx>,
        op: BinOp,
    ) -> Measured<'tcx> {
        if !matches!(op, BinOp::Lt | BinOp::Le) {
            return None;
        }
        let held = self.slot_read(operand)?;
        let (_, of) = self.fact(state, operand).order.first()?;
        Some((Against::Length(of), Some(held)))
    }

    /// The end of an operand's range that an operator reads.
    ///
    /// A value compared against one that lies in a range is compared
    /// against whichever end of that range the operator points at: past
    /// `lo < n`, `n` is above everything `lo` could be, which for an
    /// unsigned pair is above zero. That is what clears the division
    /// written under such a guard.
    fn ended(
        &self,
        state: &State<'tcx>,
        operand: &mir::Operand<'tcx>,
        op: BinOp,
    ) -> Measured<'tcx> {
        let span = self.spread(state, operand)?;
        let end = match op {
            BinOp::Lt | BinOp::Le => span.hi,
            BinOp::Gt | BinOp::Ge => span.lo,
            _ => return None,
        };
        Some((Against::Constant(end), self.slot_read(operand)))
    }

    /// Splits a comparison into the locals it measures, what each is
    /// measured against, and the operator read with that local on the left.
    ///
    /// Two claims come out of one comparison where the operands carry
    /// different kinds of fact: one side settled against a constant, and
    /// the other ordered against a length it was already measured by. Both
    /// hold on the arm, and a loop that proves the first on its way in
    /// needs the second to survive where its arms meet.
    fn compared(
        &self,
        state: &State<'tcx>,
        op: BinOp,
        left: &mir::Operand<'tcx>,
        right: &mir::Operand<'tcx>,
    ) -> [Option<Compared<'tcx>>; READINGS] {
        let read = |operand: &mir::Operand<'tcx>| self.slot_read(operand);
        let measure = |operand: &mir::Operand<'tcx>| self.named(state, operand);
        let placed =
            |operand: &mir::Operand<'tcx>, _: BinOp| self.sited(state, operand);
        let inherited = |operand: &mir::Operand<'tcx>, op: BinOp| {
            self.chained_to(state, operand, op)
        };
        let bounded = |operand: &mir::Operand<'tcx>, op: BinOp| {
            self.ended(state, operand, op)
        };
        // The arm where the comparison fails reads the other end of the
        // same range: what fails `a < b` is `a >= b`, and what bounds `a`
        // from below is the bottom of `b` rather than its top.
        let failing = |operand: &mir::Operand<'tcx>, op: BinOp| {
            self.ended(state, operand, value::negated(op))
        };
        let mirrored = value::mirrored(op);
        let orient =
            |what: &dyn Fn(&mir::Operand<'tcx>, BinOp) -> Measured<'tcx>| {
                [
                    read(left).zip(what(right, op)).map(
                        |(local, (against, source))| Compared {
                            op,
                            local,
                            against,
                            source,
                            arm: None,
                        },
                    ),
                    read(right).zip(what(left, mirrored)).map(
                        |(local, (against, source))| Compared {
                            op: mirrored,
                            local,
                            against,
                            source,
                            arm: None,
                        },
                    ),
                ]
            };
        let measured = orient(&|operand, _| measure(operand));
        let chained = orient(&inherited);
        // Each range reading is for one arm: the end it names is the end
        // that arm's comparison points at.
        let spanned = orient(&bounded).map(|held| {
            held.map(|one| Compared {
                arm: Some(true),
                ..one
            })
        });
        let otherwise = orient(&failing).map(|held| {
            held.map(|one| Compared {
                arm: Some(false),
                ..one
            })
        });
        // A comparison names two operands and either can be the one a claim
        // is recorded against, so every reading of both is kept: they
        // describe the same comparison from different sides and what one
        // proves the others do not. A reading already held is dropped,
        // since repeating it teaches nothing.
        let mut found: [Option<Compared<'tcx>>; READINGS] = [None; READINGS];
        let all = measured
            .into_iter()
            .chain(chained)
            .chain(spanned)
            .chain(otherwise)
            .chain(orient(&placed));
        for candidate in all.flatten() {
            if found.iter().flatten().any(|kept| *kept == candidate) {
                continue;
            }
            if let Some(slot) = found.iter_mut().find(|slot| slot.is_none()) {
                *slot = Some(candidate);
            }
        }
        found
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
                work.merge(
                    target,
                    refined(&state, proved.as_ref(), held, true),
                );
                unwind_to(unwind, &state, work);
            }
        }
    }
}
