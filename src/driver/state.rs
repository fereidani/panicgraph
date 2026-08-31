//! What the walk knows at one point in a body, and how it changes.
//!
//! A claim is about one local at one place, so it lives only as long as the
//! value it was drawn from: a write to a local sweeps it, and a block two
//! predecessors reach keeps only what both leave behind. The worklist here
//! is what turns those two rules into a walk that ends, by widening a claim
//! that is still moving after the arms of a branch have met.

use std::collections::VecDeque;

use rustc_middle::{
    mir::{self, BasicBlock, BinOp, UnwindAction},
    ty::Ty,
};

use crate::value::{
    self, Against, Bounds, Fact, Known, Taught, Value, truncate,
};

/// How many times a block's entry is joined exactly before what arrives is
/// widened.
///
/// Two is what a branch and its else arm need: the block they meet at is
/// recorded from the first arm and joined with the second. A third arrival
/// is a loop coming round, where a range that moves has to be pushed to the
/// end of its type rather than creeping there an iteration at a time.
pub const PRECISE: u32 = 2;

/// How many times one local's claim can change before it holds nothing.
///
/// Two exact joins, a widening step for each end of a range, and the range
/// itself given up, for each of the two ranges a fact can hold. The walk's
/// bound is built from this.
pub const STEPS: usize = 12;

/// What every local is known about at one point.
pub type State<'tcx> = Vec<Fact<'tcx>>;

/// What a branch reads, and what its arms therefore prove.
#[derive(Debug, Clone, Copy)]
pub struct Subject<'tcx> {
    /// The local the branch reads, which every arm settles.
    pub read: mir::Local,
    pub ty: Ty<'tcx>,
    pub width: u32,
    /// The comparison it stands for, when it is a boolean holding one.
    pub compared: Option<Compared<'tcx>>,
}

/// A comparison a branch turns into a fact about the local it measured.
#[derive(Debug, Clone, Copy)]
pub struct Compared<'tcx> {
    /// The operator, read with the measured local on the left.
    pub op: BinOp,
    pub local: mir::Local,
    pub against: Against<'tcx>,
    /// The local the other side was read from, when it was not written as
    /// a constant. What that local holds now is what the comparison is
    /// read against, so a write to it in between ends the claim.
    pub source: Option<mir::Local>,
}

/// The blocks still to visit, and what each is entered with.
pub struct Work<'tcx> {
    entry: Vec<Option<State<'tcx>>>,
    queued: Vec<bool>,
    changes: Vec<u32>,
    queue: VecDeque<BasicBlock>,
}

impl<'tcx> Work<'tcx> {
    /// Prepares a worklist over a body of `blocks` blocks.
    pub fn new(blocks: usize) -> Self {
        Self {
            entry: vec![None; blocks],
            queued: vec![false; blocks],
            changes: vec![0; blocks],
            queue: VecDeque::new(),
        }
    }

    /// Records what a block is entered with, queueing it if that changed.
    ///
    /// A block is first recorded with whatever its predecessor knew, and
    /// afterwards only ever widens: what two predecessors agree on stands,
    /// and what they do not is given up. Past `PRECISE` arrivals a claim
    /// that is still moving is pushed to the end of its type instead, so a
    /// local's claim changes a bounded number of times whatever the shape
    /// of the body. That is what bounds the walk.
    pub fn merge(&mut self, bb: BasicBlock, incoming: State<'tcx>) {
        let widen = self
            .changes
            .get(bb.as_usize())
            .is_some_and(|seen| *seen >= PRECISE);
        let Some(slot) = self.entry.get_mut(bb.as_usize()) else {
            return;
        };
        match slot {
            None => *slot = Some(incoming),
            Some(existing) => {
                let mut changed = false;
                for (held, arriving) in existing.iter_mut().zip(&incoming) {
                    let mut next = held.joined(*arriving);
                    if next == *held {
                        continue;
                    }
                    if widen {
                        next = next.widened(*held);
                    }
                    *held = next;
                    changed = true;
                }
                if !changed {
                    return;
                }
            }
        }
        if let Some(seen) = self.changes.get_mut(bb.as_usize()) {
            *seen = seen.saturating_add(1);
        }
        if let Some(queued) = self.queued.get_mut(bb.as_usize())
            && !*queued
        {
            *queued = true;
            self.queue.push_back(bb);
        }
    }

    /// Whether every block has been visited with its settled state.
    pub fn is_drained(&self) -> bool {
        self.queue.is_empty()
    }

    /// Takes the next block to visit, with the state it is entered with.
    ///
    /// A block is queued only once its state is recorded, so the state is
    /// always there; the walk simply skips a block if it ever is not, rather
    /// than ending early and leaving the rest of the body unvisited.
    pub fn pop(&mut self) -> Option<(BasicBlock, State<'tcx>)> {
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
pub fn escaping(mir: &mir::Body<'_>) -> Vec<bool> {
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

/// The local a local's link of sameness points at, or the local itself.
pub fn root_of(state: &State<'_>, local: mir::Local) -> mir::Local {
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
pub fn refined<'tcx>(
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
pub fn settle(known: Known<'_>, holds: bool) -> Value<'_> {
    if holds {
        Value::Exact(known)
    } else {
        Value::other_than(known)
    }
}

/// Records what a branch taught, narrowing what was already held.
///
/// A second bound on the same local adds to the first rather than replacing
/// it, so a pair of guards leaves the range they both describe. A settled
/// claim cannot be improved on, and disagreeing with one would mean the arm
/// is unreachable, which this pass does not claim. The two planes fill
/// independently: a counter that is exactly zero can still learn that it is
/// below a length.
pub fn learn<'tcx>(
    state: &mut State<'tcx>,
    local: mir::Local,
    taught: Taught<'tcx>,
) {
    // A local holding the length of a slice teaches the slice rather than
    // itself, so a guard on emptiness still stands at the next reading of
    // that length, which is a local of its own.
    if let Taught::Value(value) = taught
        && let Some(Value::Length(of)) =
            state.get(local.as_usize()).and_then(|slot| slot.value)
    {
        stretch(state, of, value);
        return;
    }
    let Some(slot) = state.get_mut(local.as_usize()) else {
        return;
    };
    match taught {
        Taught::Value(value) => {
            slot.value =
                Some(slot.value.map_or(value, |held| held.refined(value)));
        }
        Taught::Order(rel, of) => {
            if slot.order.is_none() {
                slot.order = Some((rel, of));
            }
        }
    }
}

/// Narrows how long the slice behind a local is known to be.
///
/// The claim starts as everything the length's own type admits, so what a
/// guard rules out is all that has to be recorded.
pub fn stretch<'tcx>(
    state: &mut State<'tcx>,
    of: mir::Local,
    taught: Value<'tcx>,
) {
    let Some(slot) = state.get_mut(of.as_usize()) else {
        return;
    };
    let whole = taught
        .anchor()
        .and_then(|end| Bounds::new(end.type_min(), end.type_max()));
    let Some(held) = slot.extent.or(whole) else {
        return;
    };
    slot.extent = Value::Within(held).refined(taught).bounds();
}

/// Whether a statement can change a local.
///
/// Anything not modelled is treated as able to write anywhere, so a fact
/// never outlives the value it was drawn from.
pub fn writes(stmt: &mir::Statement<'_>, local: mir::Local) -> bool {
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
pub fn forget(state: &mut State<'_>, local: mir::Local) {
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
pub fn unwind_to<'tcx>(
    unwind: UnwindAction,
    state: &State<'tcx>,
    work: &mut Work<'tcx>,
) {
    if let UnwindAction::Cleanup(target) = unwind {
        work.merge(target, state.clone());
    }
}

/// One step from a local to a place inside it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Step {
    /// Through a pointer.
    Deref,
    /// Into a field.
    Field(u32),
    /// Into the payload of one variant.
    Variant(u32),
}

/// How far from a local a tracked place may sit.
const REACH: usize = 3;

/// How many places one body may be tracked at.
///
/// Every slot costs a claim in every block's entry state, so the table is
/// capped rather than following a body wherever it goes.
const TRACKED: usize = 32;

/// A place the walk records claims against.
///
/// A field read twice is two locals and one place, and it is the place the
/// claim belongs to: what a guard proves about the first read has to be
/// there for the second.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Path {
    /// The local the place is reached from.
    pub base: mir::Local,
    steps: [Option<Step>; REACH],
}

impl Path {
    /// The place, when it is one this walk can name.
    fn of(place: &mir::Place<'_>) -> Option<Self> {
        if place.projection.is_empty() {
            return None;
        }
        let mut steps = [None; REACH];
        for (slot, element) in steps.iter_mut().zip(place.projection) {
            *slot = Some(match element {
                mir::ProjectionElem::Deref => Step::Deref,
                mir::ProjectionElem::Field(field, _) => {
                    Step::Field(field.as_u32())
                }
                mir::ProjectionElem::Downcast(_, variant) => {
                    Step::Variant(variant.as_u32())
                }
                // An index is a value in its own right, and a subslice or a
                // cast is not a place this walk can tell apart from another.
                _ => return None,
            });
        }
        if place.projection.len() > REACH {
            return None;
        }
        Some(Self {
            base: place.local,
            steps,
        })
    }

    /// Whether the place is reached through a pointer, so a write through
    /// any pointer could land on it.
    pub fn behind_pointer(self) -> bool {
        self.steps.iter().flatten().any(|step| *step == Step::Deref)
    }
}

/// The places one body is tracked at, and where each sits in the state.
///
/// Slots are laid out past the locals, so a place is named by a local index
/// like any other claim and every rule about forgetting and merging applies
/// to it unchanged.
pub struct Places {
    paths: Vec<Path>,
    first: usize,
}

impl Places {
    /// Collects the places a body reads or writes.
    pub fn of(mir: &mir::Body<'_>) -> Self {
        let mut collect = Collect { found: Vec::new() };
        mir::visit::Visitor::visit_body(&mut collect, mir);
        Self {
            paths: collect.found,
            first: mir.local_decls.len(),
        }
    }

    /// How many places are tracked.
    pub const fn len(&self) -> usize {
        self.paths.len()
    }

    /// The slot a place is recorded at.
    pub fn slot(&self, place: &mir::Place<'_>) -> Option<mir::Local> {
        let path = Path::of(place)?;
        let at = self.paths.iter().position(|held| *held == path)?;
        Some(mir::Local::from_usize(self.first.saturating_add(at)))
    }

    /// The place a slot records, when the slot is one.
    pub fn path(&self, slot: mir::Local) -> Option<Path> {
        self.paths
            .get(slot.as_usize().checked_sub(self.first)?)
            .copied()
    }

    /// Every slot with the place it records.
    pub fn each(&self) -> impl Iterator<Item = (mir::Local, Path)> + '_ {
        self.paths.iter().enumerate().map(|(at, path)| {
            (mir::Local::from_usize(self.first.saturating_add(at)), *path)
        })
    }
}

/// Gathers the places of a body as the visitor walks it.
struct Collect {
    found: Vec<Path>,
}

impl<'tcx> mir::visit::Visitor<'tcx> for Collect {
    fn visit_place(
        &mut self,
        place: &mir::Place<'tcx>,
        _: mir::visit::PlaceContext,
        _: mir::Location,
    ) {
        if self.found.len() >= TRACKED {
            return;
        }
        let Some(path) = Path::of(place) else {
            return;
        };
        if !self.found.contains(&path) {
            self.found.push(path);
        }
    }
}

/// Forgets every place reached from a local.
///
/// A write to the local puts a different value there, and a write into part
/// of it can land anywhere inside, so neither leaves a claim about what it
/// holds standing.
pub fn sweep_base(state: &mut State<'_>, places: &Places, base: mir::Local) {
    for (slot, path) in places.each() {
        if path.base == base {
            forget(state, slot);
        }
    }
}

/// Forgets every place a write through a pointer could reach.
///
/// That is every place read through a pointer, and every place inside a
/// local whose address was taken, since a pointer can only be aimed at one
/// of those.
pub fn sweep_aliased(state: &mut State<'_>, places: &Places, escaped: &[bool]) {
    for (slot, path) in places.each() {
        if path.behind_pointer()
            || escaped.get(path.base.as_usize()).copied().unwrap_or(true)
        {
            forget(state, slot);
        }
    }
}
