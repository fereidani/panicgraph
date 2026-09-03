//! What the walk finds a call does.
//!
//! A call is the edge of what one body says. Reading the callee is what
//! carries a value across it, and what shows that a check the callee makes
//! cannot fail for the arguments this call site hands it. A contract
//! answers first where one holds for every implementation the resolution
//! can reach, since it costs nothing to read.

use panicgraph::util::Map;
use rustc_middle::{
    mir::{self, TerminatorKind},
    ty::{self, Instance, Ty, TypeVisitableExt, TypingEnv},
};
use rustc_span::{Spanned, sym};

use crate::{
    fold::{Folder, Reach},
    sinks::SinkTable,
    state::{Path, State, put},
    value::{self, Bounds, Fact, Known, LenRel, Ranks, Value},
};

/// How far a chain of calls is followed for what it does.
///
/// Each step is one more body on the stack. A value worth reading out of a
/// call sits shallow, but showing that a call raises nothing means reading
/// every call it makes in turn, and the standard library reaches an unsafe
/// primitive several wrappers down: `chunks_exact` calls a constructor
/// which calls a split which calls the pointer arithmetic under it.
pub const DEPTH: u32 = 3;

/// How many blocks folding one body may spend on the callees it reads
/// values out of.
///
/// A summary is only asked for where the answer would settle a check, so
/// the budget is rarely touched. It is what keeps a body that calls into a
/// wide subgraph from paying for all of it.
pub const BUDGET: u32 = 4096;

/// What every path out of a body was found to leave in the return place.
#[derive(Debug, Clone, Copy, Default)]
pub struct Returns<'tcx> {
    /// What the paths walked so far agree on.
    held: Fact<'tcx>,
    /// Whether a path that returns has been walked at all.
    walked: bool,
    /// Whether the walk was cut short, so what it found says nothing about
    /// every path out.
    partial: bool,
}

impl<'tcx> Returns<'tcx> {
    /// Adds what one path out of the body leaves behind.
    pub fn met(self, left: Fact<'tcx>) -> Self {
        Self {
            held: if self.walked {
                self.held.joined(left)
            } else {
                left
            },
            walked: true,
            ..self
        }
    }

    /// Whether no path that returns has been walked yet.
    pub const fn is_new(self) -> bool {
        !self.walked
    }

    /// Gives up on saying anything about what the body leaves behind.
    pub const fn given_up() -> Self {
        Self {
            held: Fact::blank(),
            walked: false,
            partial: true,
        }
    }

    /// The claim every path agrees on.
    ///
    /// A body no path returns from has none: the call never comes back, so
    /// there is nothing for the caller to read, and neither has a walk that
    /// did not reach every path out.
    pub fn claim(self) -> Fact<'tcx> {
        if self.partial || !self.walked {
            return Fact::default();
        }
        self.held
    }
}

/// What folding a callee once found, kept for every later call that hands
/// it the same claims.
///
/// A body folded against one entry state answers the same way every time,
/// and the same few bodies are folded from everywhere: the index check the
/// standard library writes sits under every slice read in a crate. Keeping
/// the answer is what lets a chain of calls be followed further without
/// paying for each link at each site.
#[derive(Debug, Clone)]
pub struct Summary<'tcx> {
    /// What every path out of the callee leaves in the return place.
    pub left: Fact<'tcx>,
    /// What it leaves in the places below the return place.
    pub returned: Vec<(Path, Fact<'tcx>)>,
    /// Whether the callee, walked with these claims, can still raise.
    pub quiet: bool,
}

/// What a summary is kept under: the body, how many more calls the walk
/// may read below it, and what the call site told it.
pub type Key<'tcx> = (Instance<'tcx>, u32, State<'tcx>);

/// Every summary the extraction has found so far.
pub type Cache<'tcx> = Map<Key<'tcx>, Summary<'tcx>>;

/// What folding a callee at one call site found.
#[derive(Debug, Clone, Copy, Default)]
pub struct Found<'tcx> {
    /// What every path out of the callee leaves behind.
    pub left: Fact<'tcx>,
    /// Whether the callee, walked with these arguments, can still raise.
    pub quiet: bool,
}

/// What one argument of a call tells the parameter it becomes.
struct Carried<'tcx> {
    /// Where the argument's claims live in the caller, so a claim naming it
    /// can be rewritten to name the parameter.
    slot: Option<mir::Local>,
    /// The local the argument was read from whole, which is what the places
    /// inside it are recorded against.
    base: Option<mir::Local>,
    /// Whether the argument arrives at the type the parameter is declared
    /// with, which is what makes a claim about it describe the same value.
    alike: bool,
    fact: Fact<'tcx>,
}

/// The claim, when it means the same thing outside the body it was read in.
///
/// A length names a local of that body, so it says nothing anywhere else.
pub const fn portable(value: Value<'_>) -> Option<Value<'_>> {
    match value {
        Value::Exact(_) | Value::Other(_) | Value::Within(_) => Some(value),
        Value::Length(_) => None,
    }
}

impl<'tcx> Folder<'_, 'tcx> {
    /// What a call was found to do.
    ///
    /// A contract answers first, since it holds for every implementation
    /// the resolution can reach and costs nothing to read. Anything else is
    /// answered by folding the callee, which is what carries a value
    /// through a call the caller cannot see past, and what proves that a
    /// precondition the caller satisfies leaves the callee nothing to
    /// raise.
    pub fn inspect(
        &mut self,
        state: &State<'tcx>,
        func: &mir::Operand<'tcx>,
        args: &[Spanned<mir::Operand<'tcx>>],
        destination: mir::Place<'tcx>,
        after: &mut State<'tcx>,
        cache: &mut Cache<'tcx>,
    ) -> Found<'tcx> {
        let Some(ty) = self.ty_of(func) else {
            return Found::default();
        };
        if let Some(left) = self.contracted(state, ty, args, destination) {
            return Found { left, quiet: false };
        }
        self.folded(state, ty, args, destination, after, cache)
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
        args: &[Spanned<mir::Operand<'tcx>>],
        destination: mir::Place<'tcx>,
    ) -> Option<Fact<'tcx>> {
        let ty::FnDef(did, _) = *func.kind() else {
            return None;
        };
        if self.tcx.crate_name(did.krate).as_str() != "core" {
            return None;
        }
        // The path below is built to be matched against, and building it
        // allocates. The leaf settles the question first, since no contract
        // here is written on any other name.
        let leaf = self.tcx.def_key(did).disambiguated_data.data.get_opt_name();
        if !leaf.is_some_and(|name| {
            matches!(
                name.as_str(),
                "len"
                    | "max"
                    | "min"
                    | "integer_max"
                    | "integer_min"
                    | "ctlz"
                    | "ctlz_nonzero"
                    | "cttz"
                    | "cttz_nonzero"
                    | "ctpop"
                    | "new"
                    | "get"
            )
        }) {
            return None;
        }
        match SinkTable::def_path(self.tcx, did).as_str() {
            "slice::len" => {
                let of = self.root_slot(state, &args.first()?.node)?;
                Some(Folder::measuring(Value::Length(of)))
            }
            // Picking the larger or the smaller of two numbers is what
            // pins a value away from the end of its range. The pair is read
            // here rather than folded: the trait method compares through
            // references the walk does not follow, and the intrinsic the
            // primitive implementations lower to has no body at all. A
            // primitive cannot carry another crate's implementation of the
            // trait, so the body reached is the one this claim describes.
            "cmp::Ord::max" | "intrinsics::integer_max" => {
                self.chosen(state, true, args)
            }
            "cmp::Ord::min" | "intrinsics::integer_min" => {
                self.chosen(state, false, args)
            }
            // Counting the bits of a value, set or leading or trailing
            // zero, can never answer above the width of the type it was
            // read at, which is what clears the table every such count is
            // used to reach into.
            "intrinsics::ctlz"
            | "intrinsics::ctlz_nonzero"
            | "intrinsics::cttz"
            | "intrinsics::cttz_nonzero"
            | "intrinsics::ctpop" => {
                self.counted(args, destination).map(Fact::of)
            }
            // The wrapper holds a value exactly when that value is not
            // zero, and the option that carries it is `Some` for the same
            // reason, which is what folds the match written under every
            // `checked` operation the standard library builds this way.
            "num::nonzero::new" => self.wrapped(state, args, destination),
            "num::nonzero::get" => {
                let receiver = args.first()?;
                let source = self.ty_of(&receiver.node)?;
                if !self.is_nonzero(source) {
                    return None;
                }
                self.apart_from_zero(
                    destination.ty(&self.mir.local_decls, self.tcx).ty,
                )
                .map(Fact::of)
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
    /// across every callee one body reaches, which bounds the work. A
    /// callee already folded against the same claims, with as many calls
    /// left to read below it, is answered from the cache and costs nothing.
    fn folded(
        &mut self,
        state: &State<'tcx>,
        func: Ty<'tcx>,
        args: &[Spanned<mir::Operand<'tcx>>],
        destination: mir::Place<'tcx>,
        after: &mut State<'tcx>,
        cache: &mut Cache<'tcx>,
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
        let key = (callee, DEPTH.saturating_sub(folder.depth), entry);
        if let Some(known) = cache.get(&key) {
            let known = known.clone();
            self.handed_back(&known.returned, destination, after);
            return Found {
                left: known.left,
                quiet: known.quiet,
            };
        }
        let reach = folder.run(key.2.clone(), cache);
        self.budget = folder.budget;
        let summary = Summary {
            left: folder.returns.claim(),
            returned: std::mem::take(&mut folder.returned),
            quiet: self.silent(&folder, &reach),
        };
        self.handed_back(&summary.returned, destination, after);
        let found = Found {
            left: summary.left,
            quiet: summary.quiet,
        };
        // A walk cut short answered for the budget it had rather than for
        // the body, so it is not an answer another site can reuse.
        if folder.complete {
            cache.insert(key, summary);
        }
        found
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
    fn silent(&self, callee: &Folder<'_, 'tcx>, reach: &Reach) -> bool {
        for (bb, data) in callee.mir.basic_blocks.iter_enumerated() {
            if !reach.is_live(bb) {
                continue;
            }
            let Some(term) = &data.terminator else {
                return false;
            };
            let silent = match &term.kind {
                TerminatorKind::Assert { .. } => reach.is_settled(bb),
                // A call the walk read for these arguments and found
                // unable to raise leaves this body nothing to raise
                // either. The depth the reading is bounded by is what
                // stops the chain. An operation the compiler defines
                // rather than a body raises nothing at all.
                TerminatorKind::Call { func, .. } => {
                    reach.is_quiet(bb) || self.defined(callee, func)
                }
                // Dropping a value of a type with nothing to run is the
                // compiler writing down that the value ends here. The type
                // is read for the instantiation this call makes: a
                // parameter has drop glue for some arguments and none for
                // others, and only one of them is in front of us.
                TerminatorKind::Drop { place, .. } => callee
                    .ty_at(place)
                    .is_some_and(|ty| !ty.needs_drop(self.tcx, callee.env)),
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

    /// Whether a call runs an operation the compiler defines rather than a
    /// body of its own.
    ///
    /// Extraction adds nothing to the graph for such a call, for the same
    /// reason: it cannot call back into the program. What it does record is
    /// excluded here in the same terms, so the two halves agree: a panic
    /// entry point, a check on a type's validity, the barrier around a
    /// caught unwind, and the pair of bodies a const selection chooses
    /// between.
    fn defined(
        &self,
        callee: &Folder<'_, 'tcx>,
        func: &mir::Operand<'tcx>,
    ) -> bool {
        let Some(ty) = callee.ty_of(func) else {
            return false;
        };
        let ty::FnDef(did, generics) = *ty.kind() else {
            return false;
        };
        let Some(generics) = generics.no_bound_vars() else {
            return false;
        };
        let Ok(Some(inst)) =
            Instance::try_resolve(self.tcx, callee.env, did, generics)
        else {
            return false;
        };
        if !matches!(
            inst.def,
            ty::InstanceKind::Intrinsic(..)
                | ty::InstanceKind::LlvmIntrinsic(..)
        ) {
            return false;
        }
        let did = inst.def_id();
        if SinkTable::is_sink(self.tcx, did) {
            return false;
        }
        let name = self.tcx.item_name(did);
        ty::layout::ValidityRequirement::from_intrinsic(name).is_none()
            && !matches!(name.as_str(), "catch_unwind" | "const_eval_select")
    }

    /// The state a callee is entered with.
    ///
    /// A parameter is told only what the call site knows about the operand
    /// it was passed, and only where the claim means the same thing there:
    /// one written at another type describes a value the callee never sees.
    /// A claim that names another argument is rewritten to name the
    /// parameter that argument becomes, which is how `i < v.len()` reaches
    /// the bounds check inside the body that does the indexing.
    pub fn carried(
        &self,
        state: &State<'tcx>,
        callee: &Folder<'_, 'tcx>,
        args: &[Spanned<mir::Operand<'tcx>>],
    ) -> State<'tcx> {
        let mut entry = callee.blank();
        let carried: Vec<Carried<'tcx>> = args
            .iter()
            .enumerate()
            .map(|(index, arg)| self.about(state, callee, index, arg))
            .collect();
        for (index, held) in carried.iter().enumerate() {
            let local = mir::Local::from_usize(index.saturating_add(1));
            if callee.escapes(local) || !held.alike {
                continue;
            }
            let named = |of: mir::Local| {
                let at = carried
                    .iter()
                    .position(|other| other.alike && other.slot == Some(of))?;
                Some(mir::Local::from_usize(at.saturating_add(1)))
            };
            let mut order = Ranks::none_held();
            for (rel, of) in held.fact.order.each() {
                if let Some(there) = named(of) {
                    order.add(rel, there);
                }
            }
            let paired = held.fact.paired.and_then(named);
            let spans = held.fact.spans.and_then(named);
            let over = held
                .fact
                .over
                .and_then(|(of, step)| Some((named(of)?, step)));
            let fact = Fact {
                order,
                paired,
                over,
                spans,
                ..held.fact
            };
            if fact == Fact::default() {
                continue;
            }
            if let Some(slot) = entry.get_mut(local.as_usize()) {
                *slot = fact;
            }
        }
        Self::cut_alike(&carried, &mut entry);
        self.handed_over(state, callee, &carried, &mut entry);
        entry
    }

    /// Pairs the arguments that were cut to one length.
    ///
    /// The length itself is a local of the caller, so it cannot travel; the
    /// fact that two of the arguments share it can, and that is what the
    /// callee's own check between them reads.
    fn cut_alike(carried: &[Carried<'tcx>], entry: &mut State<'tcx>) {
        for (index, held) in carried.iter().enumerate() {
            let Some(cut) = held.fact.spans.filter(|_| held.alike) else {
                continue;
            };
            let Some(other) = carried.iter().enumerate().position(|(at, p)| {
                at != index && p.alike && p.fact.spans == Some(cut)
            }) else {
                continue;
            };
            let local = mir::Local::from_usize(index.saturating_add(1));
            let peer = mir::Local::from_usize(other.saturating_add(1));
            if let Some(slot) = entry.get_mut(local.as_usize()) {
                slot.paired = Some(peer);
            }
        }
    }

    /// Records in the caller what the parts of a returned structure hold.
    ///
    /// A field the callee filled is the same field where the caller reads
    /// it back, so the claim travels with the value rather than stopping at
    /// the call.
    fn handed_back(
        &self,
        returned: &[(Path, Fact<'tcx>)],
        destination: mir::Place<'tcx>,
        after: &mut State<'tcx>,
    ) {
        if !destination.projection.is_empty() {
            return;
        }
        for (path, fact) in returned {
            if *fact == Fact::default() || !path.portable() {
                continue;
            }
            let Some(slot) = self.places.at(path.rebased(destination.local))
            else {
                continue;
            };
            if self.escapes(slot) {
                continue;
            }
            put(after, slot, *fact);
        }
    }

    /// Carries what the caller knows about the parts of an argument into
    /// the places the callee reads them at.
    ///
    /// A value handed over inside a structure is still that value where the
    /// callee takes it out again: the `Ok` a conversion built carries the
    /// number it holds through the unwrapping below it.
    fn handed_over(
        &self,
        state: &State<'tcx>,
        callee: &Folder<'_, 'tcx>,
        carried: &[Carried<'tcx>],
        entry: &mut State<'tcx>,
    ) {
        for (slot, path) in callee.places.each() {
            if callee.escapes(slot) || !path.portable() {
                continue;
            }
            let Some(at) = path.base.as_usize().checked_sub(1) else {
                continue;
            };
            let Some(held) = carried.get(at).filter(|held| held.alike) else {
                continue;
            };
            let Some(mine) = held
                .base
                .and_then(|base| self.places.at(path.rebased(base)))
            else {
                continue;
            };
            let fact = Folder::abroad(Folder::known_at(state, mine));
            if fact == Fact::default() {
                continue;
            }
            put(entry, slot, fact);
        }
    }

    /// What one argument tells the parameter it becomes.
    fn about(
        &self,
        state: &State<'tcx>,
        callee: &Folder<'_, 'tcx>,
        index: usize,
        arg: &Spanned<mir::Operand<'tcx>>,
    ) -> Carried<'tcx> {
        let local = mir::Local::from_usize(index.saturating_add(1));
        let slot = self.root_slot(state, &arg.node);
        let param = callee
            .mir
            .local_decls
            .get(local)
            .and_then(|decl| callee.monomorphize(decl.ty));
        let passed = self.ty_of(&arg.node);
        let alike = param.is_some() && param == passed;
        let held = self.fact(state, &arg.node);
        let fact = Fact {
            value: held.value.and_then(portable).filter(|value| {
                // A claim written at another type describes another value.
                param == value.ty()
            }),
            same: None,
            ..held
        };
        let base = match &arg.node {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                place.projection.is_empty().then_some(place.local)
            }
            mir::Operand::Constant(_) | mir::Operand::RuntimeChecks(_) => None,
        };
        Carried {
            slot,
            base,
            alike,
            fact,
        }
    }

    /// The option a nonzero wrapper's constructor hands back.
    ///
    /// The constructor writes no branch of its own: the option is the value
    /// read at another type, and zero is the pattern that stands for
    /// `None`. A value the walk has proved nonzero therefore comes back as
    /// the variant that carries it.
    fn wrapped(
        &self,
        state: &State<'tcx>,
        args: &[Spanned<mir::Operand<'tcx>>],
        destination: mir::Place<'tcx>,
    ) -> Option<Fact<'tcx>> {
        let held = args.first()?;
        let ty = self.ty_of(&held.node)?;
        let zero = Known {
            bits: 0,
            ty,
            width: self.width(ty)?,
        };
        let apart = value::compare(
            mir::BinOp::Ne,
            self.fact(state, &held.node),
            Fact::of(Value::Exact(zero)),
        )?;
        if !apart {
            return None;
        }
        let out = self.ty_at(&destination)?;
        let ty::Adt(def, args) = out.kind() else {
            return None;
        };
        if self.tcx.get_diagnostic_item(sym::Option) != Some(def.did()) {
            return None;
        }
        // The variant that carries the wrapper is the one with a field.
        let (at, _) = def
            .variants()
            .iter_enumerated()
            .find(|(_, variant)| !variant.fields.is_empty())?;
        Some(Fact {
            tag: self.tag_of(def.did(), args, at),
            ..Fact::default()
        })
    }

    /// The range a count of bits lands in.
    ///
    /// The answer is a number of bits of the value counted, so it lies
    /// between none of them and all of them.
    fn counted(
        &self,
        args: &[Spanned<mir::Operand<'tcx>>],
        destination: mir::Place<'tcx>,
    ) -> Option<Value<'tcx>> {
        let counted = self.ty_of(&args.first()?.node)?;
        let bits = u128::from(self.width(counted)?);
        let ty = self.ty_at(&destination)?;
        let width = self.width(ty)?;
        let seed = Known { bits: 0, ty, width };
        Bounds::new(seed, Known { bits, ..seed }).map(Value::Within)
    }

    /// What picking one of two numbers leaves behind.
    ///
    /// The smaller of two is no larger than either, so an ordering against
    /// a slice length that either side carries is one the answer carries
    /// too, and a length itself bounds the answer from above. The larger
    /// keeps only what both sides agree on.
    fn chosen(
        &self,
        state: &State<'tcx>,
        larger: bool,
        args: &[Spanned<mir::Operand<'tcx>>],
    ) -> Option<Fact<'tcx>> {
        let fact = Fact {
            value: self.picked(state, larger, args),
            order: self.ranked(state, larger, args),
            ..Fact::default()
        };
        (fact != Fact::default()).then_some(fact)
    }

    /// The ordering against a slice length that picking one of two numbers
    /// keeps.
    fn ranked(
        &self,
        state: &State<'tcx>,
        larger: bool,
        args: &[Spanned<mir::Operand<'tcx>>],
    ) -> Ranks {
        let [left, right] = args else {
            return Ranks::none_held();
        };
        let bound = |operand: &mir::Operand<'tcx>| {
            let fact = self.fact(state, operand);
            match fact.value {
                Some(Value::Length(of)) => Ranks::of(LenRel::AT_MOST, of),
                _ => fact.order,
            }
        };
        let (left, right) = (bound(&left.node), bound(&right.node));
        if larger {
            return left.joined(right);
        }
        let mut both = left;
        for (rel, of) in right.each() {
            both.add(rel, of);
        }
        both
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
        args: &[Spanned<mir::Operand<'tcx>>],
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
    pub fn spread(
        &self,
        state: &State<'tcx>,
        operand: &mir::Operand<'tcx>,
    ) -> Option<Bounds<'tcx>> {
        let ty = self.ty_of(operand)?;
        let whole = self.whole(ty)?;
        // A length is read through the range that length was found to lie
        // in, so a guard on a slice bounds every number drawn from it.
        let Some(value) = value::sized(self.fact(state, operand)) else {
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

    /// Every value a type admits.
    ///
    /// A `char` and a `bool` hold fewer values than their width allows, and
    /// saying so is what settles the table lookup a code point is used for.
    pub fn whole(&self, ty: Ty<'tcx>) -> Option<Bounds<'tcx>> {
        let seed = Known {
            bits: 0,
            ty,
            width: self.width(ty)?,
        };
        let top = match ty.kind() {
            ty::Int(_) | ty::Uint(_) => seed.type_max(),
            ty::Char => Known {
                bits: u128::from(char::MAX as u32),
                ..seed
            },
            ty::Bool => Known { bits: 1, ..seed },
            _ => return None,
        };
        Bounds::new(seed.type_min(), top)
    }

    /// Whether a type is the standard library's nonzero wrapper.
    pub fn is_nonzero(&self, ty: Ty<'tcx>) -> bool {
        let ty::Adt(def, _) = ty.kind() else {
            return false;
        };
        self.tcx.get_diagnostic_item(sym::NonZero) == Some(def.did())
    }

    /// A value of an integer type that is known not to be zero.
    pub fn apart_from_zero(&self, ty: Ty<'tcx>) -> Option<Value<'tcx>> {
        let ty = self.monomorphize(ty)?;
        let width = self.width(ty)?;
        Some(Value::other_than(Known { bits: 0, ty, width }))
    }
}
