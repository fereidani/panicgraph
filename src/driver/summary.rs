//! What the walk finds a call does.
//!
//! A call is the edge of what one body says. Reading the callee is what
//! carries a value across it, and what shows that a check the callee makes
//! cannot fail for the arguments this call site hands it. A contract
//! answers first where one holds for every implementation the resolution
//! can reach, since it costs nothing to read.

use rustc_middle::{
    mir::{self, TerminatorKind},
    ty::{self, Instance, Ty, TypeVisitableExt, TypingEnv},
};

use crate::{
    fold::{Folder, Reach},
    sinks::SinkTable,
    state::{State, root_of},
    value::{Bounds, Fact, Known, Value},
};

/// How far a chain of calls is followed for the value it returns.
///
/// Each step is one more body on the stack, and the calls worth reading a
/// value out of sit shallow: `cmp::max` is one step above `Ord::max`, which
/// is the deepest of them.
pub const DEPTH: u32 = 3;

/// How many blocks folding one body may spend on the callees it reads
/// values out of.
///
/// A summary is only asked for where the answer would settle a check, so
/// the budget is rarely touched. It is what keeps a body that calls into a
/// wide subgraph from paying for all of it.
pub const BUDGET: u32 = 4096;

/// What every path out of a body was found to return.
#[derive(Debug, Clone, Copy)]
pub enum Returns<'tcx> {
    /// No path that returns has been walked.
    Never,
    /// Every such path leaves a value this claim admits.
    Held(Value<'tcx>),
    /// Nothing definite.
    Anything,
}

impl<'tcx> Returns<'tcx> {
    /// Adds what one path out of the body leaves behind.
    pub fn met(self, value: Option<Value<'tcx>>) -> Self {
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
    pub const fn claim(self) -> Option<Value<'tcx>> {
        match self {
            Self::Held(value) => Some(value),
            Self::Never | Self::Anything => None,
        }
    }
}

/// What folding a callee at one call site found.
#[derive(Debug, Clone, Copy, Default)]
pub struct Found<'tcx> {
    /// The value every path out of the callee leaves behind.
    pub value: Option<Value<'tcx>>,
    /// Whether the callee, walked with these arguments, can still raise.
    pub quiet: bool,
}

/// What one argument of a call tells the parameter it becomes.
struct Carried<'tcx> {
    /// Where the argument's claims live in the caller, so a claim naming it
    /// can be rewritten to name the parameter.
    slot: Option<mir::Local>,
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
            let fact = self.fact(state, &arg.node);
            fact.tag.is_some()
                || fact.extent.is_some()
                || fact.value.and_then(portable).is_some()
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
                Some(Value::Length(root_of(state, self.slot_of(place)?)))
            }
            // Picking the larger or the smaller of two numbers is what
            // pins a value away from the end of its range, and the two are
            // read here rather than folded because the body compares
            // through references the walk does not follow. A primitive
            // cannot carry another crate's implementation of the trait, so
            // the body reached is the one this claim describes.
            "cmp::Ord::max" => self.picked(state, true, args),
            "cmp::Ord::min" => self.picked(state, false, args),
            // Counting the bits of a value, set or leading or trailing
            // zero, can never answer above the width of the type it was
            // read at, which is what clears the table every such count is
            // used to reach into.
            "intrinsics::ctlz"
            | "intrinsics::ctlz_nonzero"
            | "intrinsics::cttz"
            | "intrinsics::cttz_nonzero"
            | "intrinsics::ctpop" => self.counted(args, destination),
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
    /// A claim that names another argument is rewritten to name the
    /// parameter that argument becomes, which is how `i < v.len()` reaches
    /// the bounds check inside the body that does the indexing.
    pub fn carried(
        &self,
        state: &State<'tcx>,
        callee: &Folder<'_, 'tcx>,
        args: &[rustc_span::Spanned<mir::Operand<'tcx>>],
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
            let order = held.fact.order.and_then(|(rel, of)| {
                let at = carried
                    .iter()
                    .position(|other| other.alike && other.slot == Some(of))?;
                Some((rel, mir::Local::from_usize(at.saturating_add(1))))
            });
            let fact = Fact { order, ..held.fact };
            if fact == Fact::default() {
                continue;
            }
            if let Some(slot) = entry.get_mut(local.as_usize()) {
                *slot = fact;
            }
        }
        entry
    }

    /// What one argument tells the parameter it becomes.
    fn about(
        &self,
        state: &State<'tcx>,
        callee: &Folder<'_, 'tcx>,
        index: usize,
        arg: &rustc_span::Spanned<mir::Operand<'tcx>>,
    ) -> Carried<'tcx> {
        let local = mir::Local::from_usize(index.saturating_add(1));
        let slot = match &arg.node {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                self.slot_of(place).map(|slot| root_of(state, slot))
            }
            _ => None,
        };
        let param = callee
            .mir
            .local_decls
            .get(local)
            .and_then(|decl| callee.monomorphize(decl.ty));
        let passed =
            self.monomorphize(arg.node.ty(&self.mir.local_decls, self.tcx));
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
        Carried { slot, alike, fact }
    }

    /// The range a count of bits lands in.
    ///
    /// The answer is a number of bits of the value counted, so it lies
    /// between none of them and all of them.
    fn counted(
        &self,
        args: &[rustc_span::Spanned<mir::Operand<'tcx>>],
        destination: mir::Place<'tcx>,
    ) -> Option<Value<'tcx>> {
        let counted = self.monomorphize(
            args.first()?.node.ty(&self.mir.local_decls, self.tcx),
        )?;
        let bits = u128::from(self.width(counted)?);
        let ty = self
            .monomorphize(destination.ty(&self.mir.local_decls, self.tcx).ty)?;
        let width = self.width(ty)?;
        let seed = Known { bits: 0, ty, width };
        Bounds::new(seed, Known { bits, ..seed }).map(Value::Within)
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
    pub fn spread(
        &self,
        state: &State<'tcx>,
        operand: &mir::Operand<'tcx>,
    ) -> Option<Bounds<'tcx>> {
        let ty =
            self.monomorphize(operand.ty(&self.mir.local_decls, self.tcx))?;
        let whole = self.whole(ty)?;
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

    /// Every value a type admits.
    pub fn whole(&self, ty: Ty<'tcx>) -> Option<Bounds<'tcx>> {
        if !matches!(ty.kind(), ty::Int(_) | ty::Uint(_)) {
            return None;
        }
        let seed = Known {
            bits: 0,
            ty,
            width: self.width(ty)?,
        };
        Bounds::new(seed.type_min(), seed.type_max())
    }

    /// Whether a type is the standard library's nonzero wrapper.
    pub fn is_nonzero(&self, ty: Ty<'tcx>) -> bool {
        let ty::Adt(def, _) = ty.kind() else {
            return false;
        };
        self.tcx.get_diagnostic_item(rustc_span::sym::NonZero)
            == Some(def.did())
    }

    /// A value of an integer type that is known not to be zero.
    pub fn apart_from_zero(&self, ty: Ty<'tcx>) -> Option<Value<'tcx>> {
        let ty = self.monomorphize(ty)?;
        let width = self.width(ty)?;
        Some(Value::other_than(Known { bits: 0, ty, width }))
    }
}
