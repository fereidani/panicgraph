//! What the walk reads a body's values as.
//!
//! Every claim here is drawn from one statement or one call and says what a
//! local can hold at that point. The walk itself lives next door; this is
//! the half that answers what a value is, which is what decides whether a
//! check the compiler wrote can fail.

use std::cmp::Ordering::Less;

use rustc_middle::{
    mir::{self, BinOp},
    ty::{self, Ty, TypeVisitableExt},
};

use crate::{
    fold::Folder,
    state::{State, root_of},
    value::{self, Bounds, Fact, Known, LenRel, Ranks, Value, truncate},
};

impl<'tcx> Folder<'_, 'tcx> {
    /// Evaluates an rvalue against what the locals are known about.
    pub(crate) fn rvalue(
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
            // Unsizing an array gives a slice as long as the array's type
            // says it is, which is what settles the length checks written
            // against a fixed size buffer.
            mir::Rvalue::Cast(
                mir::CastKind::PointerCoercion(
                    ty::adjustment::PointerCoercion::Unsize,
                    _,
                ),
                operand,
                _,
            ) => return self.unsized_from(operand),
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
                return self
                    .length_of(state, operand)
                    .map_or_else(Fact::default, Self::measuring);
            }
            // A place has an address, so a pointer taken of one is never
            // null however the place was reached. Taking one of everything
            // another points at leaves a slice as long as that one was.
            mir::Rvalue::Ref(_, _, place)
            | mir::Rvalue::RawPtr(_, place)
            | mir::Rvalue::Reborrow(_, _, place) => {
                return Fact {
                    address: true,
                    ..self.reborrowed(state, place)
                };
            }
            // Reading the discriminant of an enum the walk has settled is
            // what folds the match below it.
            mir::Rvalue::Discriminant(place) => self.tag_read(state, place),
            mir::Rvalue::Aggregate(kind, fields) => match &**kind {
                mir::AggregateKind::Adt(did, variant, args, ..) => {
                    return Fact {
                        tag: self.tag_of(*did, args, *variant),
                        ..Fact::default()
                    };
                }
                // A fat pointer is built from a thin one and what it points
                // at, and for a slice that is how many elements it holds.
                mir::AggregateKind::RawPtr(..) => {
                    let Some(meta) = fields.iter().nth(1) else {
                        return Fact::default();
                    };
                    let held = self.fact(state, meta).value;
                    // A slice as long as the length of another is as long
                    // as that other, which is what settles the check a copy
                    // between the two writes.
                    let paired = match held {
                        Some(Value::Length(of)) => Some(of),
                        _ => None,
                    };
                    // A slice cut to a length is exactly that long, so
                    // one cut to the same length again is as long as it.
                    let spans = match meta {
                        mir::Operand::Copy(from) | mir::Operand::Move(from) => {
                            from.as_local().filter(|of| !self.escapes(*of))
                        }
                        _ => None,
                    };
                    return Fact {
                        extent: held.and_then(Value::bounds),
                        paired,
                        spans,
                        ..Fact::default()
                    };
                }
                _ => return Fact::default(),
            },
            _ => None,
        };
        Fact {
            value,
            ..Fact::default()
        }
    }

    /// How long a slice a reborrow of a whole pointee is.
    ///
    /// Taking a reference to everything a pointer points at leaves a slice
    /// as long as the one it was taken of, which is what carries the length
    /// of a subslice built from its parts to the call that reads it.
    pub(crate) fn reborrowed(
        &self,
        state: &State<'tcx>,
        place: &mir::Place<'tcx>,
    ) -> Fact<'tcx> {
        let blank = Fact::default();
        let [mir::ProjectionElem::Deref] = place.projection.as_slice() else {
            return blank;
        };
        if self.escapes(place.local) {
            return blank;
        }
        let Some(decl) = self.mir.local_decls.get(place.local) else {
            return blank;
        };
        let Some(ty) = self.monomorphize(decl.ty) else {
            return blank;
        };
        let (ty::Ref(_, inner, _) | ty::RawPtr(inner, _)) = ty.kind() else {
            return blank;
        };
        if !matches!(inner.kind(), ty::Slice(_) | ty::Str) {
            return blank;
        }
        let held = Self::known_at(state, place.local);
        Fact {
            extent: held.extent,
            // A reborrow of everything a pointer points at is as long as
            // the slice behind that pointer, which is the claim itself.
            paired: held.paired.or(Some(place.local)),
            spans: held.spans,
            ..blank
        }
    }

    /// How long the slice an array was unsized into is.
    ///
    /// The array states its own length, so the slice made of it is exactly
    /// that long wherever it is read, and a check comparing two such
    /// lengths is one the walk can settle.
    pub(crate) fn unsized_from(
        &self,
        operand: &mir::Operand<'tcx>,
    ) -> Fact<'tcx> {
        let Some(count) = self.array_length(operand) else {
            return Fact::default();
        };
        let ty = self.tcx.types.usize;
        let Some(width) = self.width(ty) else {
            return Fact::default();
        };
        let end = Known {
            bits: u128::from(count),
            ty,
            width,
        };
        Fact {
            extent: Bounds::new(end, end),
            address: true,
            ..Fact::default()
        }
    }

    /// How many elements the array behind a pointer holds.
    pub(crate) fn array_length(
        &self,
        operand: &mir::Operand<'tcx>,
    ) -> Option<u64> {
        let source =
            self.monomorphize(operand.ty(&self.mir.local_decls, self.tcx))?;
        let pointee = match source.kind() {
            ty::Ref(_, inner, _) | ty::RawPtr(inner, _) => *inner,
            _ => return None,
        };
        let ty::Array(_, count) = pointee.kind() else {
            return None;
        };
        count.try_to_target_usize(self.tcx)
    }

    /// Reads a value out at another type without changing its bits.
    ///
    /// An address and the value inside a nonzero wrapper both come out this
    /// way, and neither of them is zero.
    pub(crate) fn reinterpreted(
        &self,
        state: &State<'tcx>,
        operand: &mir::Operand<'tcx>,
        ty: Ty<'tcx>,
    ) -> Fact<'tcx> {
        let tag = self.niched(state, operand, ty);
        if self.fact(state, operand).address {
            return Fact {
                address: true,
                value: self.apart_from_zero(ty),
                tag,
                ..Fact::default()
            };
        }
        let value = self
            .monomorphize(operand.ty(&self.mir.local_decls, self.tcx))
            .filter(|source| self.is_nonzero(*source))
            .and_then(|_| self.apart_from_zero(ty));
        Fact {
            value,
            tag,
            ..Fact::default()
        }
    }

    /// The variant a value read at a niche encoded enum's own type holds.
    ///
    /// Such an enum carries no tag of its own: a variant with no fields is
    /// written as a value the payload could never take, so a payload the
    /// walk has ruled that value out for is the variant that carries one.
    /// It is what settles the match written under `NonZero::new`, and with
    /// it every check the standard library builds on one.
    ///
    /// Only an encoding with a single such value is read, which is what an
    /// option around a pointer or a nonzero number uses.
    pub(crate) fn niched(
        &self,
        state: &State<'tcx>,
        operand: &mir::Operand<'tcx>,
        ty: Ty<'tcx>,
    ) -> Option<u128> {
        let ty = self.monomorphize(ty)?;
        let ty::Adt(def, _) = ty.kind() else {
            return None;
        };
        if !def.is_enum() {
            return None;
        }
        let layout = self.tcx.layout_of(self.env.as_query_input(ty)).ok()?;
        let rustc_abi::Variants::Multiple {
            tag_encoding:
                rustc_abi::TagEncoding::Niche {
                    untagged_variant,
                    ref niche_variants,
                    niche_start,
                },
            ..
        } = layout.variants
        else {
            return None;
        };
        if niche_variants.start != niche_variants.last {
            return None;
        }
        let held = self.fact(state, operand);
        let apart = if held.address && niche_start == 0 {
            true
        } else {
            let source =
                self.monomorphize(operand.ty(&self.mir.local_decls, self.tcx))?;
            let width = self.width(source)?;
            value::compare(
                BinOp::Ne,
                held,
                Fact::of(Value::Exact(Known {
                    bits: truncate(niche_start, width),
                    ty: source,
                    width,
                })),
            )?
        };
        apart.then(|| {
            def.discriminant_for_variant(self.tcx, untagged_variant).val
        })
    }

    /// Applies a binary operator to what its operands are known about.
    pub(crate) fn operated(
        &self,
        state: &State<'tcx>,
        op: BinOp,
        pair: &(mir::Operand<'tcx>, mir::Operand<'tcx>),
    ) -> Fact<'tcx> {
        let left = self.fact(state, &pair.0);
        let right = self.fact(state, &pair.1);
        // A value and the same value raised by a constant compare by what
        // was added, which is what settles the order check a range index
        // writes over `at` and `at + 4`.
        if let Some(truth) = self.stepped(state, op, pair) {
            return Fact {
                value: self.boolean(truth).map(Value::Exact),
                ..Fact::default()
            };
        }
        let value = self.binary(state, op, pair, left, right);
        Fact {
            over: self.raised(state, op, pair, right, value),
            value,
            order: self.ordered(state, op, pair, left, right),
            ..Fact::default()
        }
    }

    /// How a value compares with the one it was reached from.
    fn stepped(
        &self,
        state: &State<'tcx>,
        op: BinOp,
        pair: &(mir::Operand<'tcx>, mir::Operand<'tcx>),
    ) -> Option<bool> {
        let root = |operand: &mir::Operand<'tcx>| match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                self.slot_of(place).map(|slot| root_of(state, slot))
            }
            _ => None,
        };
        if let (Some(near), Some((of, step))) =
            (root(&pair.0), self.fact(state, &pair.1).over)
            && of == near
        {
            return value::stepped(op, step);
        }
        let (far, (of, step)) =
            (root(&pair.1), self.fact(state, &pair.0).over?);
        (far? == of).then(|| value::stepped(value::mirrored(op), step))?
    }

    /// The link back to the value an addition was reached from.
    ///
    /// It is only recorded where the sum stayed inside its type, so the
    /// claim is the arithmetic one rather than what the machine wraps to.
    fn raised(
        &self,
        state: &State<'tcx>,
        op: BinOp,
        pair: &(mir::Operand<'tcx>, mir::Operand<'tcx>),
        right: Fact<'tcx>,
        value: Option<Value<'tcx>>,
    ) -> Option<(mir::Local, u128)> {
        if op != BinOp::Add || !matches!(value, Some(Value::Within(_))) {
            return None;
        }
        let step = right.value?.exact()?;
        if step.is_signed() {
            return None;
        }
        let (mir::Operand::Copy(place) | mir::Operand::Move(place)) = &pair.0
        else {
            return None;
        };
        Some((root_of(state, self.slot_of(place)?), step.bits))
    }

    /// How the result of an operator is ordered against a slice's length.
    ///
    /// The remainder of an unsigned value by a length lands below it, which
    /// is what the slice's own bounds check asks, and a length divided by
    /// anything is no larger than itself. Both divisors are above zero
    /// wherever this runs, since the check the compiler writes in front of
    /// them has passed to get here.
    pub(crate) fn ordered(
        &self,
        state: &State<'tcx>,
        op: BinOp,
        pair: &(mir::Operand<'tcx>, mir::Operand<'tcx>),
        left: Fact<'tcx>,
        right: Fact<'tcx>,
    ) -> Ranks {
        match op {
            BinOp::Rem => match right.value {
                Some(Value::Length(of)) if self.unsigned(&pair.0) => {
                    Ranks::of(LenRel::Below, of)
                }
                _ => Ranks::none_held(),
            },
            BinOp::Div => match left.value {
                Some(Value::Length(of)) if self.unsigned(&pair.1) => {
                    Ranks::of(LenRel::AtMost, of)
                }
                _ => Ranks::none_held(),
            },
            BinOp::Sub => self.shortened(state, pair, left, right),
            BinOp::Add => Self::lengthened(left, right),
            _ => Ranks::none_held(),
        }
    }

    /// How an addition leaves a value ordered against a slice's length.
    ///
    /// A value below a length is at most that length once one is added to
    /// it, which is what the read of everything past a byte asks. The sum
    /// cannot wrap: the length itself lies inside the type, so a value
    /// below it has room for one more.
    fn lengthened(left: Fact<'tcx>, right: Fact<'tcx>) -> Ranks {
        let mut ranks = Ranks::none_held();
        let Some(added) = right.value.and_then(Value::exact) else {
            return ranks;
        };
        if added.is_signed() {
            return ranks;
        }
        for (rel, of) in left.order.each() {
            match (rel, added.bits) {
                (held, 0) => ranks.add(held, of),
                (LenRel::Below, 1) => ranks.add(LenRel::AtMost, of),
                _ => {}
            }
        }
        ranks
    }

    /// How a subtraction leaves a value ordered against a slice's length.
    ///
    /// A value already measured against a length is still measured against
    /// it once a constant is taken off, and strictly below it once anything
    /// at all is. The value has to be at least what is taken off, or a
    /// build with the check turned off wraps it round to the top of the
    /// type instead of shortening it.
    pub(crate) fn shortened(
        &self,
        state: &State<'tcx>,
        pair: &(mir::Operand<'tcx>, mir::Operand<'tcx>),
        left: Fact<'tcx>,
        right: Fact<'tcx>,
    ) -> Ranks {
        let mut ranks = Ranks::none_held();
        let Some(taken) = right.value.and_then(Value::exact) else {
            return ranks;
        };
        let held = match (left.order.is_empty(), left.value) {
            (true, Some(Value::Length(of))) => Ranks::of(LenRel::AtMost, of),
            _ => left.order,
        };
        if taken.is_signed() || held.is_empty() {
            return ranks;
        }
        let under = self
            .spread(state, &pair.0)
            .and_then(|span| span.lo.order(taken))
            .is_none_or(|by| by == Less);
        if under {
            return ranks;
        }
        for (rel, of) in held.each() {
            ranks.add(if taken.bits == 0 { rel } else { LenRel::Below }, of);
        }
        ranks
    }

    /// Whether an operand is read as an unsigned integer.
    pub(crate) fn unsigned(&self, operand: &mir::Operand<'tcx>) -> bool {
        self.monomorphize(operand.ty(&self.mir.local_decls, self.tcx))
            .is_some_and(|ty| matches!(ty.kind(), ty::Uint(_)))
    }

    /// The value the discriminant of a settled place reads as.
    pub(crate) fn tag_read(
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
    pub fn tag_of(
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
    pub(crate) fn enum_at(&self, place: &mir::Place<'tcx>) -> Option<Ty<'tcx>> {
        let ty =
            self.monomorphize(place.ty(&self.mir.local_decls, self.tcx).ty)?;
        matches!(ty.kind(), ty::Adt(def, _) if def.is_enum()).then_some(ty)
    }

    /// The length a wide pointer carries, when the pointee is a slice.
    pub(crate) fn length_of(
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

    /// The claim a reading of a slice's length carries.
    ///
    /// A length is at most itself. Saying so outright is what lets a value
    /// that started as one keep an ordering where a loop's arms meet: the
    /// turn that walks back carries a bound, and the two agree on the
    /// weaker of them rather than on nothing.
    pub fn measuring(value: Value<'tcx>) -> Fact<'tcx> {
        let order = match value {
            Value::Length(of) => Ranks::of(LenRel::AtMost, of),
            _ => Ranks::none_held(),
        };
        Fact {
            order,
            ..Fact::of(value)
        }
    }

    /// Reads an operand, when its value is settled.
    pub(crate) fn exact(
        &self,
        state: &State<'tcx>,
        operand: &mir::Operand<'tcx>,
    ) -> Option<Known<'tcx>> {
        value::pinned(self.fact(state, operand))
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
            // A copy denotes what its source did, so what the source is
            // known about stands for the copy as well.
            Fact {
                value: own.value.or(at_root.value),
                order: if own.order.is_empty() {
                    at_root.order
                } else {
                    own.order
                },
                extent: own.extent.or(at_root.extent),
                paired: own.paired.or(at_root.paired),
                spans: own.spans.or(at_root.spans),
                address: own.address || at_root.address,
                ..own
            }
        });
        let Some(Value::Length(of)) = held.value else {
            return Self::ranged(state, held);
        };
        let behind = state.get(of.as_usize()).copied().unwrap_or_default();
        Fact {
            extent: behind.extent,
            paired: behind.paired,
            ..held
        }
    }

    /// The claim an ordering against a slice of known length amounts to.
    ///
    /// An index below a length that lies in a range lies in that range
    /// too, one short of its top. That is what carries a bound proved
    /// against one slice into a read of a second slice known to be as
    /// long.
    pub(crate) fn ranged(state: &State<'tcx>, held: Fact<'tcx>) -> Fact<'tcx> {
        let Some((rel, of)) = held.order.first() else {
            return held;
        };
        let Some(extent) = state.get(of.as_usize()).and_then(|s| s.extent)
        else {
            return held;
        };
        if extent.hi.is_signed() {
            return held;
        }
        let top = match rel {
            LenRel::Below => extent.hi.predecessor(),
            LenRel::AtMost => Some(extent.hi),
        };
        let Some(bound) = top.and_then(|hi| Bounds::new(extent.hi.zero(), hi))
        else {
            return held;
        };
        Fact {
            value: Some(held.value.map_or(Value::Within(bound), |known| {
                known.refined(Value::Within(bound))
            })),
            ..held
        }
    }

    /// Reads an operand for an assignment, recording where a copy of a
    /// plain local came from.
    ///
    /// The link is kept even when the value itself is known: a fact the
    /// source learns later still has to reach the checks that read the
    /// copy, and the link is how it travels.
    pub(crate) fn traced(
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
    pub(crate) fn constant(
        &self,
        konst: &mir::ConstOperand<'tcx>,
    ) -> Option<Known<'tcx>> {
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
    pub(crate) fn cast(
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
    pub(crate) fn preserved(
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
    pub(crate) fn converted(
        value: Known<'tcx>,
        ty: Ty<'tcx>,
        width: u32,
    ) -> Known<'tcx> {
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
    pub(crate) fn binary(
        &self,
        state: &State<'tcx>,
        op: BinOp,
        pair: &(mir::Operand<'tcx>, mir::Operand<'tcx>),
        left: Fact<'tcx>,
        right: Fact<'tcx>,
    ) -> Option<Value<'tcx>> {
        if let Some(truth) = value::compare(op, left, right) {
            return self.boolean(truth).map(Value::Exact);
        }
        // A value nothing is known about still lies inside its own type,
        // and that alone settles a check written against the end of it:
        // nothing unsigned is below zero, which is what a range index turns
        // into once its other end is proved.
        if let Some(truth) = self
            .spread(state, &pair.0)
            .zip(self.spread(state, &pair.1))
            .and_then(|(left, right)| value::spans_compare(op, left, right))
        {
            return self.boolean(truth).map(Value::Exact);
        }
        if let (Some(Value::Exact(l)), Some(Value::Exact(r))) =
            (left.value, right.value)
            && let Some(known) = Self::settled(op, l, r)
        {
            return Some(Value::Exact(known));
        }
        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul => Self::spanned(
                op,
                self.spread(state, &pair.0)?,
                self.spread(state, &pair.1)?,
            ),
            BinOp::Div | BinOp::Rem => self.split(state, op, pair),
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => {
                self.bitwise(state, op, pair)
            }
            BinOp::Shl
            | BinOp::ShlUnchecked
            | BinOp::Shr
            | BinOp::ShrUnchecked => self.shifted(state, op, pair, right),
            _ => None,
        }
    }

    /// The range a division or a remainder leaves behind.
    ///
    /// A remainder lies below its divisor and never above the value it was
    /// taken of, and a quotient moves with the value and against the
    /// divisor. Both are read as unsigned only: a signed remainder carries
    /// the sign of its left operand, and a signed division has a corner the
    /// type cannot hold. The divisor is above zero wherever this runs,
    /// since the check the compiler writes in front of it has passed to get
    /// here.
    pub(crate) fn split(
        &self,
        state: &State<'tcx>,
        op: BinOp,
        pair: &(mir::Operand<'tcx>, mir::Operand<'tcx>),
    ) -> Option<Value<'tcx>> {
        let left = self.spread(state, &pair.0)?;
        let right = self.spread(state, &pair.1)?;
        if left.lo.is_signed() || right.lo.is_signed() || right.lo.bits == 0 {
            return None;
        }
        let bounds = match op {
            BinOp::Div => Bounds::new(
                left.lo.quotient(right.hi)?,
                left.hi.quotient(right.lo)?,
            ),
            BinOp::Rem => Bounds::new(
                left.lo.zero(),
                left.hi.lesser(right.hi.predecessor()?)?,
            ),
            _ => return None,
        };
        bounds.map(Value::Within)
    }

    /// The range a bitwise operator leaves behind.
    ///
    /// An `and` keeps only the bits an operand already carried, so a side
    /// that is never negative bounds the result on its own. An `or` and an
    /// `xor` reach no higher than the topmost bit either side carries, and
    /// an `or` is never below the larger of the two, which is what keeps
    /// `d | 1` away from zero.
    pub(crate) fn bitwise(
        &self,
        state: &State<'tcx>,
        op: BinOp,
        pair: &(mir::Operand<'tcx>, mir::Operand<'tcx>),
    ) -> Option<Value<'tcx>> {
        let left = self.spread(state, &pair.0)?;
        let right = self.spread(state, &pair.1)?;
        if op == BinOp::BitAnd {
            let mut hi = None;
            for side in [left, right].iter().filter(|s| s.lo.nonnegative()) {
                hi = Some(match hi {
                    Some(held) => side.hi.lesser(held)?,
                    None => side.hi,
                });
            }
            return Bounds::new(left.lo.zero(), hi?).map(Value::Within);
        }
        if !left.lo.nonnegative() || !right.lo.nonnegative() {
            return None;
        }
        let hi = left.hi.greater(right.hi)?.saturated()?;
        let lo = if op == BinOp::BitOr {
            left.lo.greater(right.lo)?
        } else {
            left.lo.zero()
        };
        Bounds::new(lo, hi).map(Value::Within)
    }

    /// The range a shift by a settled amount leaves behind.
    ///
    /// The shift moves both ends of the range the same way, so what was an
    /// end of the value is an end of the result. Nothing is claimed unless
    /// the amount is settled: a shift the walk cannot read is a shift by
    /// anything.
    pub(crate) fn shifted(
        &self,
        state: &State<'tcx>,
        op: BinOp,
        pair: &(mir::Operand<'tcx>, mir::Operand<'tcx>),
        right: Fact<'tcx>,
    ) -> Option<Value<'tcx>> {
        let amount = right.value?.exact()?;
        if !amount.nonnegative() {
            return None;
        }
        let amount = u32::try_from(amount.bits).ok()?;
        let span = self.spread(state, &pair.0)?;
        Bounds::new(span.lo.shifted(op, amount)?, span.hi.shifted(op, amount)?)
            .map(Value::Within)
    }

    /// The range an arithmetic operator leaves behind.
    ///
    /// Each end is worked out as arithmetic rather than as the machine does
    /// it, and an end that would leave its type abandons the claim, so a
    /// result that wraps is never described by a range that cannot hold it.
    pub(crate) fn spanned(
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
    pub(crate) fn settled(
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
