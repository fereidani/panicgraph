//! The value domain the folder reasons in.
//!
//! Everything here is a claim about what a local can hold at one point, and
//! every claim is conservative: a value is only narrowed when the operation
//! that produced it guarantees the narrowing for every execution.

use rustc_middle::{
    mir,
    ty::{self, Ty},
};

/// A value the folder is certain of.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Known<'tcx> {
    /// The value, zero extended from the bit pattern of its type.
    pub bits: u128,
    /// The type it was read at, which decides how the bits compare.
    pub ty: Ty<'tcx>,
    /// The width of that type, in bits.
    pub width: u32,
}

impl Known<'_> {
    /// Whether the type reads its top bit as a sign.
    pub fn is_signed(self) -> bool {
        matches!(self.ty.kind(), ty::Int(_))
    }

    /// The value read as a signed integer.
    ///
    /// The bits are held zero extended, so the sign has to be put back by
    /// shifting the value up to the top of the word and down again.
    pub const fn as_signed(self) -> i128 {
        let Some(shift) = 128u32.checked_sub(self.width) else {
            return self.bits.cast_signed();
        };
        if shift == 0 || shift == 128 {
            return self.bits.cast_signed();
        }
        (self.bits << shift).cast_signed() >> shift
    }

    /// Whether the value is the one a branch treats as true.
    pub const fn truth(self) -> bool {
        self.bits != 0
    }

    /// How two values of the same type compare.
    pub fn order(self, other: Self) -> Option<std::cmp::Ordering> {
        if self.ty != other.ty || self.width != other.width {
            return None;
        }
        Some(if self.is_signed() {
            self.as_signed().cmp(&other.as_signed())
        } else {
            self.bits.cmp(&other.bits)
        })
    }

    /// The smallest value of this value's type.
    pub fn type_min(self) -> Self {
        let bits = if self.is_signed() {
            truncate(1u128 << (self.width.saturating_sub(1)), self.width)
        } else {
            0
        };
        Self { bits, ..self }
    }

    /// The largest value of this value's type.
    pub fn type_max(self) -> Self {
        let all = truncate(u128::MAX, self.width);
        let bits = if self.is_signed() { all >> 1 } else { all };
        Self { bits, ..self }
    }

    /// The next value down, when the type has one.
    pub fn predecessor(self) -> Option<Self> {
        if self == self.type_min() {
            return None;
        }
        Some(Self {
            bits: truncate(self.bits.wrapping_sub(1), self.width),
            ..self
        })
    }

    /// The next value up, when the type has one.
    pub fn successor(self) -> Option<Self> {
        if self == self.type_max() {
            return None;
        }
        Some(Self {
            bits: truncate(self.bits.wrapping_add(1), self.width),
            ..self
        })
    }

    /// The result of an arithmetic operator, when it lands inside the type.
    ///
    /// The answer is the arithmetic one. An operation that would leave the
    /// type has no answer here rather than the wrapped one, so a range built
    /// from these ends never describes a wraparound it cannot hold.
    pub fn arith(self, op: mir::BinOp, other: Self) -> Option<Self> {
        use mir::BinOp::{Add, Mul, Sub};
        if self.ty != other.ty || self.width != other.width {
            return None;
        }
        let bits = if self.is_signed() {
            let (left, right) = (self.as_signed(), other.as_signed());
            let value = match op {
                Add => left.checked_add(right)?,
                Sub => left.checked_sub(right)?,
                Mul => left.checked_mul(right)?,
                _ => return None,
            };
            if value < self.type_min().as_signed()
                || value > self.type_max().as_signed()
            {
                return None;
            }
            truncate(value.cast_unsigned(), self.width)
        } else {
            let value = match op {
                Add => self.bits.checked_add(other.bits)?,
                Sub => self.bits.checked_sub(other.bits)?,
                Mul => self.bits.checked_mul(other.bits)?,
                _ => return None,
            };
            if value > self.type_max().bits {
                return None;
            }
            value
        };
        Some(Self { bits, ..self })
    }

    /// The value shifted by a settled amount, when the shift means what the
    /// arithmetic says.
    ///
    /// Both directions are monotonic, so an end of a range shifted this way
    /// is still an end of the shifted range. A shift as wide as the type is
    /// refused: the machine masks the amount there and the arithmetic does
    /// not, and a claim drawn from the wrong one drops a panic that is real.
    /// Shifting left multiplies, so it is answered as a product and gives
    /// the claim up where the product leaves the type.
    pub fn shifted(self, op: mir::BinOp, amount: u32) -> Option<Self> {
        use mir::BinOp::{Shl, ShlUnchecked, Shr, ShrUnchecked};
        if amount >= self.width {
            return None;
        }
        match op {
            Shr | ShrUnchecked => {
                let bits = if self.is_signed() {
                    truncate(
                        (self.as_signed() >> amount).cast_unsigned(),
                        self.width,
                    )
                } else {
                    self.bits >> amount
                };
                Some(Self { bits, ..self })
            }
            Shl | ShlUnchecked => {
                let factor = Self {
                    bits: 1u128 << amount,
                    ..self
                };
                // A factor that reads as negative is the sign bit itself,
                // and multiplying by it reverses the order the ends rely on.
                if factor.is_signed() && factor.as_signed() < 0 {
                    return None;
                }
                self.arith(mir::BinOp::Mul, factor)
            }
            _ => None,
        }
    }

    /// The value with every bit below its highest one set as well.
    ///
    /// Setting or flipping the bits of two values never reaches above the
    /// highest bit either of them carries, so this is what bounds an `or`
    /// or an `xor` from above. A negative value has no such bound, since
    /// its top bit is the sign.
    pub fn saturated(self) -> Option<Self> {
        if self.is_signed() && self.as_signed() < 0 {
            return None;
        }
        let bits = self
            .bits
            .checked_ilog2()
            .map_or(0, |top| truncate(u128::MAX, top.saturating_add(1)));
        Some(Self { bits, ..self })
    }

    /// The quotient of two values the type reads as unsigned.
    ///
    /// Signed division has a corner the type cannot hold, so it is left to
    /// the check the compiler writes for it.
    pub fn quotient(self, other: Self) -> Option<Self> {
        if self.ty != other.ty || self.is_signed() || other.bits == 0 {
            return None;
        }
        Some(Self {
            bits: self.bits / other.bits,
            ..self
        })
    }

    /// The smaller of two values of the same type.
    pub fn lesser(self, other: Self) -> Option<Self> {
        Some(if self.order(other)? == std::cmp::Ordering::Greater {
            other
        } else {
            self
        })
    }

    /// The larger of two values of the same type.
    pub fn greater(self, other: Self) -> Option<Self> {
        Some(if self.order(other)? == std::cmp::Ordering::Greater {
            self
        } else {
            other
        })
    }

    /// Whether the value reads as zero or above.
    pub fn nonnegative(self) -> bool {
        !self.is_signed() || self.as_signed() >= 0
    }

    /// Zero, read at this value's type.
    pub const fn zero(self) -> Self {
        Self { bits: 0, ..self }
    }
}

/// A distance cut down to what a claim can count, which weakens the claim
/// rather than wronging it: less to spare is still to spare.
#[allow(
    clippy::cast_possible_truncation,
    reason = "the value is checked against the counter's range first"
)]
const fn clipped(by: u64) -> u32 {
    if by > u32::MAX as u64 {
        u32::MAX
    } else {
        by as u32
    }
}

/// How many quantities one value's ordering is kept against.
///
/// Two is what `min(a.len(), b.len())` leaves behind: the answer is inside
/// both slices, and a read of either has to find its own claim. A third
/// seat is for the plain value a guard measures against on top of those,
/// which is a length's own local as often as not.
const RANKS: usize = 3;

/// How a value is ordered against other quantities.
///
/// Each claim names a local. One holding a slice stands for the length of
/// that slice; any other stands for the number it holds, so a guard between
/// two values the walk cannot settle still orders the pair.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Ranks {
    held: [Option<(LenRel, mir::Local)>; RANKS],
}

impl Ranks {
    /// No claim at all, in a form a constant can be built from.
    pub const fn none_held() -> Self {
        Self {
            held: [None; RANKS],
        }
    }

    /// A single claim.
    pub fn of(rel: LenRel, of: mir::Local) -> Self {
        let mut ranks = Self::default();
        ranks.add(rel, of);
        ranks
    }

    /// Whether nothing is claimed at all.
    pub fn is_empty(self) -> bool {
        self.held.iter().all(Option::is_none)
    }

    /// The claim held against one slice.
    pub fn against(self, of: mir::Local) -> Option<LenRel> {
        self.held
            .iter()
            .flatten()
            .find(|(_, held)| *held == of)
            .map(|(rel, _)| *rel)
    }

    /// The first claim, for the readings that take one bound and no more.
    pub fn first(self) -> Option<(LenRel, mir::Local)> {
        self.held.iter().flatten().copied().next()
    }

    /// Every claim held.
    pub fn each(self) -> impl Iterator<Item = (LenRel, mir::Local)> {
        self.held.into_iter().flatten()
    }

    /// Records a claim, keeping the sharper one where the same slice is
    /// already named and dropping it where the table is full.
    pub fn add(&mut self, rel: LenRel, of: mir::Local) {
        for slot in &mut self.held {
            match slot {
                Some((held, named)) if *named == of => {
                    *held = held.sharper(rel);
                    return;
                }
                Some(_) => {}
                None => {
                    *slot = Some((rel, of));
                    return;
                }
            }
        }
    }

    /// Everything both sets of claims admit.
    pub fn joined(self, other: Self) -> Self {
        self.joined_with(other, false, false)
    }

    /// Everything both sets admit, where a side that can only be zero is
    /// at most every length there is.
    ///
    /// That is what carries a bound round a loop whose counter starts at
    /// nothing: the way in proves no ordering of its own, the way round
    /// proves one, and zero agrees with it.
    pub fn joined_with(self, other: Self, mine: bool, theirs: bool) -> Self {
        let mut ranks = Self::default();
        for (rel, of) in self.each() {
            if let Some(held) = other.against(of) {
                ranks.add(rel.weaker(held), of);
            } else if theirs {
                ranks.add(LenRel::AT_MOST, of);
            }
        }
        if mine {
            for (_, of) in other.each() {
                if self.against(of).is_none() {
                    ranks.add(LenRel::AT_MOST, of);
                }
            }
        }
        ranks
    }

    /// The claims widened away from the ones they replaced.
    ///
    /// A claim with less to spare than before is still shrinking, and a
    /// loop that takes a step off it on every turn would shrink it once
    /// per turn. It is pushed at once to the one claim an index check
    /// still reads, or to nothing to spare when even that has gone.
    pub fn widened(self, from: Self) -> Self {
        let mut ranks = Self::default();
        for (rel, of) in self.each() {
            let shrinking =
                from.against(of).is_some_and(|was| rel.short < was.short);
            let kept = if shrinking {
                LenRel {
                    short: rel.short.min(1),
                }
            } else {
                rel
            };
            ranks.add(kept, of);
        }
        ranks
    }

    /// Drops every claim measured against a local.
    pub fn forget(&mut self, local: mir::Local) {
        for slot in &mut self.held {
            if slot.is_some_and(|(_, of)| of == local) {
                *slot = None;
            }
        }
    }
}

/// How many values a widening step may stop at before it gives up.
///
/// Each one is a step an end of a range can take, so the table is capped:
/// what bounds the walk is that an end moves outward a fixed number of
/// times whatever the body looks like.
pub const STOPS: usize = 8;

/// The values a body compares against, in order.
///
/// A range pushed straight to the end of its type loses the bound a loop
/// was written to keep, so a widening step stops at what the body itself
/// names first.
pub struct Thresholds {
    steps: [u128; STOPS],
    held: usize,
}

impl Thresholds {
    /// An empty table, which widens straight to the end of the type.
    pub const fn none() -> Self {
        Self {
            steps: [0; STOPS],
            held: 0,
        }
    }

    /// Records a value the body compares against, keeping the table
    /// sorted and free of repeats.
    pub fn add(&mut self, value: u128) {
        let Some(held) = self
            .steps
            .get(..self.held)
            .filter(|held| self.held < STOPS && !held.contains(&value))
        else {
            return;
        };
        let at = held
            .iter()
            .position(|step| *step > value)
            .unwrap_or(self.held);
        self.steps.copy_within(at..self.held, at.saturating_add(1));
        if let Some(slot) = self.steps.get_mut(at) {
            *slot = value;
            self.held = self.held.saturating_add(1);
        }
    }

    /// The end a range's top is pushed out to.
    fn over<'tcx>(&self, end: Known<'tcx>) -> Known<'tcx> {
        let ceiling = end.type_max();
        if end.is_signed() {
            return ceiling;
        }
        for step in self.steps.get(..self.held).unwrap_or_default() {
            if *step >= end.bits && *step <= ceiling.bits {
                return Known { bits: *step, ..end };
            }
        }
        ceiling
    }

    /// The end a range's bottom is pushed out to.
    fn under<'tcx>(&self, end: Known<'tcx>) -> Known<'tcx> {
        let floor = end.type_min();
        if end.is_signed() {
            return floor;
        }
        for step in self.steps.get(..self.held).unwrap_or_default().iter().rev()
        {
            if *step <= end.bits {
                return Known { bits: *step, ..end };
            }
        }
        floor
    }
}

/// Masks a value to the width of its type.
pub const fn truncate(bits: u128, width: u32) -> u128 {
    match 1u128.checked_shl(width) {
        Some(above) => bits & above.wrapping_sub(1),
        None => bits,
    }
}

/// An inclusive range a value is known to lie in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Bounds<'tcx> {
    pub lo: Known<'tcx>,
    pub hi: Known<'tcx>,
}

impl<'tcx> Bounds<'tcx> {
    /// A range, when its ends are ordered.
    pub fn new(lo: Known<'tcx>, hi: Known<'tcx>) -> Option<Self> {
        (lo.order(hi)? != std::cmp::Ordering::Greater)
            .then_some(Self { lo, hi })
    }

    /// Whether a value lies inside the range.
    fn admits(self, value: Known<'tcx>) -> Option<bool> {
        let above = self.lo.order(value)? != std::cmp::Ordering::Greater;
        let below = value.order(self.hi)? != std::cmp::Ordering::Greater;
        Some(above && below)
    }

    /// The smallest range holding both.
    fn hull(self, other: Self) -> Option<Self> {
        Self::new(self.lo.lesser(other.lo)?, self.hi.greater(other.hi)?)
    }

    /// The part both ranges hold, when they meet at all.
    fn overlap(self, other: Self) -> Option<Self> {
        Self::new(self.lo.greater(other.lo)?, self.hi.lesser(other.hi)?)
    }

    /// The smallest range holding every value given.
    ///
    /// The corners of an arithmetic result are what this is read with, so
    /// the slice is a handful of values and the walk over it is as short.
    pub fn covering(values: &[Known<'tcx>]) -> Option<Self> {
        let (first, rest) = values.split_first()?;
        let mut span = Self {
            lo: *first,
            hi: *first,
        };
        for value in rest {
            span = span.hull(Self {
                lo: *value,
                hi: *value,
            })?;
        }
        Some(span)
    }
}

/// How a value is ordered against another quantity: the length of a slice,
/// or a number another local or place holds.
///
/// The value is at most the quantity less `short`. Nothing short is what a
/// range end check asks, and one short is what an index check asks, since
/// a value below the length is at most one short of it. A guard written
/// against the value raised by a constant leaves the constant here, which
/// is what carries `i + 16 <= len` down to `v[i + 3]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LenRel {
    pub short: u32,
}

impl LenRel {
    /// At most the length, which is what a range end check asks.
    pub const AT_MOST: Self = Self { short: 0 };
    /// Below the length, which is what an index check asks.
    pub const BELOW: Self = Self { short: 1 };

    /// Whether the value is strictly below the length.
    pub const fn is_below(self) -> bool {
        self.short >= 1
    }

    /// The claim that says more of the two.
    pub fn sharper(self, other: Self) -> Self {
        Self {
            short: self.short.max(other.short),
        }
    }

    /// The claim both agree on, which is what two arms leave behind.
    pub fn weaker(self, other: Self) -> Self {
        Self {
            short: self.short.min(other.short),
        }
    }

    /// The claim after the value is raised by a constant, when what was to
    /// spare covers it.
    pub fn raised(self, by: u64) -> Option<Self> {
        let by = u32::try_from(by).ok()?;
        self.short.checked_sub(by).map(|short| Self { short })
    }

    /// The claim after a constant is taken off the value, which leaves it
    /// that much further under the length. Saturating keeps the claim a
    /// weaker one rather than a wrong one, and so does cutting a constant
    /// down to what the counter holds.
    pub const fn lowered(self, by: u64) -> Self {
        Self {
            short: self.short.saturating_add(clipped(by)),
        }
    }
}

/// What a local is known about.
///
/// A branch teaches the arm it guards something its condition never states
/// outright: past `if rhs != 0`, the divisor is not zero, which is the fact
/// the division's own check is asking for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Value<'tcx> {
    /// Exactly this value.
    Exact(Known<'tcx>),
    /// Anything but this value.
    Other(Known<'tcx>),
    /// A value inside an inclusive range.
    Within(Bounds<'tcx>),
    /// The length of the slice behind another local.
    Length(mir::Local),
}

/// Everything known about one local.
///
/// The planes are deliberate. A loop's counter is an exact zero on the way
/// in and merely below the length on the way round, and holding both claims
/// lets the merge keep the ordering while it gives the constant up. The
/// link of sameness is a plane of its own for the same reason: a copy whose
/// value is already known still has to name its source, or a fact the
/// source learns later never reaches the checks that read the copy.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Fact<'tcx> {
    /// What the value is.
    pub value: Option<Value<'tcx>>,
    /// How the value is ordered against the lengths of the slices behind
    /// other locals.
    pub order: Ranks,
    /// The local this one was copied from, still unwritten since. The
    /// target never carries a link itself, so chains are one step long.
    pub same: Option<mir::Local>,
    /// How long the slice in play is.
    ///
    /// It is recorded against the local the slice is behind, so a guard
    /// that proves a slice not empty still says so at the next read of its
    /// length, which is a different local. A local holding a length is
    /// handed the claim recorded against that slice when it is read, so
    /// both describe the same quantity.
    pub extent: Option<Bounds<'tcx>>,
    /// Whether the value is an address, and so cannot be zero.
    ///
    /// A place has an address, and a reference is valid only when it holds
    /// one, so a pointer taken of either is never null. That is the claim a
    /// null check reads, and reading it is what clears the check written
    /// under every `NonNull::new`.
    pub address: bool,
    /// The tag the enum at this place carries, which is the value its
    /// discriminant reads as rather than the index of the variant.
    ///
    /// It is what makes a match fold: an option built as `Some` never takes
    /// the arm that panics, and the body holding that arm is then a body
    /// that raises nothing.
    pub tag: Option<u128>,
    /// The slice the one behind this local is as long as.
    ///
    /// A guard measuring two lengths against each other says nothing about
    /// either on its own and everything about the pair, so the claim is
    /// recorded against the slices rather than against the two locals that
    /// happened to hold their lengths. It is what settles the check a copy
    /// between two slices writes over them.
    pub paired: Option<mir::Local>,
    /// The local this value was reached from, and by how much.
    ///
    /// A range index compares its two ends against each other, and the far
    /// end is usually the near one with something added to it. The link is
    /// only recorded where the addition stays inside its type, so what it
    /// says is the arithmetic rather than what the machine wraps to.
    pub over: Option<(mir::Local, u128)>,
    /// The local holding how long the slice behind this one is.
    ///
    /// A slice cut to a length is exactly that long, so two cut to the same
    /// length are as long as each other however that length was worked out.
    pub spans: Option<mir::Local>,
}

impl<'tcx> Fact<'tcx> {
    /// A fact claiming nothing, in a form a constant can be built from.
    pub const fn blank() -> Self {
        Self {
            value: None,
            order: Ranks::none_held(),
            same: None,
            extent: None,
            address: false,
            tag: None,
            paired: None,
            spans: None,
            over: None,
        }
    }

    /// A fact holding just a value.
    pub const fn of(value: Value<'tcx>) -> Self {
        let mut fact = Self::blank();
        fact.value = Some(value);
        fact
    }

    /// Everything both facts admit.
    ///
    /// The two planes that hold a range are joined, so an arm that settles
    /// a local on one and bounds it on the other still leaves a range
    /// behind. The planes that name a local describe nothing when they name
    /// different ones, so those survive only by agreeing.
    pub fn joined(self, other: Self) -> Self {
        Self {
            // Two claims with nothing in common as they stand may still
            // agree once a length is read as the range it was found to lie
            // in, which is what a loop counting down from one leaves where
            // its arms meet.
            value: match (self.value, other.value) {
                (Some(held), Some(arriving)) => held
                    .join(arriving)
                    .or_else(|| sized(self)?.join(sized(other)?)),
                _ => None,
            },
            // Two arms that measure a value against the same slice meet at
            // the weaker of the two claims rather than at nothing, which is
            // what carries a bound round a loop whose first turn proved
            // more than the rest.
            order: self.order.joined_with(
                other.order,
                Self::zeroed(self),
                Self::zeroed(other),
            ),
            same: (self.same == other.same).then_some(self.same).flatten(),
            extent: match (self.extent, other.extent) {
                (Some(held), Some(arriving)) => held.hull(arriving),
                _ => None,
            },
            address: self.address && other.address,
            tag: (self.tag == other.tag).then_some(self.tag).flatten(),
            paired: (self.paired == other.paired)
                .then_some(self.paired)
                .flatten(),
            spans: (self.spans == other.spans).then_some(self.spans).flatten(),
            over: (self.over == other.over).then_some(self.over).flatten(),
        }
    }

    /// Whether the value can only be zero, which is at most every length.
    fn zeroed(self) -> bool {
        self.value
            .and_then(Value::bounds)
            .is_some_and(|span| !span.hi.is_signed() && span.hi.bits == 0)
    }

    /// The fact widened away from the one it replaced.
    ///
    /// Only an end that moved is pushed out. A claim that is the same on
    /// both sides has nothing to widen and stands as it is, whatever kind
    /// of claim it is: a length or a value ruled out has no range to push,
    /// and giving it up would lose a bound the loop never threatened.
    pub fn widened(self, from: Self, stops: &Thresholds) -> Self {
        Self {
            value: match (self.value, from.value) {
                (Some(now), Some(was)) if now == was => Some(now),
                (Some(now), Some(was)) => now.widened(was, stops),
                _ => None,
            },
            extent: match (self.extent, from.extent) {
                (Some(now), Some(was)) if now == was => Some(now),
                (Some(now), Some(was)) => Value::Within(now)
                    .widened(Value::Within(was), stops)
                    .and_then(Value::bounds),
                _ => None,
            },
            order: self.order.widened(from.order),
            ..self
        }
    }
}

/// A fact a comparison teaches, filed by the plane it lives in.
#[derive(Debug, Clone, Copy)]
pub enum Taught<'tcx> {
    /// A claim about the value itself.
    Value(Value<'tcx>),
    /// A claim about its order against a slice length.
    Order(LenRel, mir::Local),
    /// The slice measured is exactly as long as another.
    Alike(mir::Local),
    /// The value differs from the length of a slice, which sharpens an
    /// ordering already held against it.
    Apart(mir::Local),
}

impl<'tcx> Value<'tcx> {
    /// The value, when it is settled.
    pub const fn exact(self) -> Option<Known<'tcx>> {
        match self {
            Self::Exact(known) => Some(known),
            _ => None,
        }
    }

    /// Records that a value is anything but `known`.
    ///
    /// A `bool` has only two values, so ruling one out settles the other.
    pub fn other_than(known: Known<'tcx>) -> Self {
        if known.ty.is_bool() && known.bits <= 1 {
            return Self::Exact(Known {
                bits: 1 - known.bits,
                ..known
            });
        }
        Self::Other(known)
    }

    /// Whether forgetting `local` invalidates this claim.
    pub fn leans_on(self, local: mir::Local) -> bool {
        match self {
            Self::Exact(_) | Self::Other(_) | Self::Within(_) => false,
            Self::Length(other) => other == local,
        }
    }

    /// The type the claim is written at, when it names one.
    pub const fn ty(self) -> Option<Ty<'tcx>> {
        match self.anchor() {
            Some(known) => Some(known.ty),
            None => None,
        }
    }

    /// A value the claim names, read for the type it is written at.
    pub const fn anchor(self) -> Option<Known<'tcx>> {
        match self {
            Self::Exact(known) | Self::Other(known) => Some(known),
            Self::Within(bounds) => Some(bounds.lo),
            Self::Length(_) => None,
        }
    }

    /// The range the claim pins the value to, when it is one.
    pub const fn bounds(self) -> Option<Bounds<'tcx>> {
        match self {
            Self::Exact(known) => Some(Bounds {
                lo: known,
                hi: known,
            }),
            Self::Within(bounds) => Some(bounds),
            _ => None,
        }
    }

    /// Whether the claim admits a value.
    fn admits(self, value: Known<'tcx>) -> Option<bool> {
        use std::cmp::Ordering::Equal;
        match self {
            Self::Exact(known) => Some(known.order(value)? == Equal),
            Self::Other(ruled_out) => Some(ruled_out.order(value)? != Equal),
            Self::Within(bounds) => bounds.admits(value),
            Self::Length(_) => None,
        }
    }

    /// Everything either claim admits.
    ///
    /// This is what two arms of a branch leave behind where they meet: one
    /// that settles a divisor at one and bounds it below at the other still
    /// proves it nonzero, which is the whole point of reading the arms
    /// separately. `None` is the claim that admits everything, and a pair
    /// with no common description gives it.
    pub fn join(self, other: Self) -> Option<Self> {
        if self == other {
            return Some(self);
        }
        if let (Self::Other(ruled_out), rest) | (rest, Self::Other(ruled_out)) =
            (self, other)
        {
            // Ruling one value out still describes the pair, as long as the
            // other claim never admits it.
            return (!rest.admits(ruled_out)?)
                .then_some(Self::Other(ruled_out));
        }
        self.bounds()?.hull(other.bounds()?).map(Self::Within)
    }

    /// The claim widened away from the one it replaced.
    ///
    /// An end that moved is pushed outward at once rather than one
    /// iteration at a time, but only as far as the nearest value the body
    /// compares against: a counter a loop keeps below a constant settles
    /// at that constant instead of at everything its type admits. Where
    /// the body names no such value the end goes to the end of the type.
    /// Only a range widens; any other claim is given up instead.
    pub fn widened(self, from: Self, stops: &Thresholds) -> Option<Self> {
        let (now, was) = (self.bounds()?, from.bounds()?);
        let lo = if now.lo == was.lo {
            now.lo
        } else {
            stops.under(now.lo)
        };
        let hi = if now.hi == was.hi {
            now.hi
        } else {
            stops.over(now.hi)
        };
        Bounds::new(lo, hi).map(Self::Within)
    }

    /// The claim narrowed by one a branch taught.
    ///
    /// Only a narrowing that lies wholly inside the claim already held is
    /// taken, so a second bound on the same local adds to the first instead
    /// of replacing it. A pair with nothing in common would mean the arm
    /// never runs, which this pass does not claim, so what was held stands.
    pub fn refined(self, taught: Self) -> Self {
        self.narrowed(taught).unwrap_or(self)
    }

    /// The narrowing, when the claim taught is one.
    fn narrowed(self, taught: Self) -> Option<Self> {
        match (self, taught) {
            // A settled claim cannot be improved on.
            (Self::Exact(_) | Self::Length(_), _) => None,
            (_, Self::Exact(known)) => {
                self.admits(known)?.then_some(Self::Exact(known))
            }
            (Self::Other(ruled_out), Self::Within(bounds))
            | (Self::Within(bounds), Self::Other(ruled_out)) => {
                Self::without(bounds, ruled_out)
            }
            (Self::Within(held), Self::Within(bounds)) => {
                held.overlap(bounds).map(Self::Within)
            }
            (Self::Other(_) | Self::Within(_), _) => None,
        }
    }

    /// A range with one value taken off it, when it leaves a range.
    fn without(range: Bounds<'tcx>, ruled_out: Known<'tcx>) -> Option<Self> {
        if !range.admits(ruled_out)? {
            return Some(Self::Within(range));
        }
        if range.lo == ruled_out {
            return Bounds::new(ruled_out.successor()?, range.hi)
                .map(Self::Within);
        }
        if range.hi == ruled_out {
            return Bounds::new(range.lo, ruled_out.predecessor()?)
                .map(Self::Within);
        }
        None
    }
}

/// How a value compares with the same value plus a constant.
///
/// The step is never negative and the addition never wraps, so the answer
/// is the arithmetic one: a value is below itself raised by anything, and
/// never above it.
pub const fn stepped(op: mir::BinOp, step: u128) -> Option<bool> {
    use mir::BinOp::{Eq, Ge, Gt, Le, Lt, Ne};
    let same = step == 0;
    Some(match op {
        Eq | Ge => same,
        Ne | Lt => !same,
        Le => true,
        Gt => false,
        _ => return None,
    })
}

/// What a comparison measured a local against.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Against<'tcx> {
    /// A constant value.
    Constant(Known<'tcx>),
    /// A quantity measured against the length of the slice behind a local:
    /// the length itself, with nothing to spare, or a value already known
    /// to sit that far under it.
    Length(mir::Local, LenRel),
    /// The number read from a place or held by a local, named by the slot
    /// it is recorded at, and what that number has to spare under a third
    /// quantity when it is itself measured.
    ///
    /// A container keeps its length as a field rather than as a slice's
    /// metadata, so this is how a guard on `v.len()` reaches the check that
    /// reads the field again, and how a guard between two plain values
    /// reaches the check written between the ends of a range.
    Place(mir::Local, LenRel),
}

/// The comparison operator with its operands exchanged.
///
/// This is also what normalizes a comparison read backwards, constant
/// first.
pub const fn mirrored(op: mir::BinOp) -> mir::BinOp {
    use mir::BinOp::{Ge, Gt, Le, Lt};
    match op {
        Lt => Gt,
        Le => Ge,
        Gt => Lt,
        Ge => Le,
        other => other,
    }
}

/// The comparison operator whose truth is the negation of the given one.
pub const fn negated(op: mir::BinOp) -> mir::BinOp {
    use mir::BinOp::{Eq, Ge, Gt, Le, Lt, Ne};
    match op {
        Lt => Ge,
        Le => Gt,
        Gt => Le,
        Ge => Lt,
        Eq => Ne,
        Ne => Eq,
        other => other,
    }
}

/// What holding or failing a comparison proves about the measured local.
pub fn fact_of(
    op: mir::BinOp,
    against: Against<'_>,
    holds: bool,
) -> Option<Taught<'_>> {
    let op = if holds { op } else { negated(op) };
    match against {
        Against::Constant(k) => constant_fact(op, k).map(Taught::Value),
        Against::Length(of, under) => length_fact(op, of, true, under),
        Against::Place(of, under) => length_fact(op, of, false, under),
    }
}

/// The fact a comparison against a constant leaves behind.
fn constant_fact(op: mir::BinOp, k: Known<'_>) -> Option<Value<'_>> {
    use mir::BinOp::{Eq, Ge, Gt, Le, Lt, Ne};
    let bounds = |lo, hi| Bounds::new(lo, hi).map(Value::Within);
    match op {
        Eq => Some(Value::Exact(k)),
        Ne => Some(Value::other_than(k)),
        Lt => bounds(k.type_min(), k.predecessor()?),
        Le => bounds(k.type_min(), k),
        Gt => bounds(k.successor()?, k.type_max()),
        Ge => bounds(k, k.type_max()),
        _ => None,
    }
}

/// The fact a comparison against a slice length leaves behind.
///
/// Only the two orderings a bounds check can consume are kept. The rest say
/// something, but nothing this pass reads. `under` is what the quantity
/// compared against has to spare under the length itself, which the value
/// measured inherits: below a value with nothing to spare is one short of
/// the length. `measures` says whether the quantity is a slice's length.
/// The claims that pair two slices are only about lengths, so a quantity
/// named by the place it was read from carries the orderings and nothing
/// more.
const fn length_fact<'tcx>(
    op: mir::BinOp,
    of: mir::Local,
    measures: bool,
    under: LenRel,
) -> Option<Taught<'tcx>> {
    match op {
        mir::BinOp::Lt => Some(Taught::Order(under.lowered(1), of)),
        mir::BinOp::Le => Some(Taught::Order(under, of)),
        mir::BinOp::Eq if measures => Some(Taught::Alike(of)),
        mir::BinOp::Ne if measures => Some(Taught::Apart(of)),
        _ => None,
    }
}

/// Evaluates a comparison whose operands are only partly known.
///
/// `None` means the answer depends on the run. Everything here follows from
/// the claims alone, so an answer is only given when every execution agrees.
pub fn compare<'tcx>(
    op: mir::BinOp,
    left: Fact<'tcx>,
    right: Fact<'tcx>,
) -> Option<bool> {
    // An index the branch proved in range, compared against the length it
    // was measured by, read from each end in turn. Reading the second end
    // by exchanging the operands and calling back in would not terminate:
    // two lengths that each carry an ordering exchange them forever.
    if let Some(settled) = measured_against(op, left, right) {
        return Some(settled);
    }
    if let Some(settled) = measured_against(mirrored(op), right, left) {
        return Some(settled);
    }
    if let Some(settled) = alike(op, left, right) {
        return Some(settled);
    }
    values_compare(op, sized(left)?, sized(right)?)
}

/// What two lengths known to describe slices of one length prove.
///
/// The claim is recorded against the slices, so it reads the same way from
/// either side, and a slice is trivially as long as itself.
fn alike(op: mir::BinOp, left: Fact<'_>, right: Fact<'_>) -> Option<bool> {
    use mir::BinOp::{Eq, Ge, Gt, Le, Lt, Ne};
    let (Some(Value::Length(here)), Some(Value::Length(there))) =
        (left.value, right.value)
    else {
        return None;
    };
    // Two slices cut to one length, or as long as the same third, are as
    // long as each other.
    let together = (left.paired.is_some() && left.paired == right.paired)
        || (left.spans.is_some() && left.spans == right.spans);
    if here != there
        && !together
        && left.paired != Some(there)
        && right.paired != Some(here)
    {
        return None;
    }
    match op {
        Eq | Le | Ge => Some(true),
        Ne | Lt | Gt => Some(false),
        _ => None,
    }
}

/// What an index measured against a length proves about a comparison.
///
/// The measured value is on the left and the length it was measured by on
/// the right.
fn measured_against(
    op: mir::BinOp,
    left: Fact<'_>,
    right: Fact<'_>,
) -> Option<bool> {
    // The quantity on the right is named by the slice it measures and by
    // the place it was read from, and either name can carry the ordering,
    // so both are tried. A vector's length is both at once: the metadata of
    // the slice built from it, and a reading of the vector's own field.
    let named = |of| left.order.against(of);
    let measured = match right.value {
        Some(Value::Length(of)) => Some(of),
        _ => None,
    };
    // A slice as long as another is measured by the other's bounds too.
    let rel = measured
        .and_then(named)
        .or_else(|| right.same.and_then(named))
        .or_else(|| right.paired.and_then(named))?;
    ordered_by(op, rel)
}

/// What a value known to sit under another says about a comparison between
/// the two, read with the measured value on the left.
pub const fn ordered_by(op: mir::BinOp, rel: LenRel) -> Option<bool> {
    use mir::BinOp::{Ge, Gt, Le, Lt};
    match op {
        Le => Some(true),
        Gt => Some(false),
        Lt if rel.is_below() => Some(true),
        Ge if rel.is_below() => Some(false),
        _ => None,
    }
}

/// What a fact claims about its value, reading a length as the range that
/// length was found to lie in.
///
/// This is what a guard on emptiness leaves behind: the check that a slice
/// read is in range compares a constant against the length, and past
/// `if v.is_empty()` the length is known to be at least one.
pub const fn sized(fact: Fact<'_>) -> Option<Value<'_>> {
    match (fact.value, fact.extent) {
        (Some(Value::Length(_)), Some(bounds)) => Some(Value::Within(bounds)),
        (value, _) => value,
    }
}

/// What a fact settles a value to.
///
/// A length is read through the range that length was found to lie in, so
/// a slice made of a fixed size array answers a check on its length the
/// way a constant would.
pub fn pinned(fact: Fact<'_>) -> Option<Known<'_>> {
    match opened(sized(fact)?) {
        Value::Exact(known) => Some(known),
        _ => None,
    }
}

/// The claim read in the sharpest form it has.
///
/// Ruling out the end of a type leaves everything but that end, which is
/// what makes a value known apart from zero compare above it, and a range
/// with one value in it is that value.
fn opened(value: Value<'_>) -> Value<'_> {
    match value {
        Value::Other(ruled_out) => {
            Bounds::new(ruled_out.type_min(), ruled_out.type_max())
                .and_then(|whole| Value::without(whole, ruled_out))
                .unwrap_or(value)
        }
        Value::Within(bounds) if bounds.lo == bounds.hi => {
            Value::Exact(bounds.lo)
        }
        _ => value,
    }
}

/// Evaluates a comparison over the value plane alone.
fn values_compare<'tcx>(
    op: mir::BinOp,
    left: Value<'tcx>,
    right: Value<'tcx>,
) -> Option<bool> {
    use mir::BinOp::{Eq, Ne};
    match (opened(left), opened(right)) {
        (Value::Exact(a), Value::Exact(b)) => {
            range_compare(op, Bounds { lo: a, hi: a }, b)
        }
        // One side is known to differ from exactly the value the other side
        // holds, which answers an equality and nothing else.
        (Value::Exact(known), Value::Other(ruled_out))
        | (Value::Other(ruled_out), Value::Exact(known))
            if known == ruled_out =>
        {
            matches!(op, Eq | Ne).then_some(op == Ne)
        }
        (Value::Within(range), Value::Exact(k)) => range_compare(op, range, k),
        (Value::Exact(k), Value::Within(range)) => {
            range_compare(mirrored(op), range, k)
        }
        (Value::Within(a), Value::Within(b)) => spans_compare(op, a, b),
        _ => None,
    }
}

/// Evaluates a comparison between two ranges.
///
/// Equality is settled only by ranges that do not meet. Ranges that overlap
/// leave it open, because a range standing for a whole span says nothing
/// about which value inside it is held; the caller refines that where it
/// knows the range holds one value.
///
/// The mirrored operators recurse once and the mirror of a mirror is not
/// taken, so the depth is one.
pub fn spans_compare<'tcx>(
    op: mir::BinOp,
    a: Bounds<'tcx>,
    b: Bounds<'tcx>,
) -> Option<bool> {
    use std::cmp::Ordering::{Equal, Greater, Less};

    use mir::BinOp::{Eq, Ge, Gt, Le, Lt, Ne};
    match op {
        Lt => match a.hi.order(b.lo)? {
            Less => Some(true),
            _ => (a.lo.order(b.hi)? != Less).then_some(false),
        },
        Le => match a.hi.order(b.lo)? {
            Less | Equal => Some(true),
            Greater => (a.lo.order(b.hi)? == Greater).then_some(false),
        },
        Gt => spans_compare(Lt, b, a),
        Ge => spans_compare(Le, b, a),
        Eq | Ne => {
            let apart = a.hi.order(b.lo)? == Less || b.hi.order(a.lo)? == Less;
            apart.then_some(op == Ne)
        }
        _ => None,
    }
}

/// Evaluates a comparison inside a range against one settled end.
fn range_compare<'tcx>(
    op: mir::BinOp,
    range: Bounds<'tcx>,
    k: Known<'tcx>,
) -> Option<bool> {
    use mir::BinOp::{Eq, Ne};
    if let Some(settled) = spans_compare(op, range, Bounds { lo: k, hi: k }) {
        return Some(settled);
    }
    // The range meets the value, so equality is only settled when the range
    // holds nothing else.
    let single = range.lo == range.hi && range.lo == k;
    (single && matches!(op, Eq | Ne)).then_some(op == Eq)
}
