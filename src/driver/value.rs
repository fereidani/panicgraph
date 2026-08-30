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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
}

/// Masks a value to the width of its type.
pub const fn truncate(bits: u128, width: u32) -> u128 {
    match 1u128.checked_shl(width) {
        Some(above) => bits & above.wrapping_sub(1),
        None => bits,
    }
}

/// An inclusive range a value is known to lie in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
}

/// How a value relates to the length of a slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LenRel {
    /// Strictly less than the length, which is what an index check asks.
    Below,
    /// At most the length, which is what a range end check asks.
    AtMost,
}

/// What a local is known about.
///
/// A branch teaches the arm it guards something its condition never states
/// outright: past `if rhs != 0`, the divisor is not zero, which is the fact
/// the division's own check is asking for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Fact<'tcx> {
    /// What the value is.
    pub value: Option<Value<'tcx>>,
    /// How the value is ordered against the length of the slice behind
    /// another local.
    pub order: Option<(LenRel, mir::Local)>,
    /// The local this one was copied from, still unwritten since. The
    /// target never carries a link itself, so chains are one step long.
    pub same: Option<mir::Local>,
}

impl<'tcx> Fact<'tcx> {
    /// A fact holding just a value.
    pub const fn of(value: Value<'tcx>) -> Self {
        Self {
            value: Some(value),
            order: None,
            same: None,
        }
    }

    /// Keeps only what both facts agree on.
    pub fn agreed(self, other: Self) -> Self {
        Self {
            value: (self.value == other.value).then_some(self.value).flatten(),
            order: (self.order == other.order).then_some(self.order).flatten(),
            same: (self.same == other.same).then_some(self.same).flatten(),
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
}

/// What a comparison measured a local against.
#[derive(Debug, Clone, Copy)]
pub enum Against<'tcx> {
    /// A constant value.
    Constant(Known<'tcx>),
    /// The length of the slice behind a local.
    Length(mir::Local),
}

/// The comparison operator with its operands exchanged.
const fn mirrored(op: mir::BinOp) -> mir::BinOp {
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
const fn negated(op: mir::BinOp) -> mir::BinOp {
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

/// Normalizes a comparison read backwards, constant first.
pub const fn from_left(op: mir::BinOp) -> mir::BinOp {
    mirrored(op)
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
        Against::Length(of) => length_fact(op, of),
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
/// something, but nothing this pass reads.
const fn length_fact<'tcx>(
    op: mir::BinOp,
    of: mir::Local,
) -> Option<Taught<'tcx>> {
    match op {
        mir::BinOp::Lt => Some(Taught::Order(LenRel::Below, of)),
        mir::BinOp::Le => Some(Taught::Order(LenRel::AtMost, of)),
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
    use mir::BinOp::{Ge, Gt, Le, Lt};
    // An index the branch proved in range, compared against the length it
    // was measured by.
    if let (Some((rel, of)), Some(Value::Length(len))) =
        (left.order, right.value)
        && of == len
    {
        match (rel, op) {
            (LenRel::Below, Lt | Le) | (LenRel::AtMost, Le) => {
                return Some(true);
            }
            (LenRel::Below, Ge | Gt) | (LenRel::AtMost, Gt) => {
                return Some(false);
            }
            _ => {}
        }
    }
    if let (Some(Value::Length(_)), Some(_)) = (left.value, right.order) {
        return compare(mirrored(op), right, left);
    }
    values_compare(op, left.value?, right.value?)
}

/// Evaluates a comparison over the value plane alone.
fn values_compare<'tcx>(
    op: mir::BinOp,
    left: Value<'tcx>,
    right: Value<'tcx>,
) -> Option<bool> {
    use std::cmp::Ordering;

    use mir::BinOp::{Eq, Ge, Gt, Le, Lt, Ne};
    match (left, right) {
        (Value::Exact(a), Value::Exact(b)) => {
            let order = a.order(b)?;
            Some(match op {
                Eq => order == Ordering::Equal,
                Ne => order != Ordering::Equal,
                Lt => order == Ordering::Less,
                Le => order != Ordering::Greater,
                Gt => order == Ordering::Greater,
                Ge => order != Ordering::Less,
                _ => return None,
            })
        }
        // One side is known to differ from exactly the value the other side
        // holds, which answers an equality and nothing else.
        (Value::Exact(known), Value::Other(ruled_out))
        | (Value::Other(ruled_out), Value::Exact(known))
            if known == ruled_out =>
        {
            match op {
                Eq => Some(false),
                Ne => Some(true),
                _ => None,
            }
        }
        (Value::Within(range), Value::Exact(k)) => range_compare(op, range, k),
        (Value::Exact(k), Value::Within(range)) => {
            range_compare(mirrored(op), range, k)
        }
        (Value::Within(a), Value::Within(b)) => match op {
            Lt => match a.hi.order(b.lo)? {
                Ordering::Less => Some(true),
                _ => (a.lo.order(b.hi)? != Ordering::Less).then_some(false),
            },
            Gt => values_compare(Lt, Value::Within(b), Value::Within(a)),
            Le => match a.hi.order(b.lo)? {
                Ordering::Less | Ordering::Equal => Some(true),
                Ordering::Greater => {
                    (a.lo.order(b.hi)? == Ordering::Greater).then_some(false)
                }
            },
            Ge => values_compare(Le, Value::Within(b), Value::Within(a)),
            Eq | Ne => {
                let apart = a.hi.order(b.lo)? == Ordering::Less
                    || b.hi.order(a.lo)? == Ordering::Less;
                if !apart {
                    return None;
                }
                Some(op == Ne)
            }
            _ => None,
        },
        _ => None,
    }
}

/// Evaluates a comparison inside a range against one settled end.
fn range_compare<'tcx>(
    op: mir::BinOp,
    range: Bounds<'tcx>,
    k: Known<'tcx>,
) -> Option<bool> {
    use std::cmp::Ordering;

    use mir::BinOp::{Eq, Ge, Gt, Le, Lt, Ne};
    match op {
        Lt => match range.hi.order(k)? {
            Ordering::Less => Some(true),
            _ => (range.lo.order(k)? != Ordering::Less).then_some(false),
        },
        Le => match range.hi.order(k)? {
            Ordering::Less | Ordering::Equal => Some(true),
            Ordering::Greater => {
                (range.lo.order(k)? == Ordering::Greater).then_some(false)
            }
        },
        Gt => match range.lo.order(k)? {
            Ordering::Greater => Some(true),
            _ => (range.hi.order(k)? != Ordering::Greater).then_some(false),
        },
        Ge => match range.lo.order(k)? {
            Ordering::Greater | Ordering::Equal => Some(true),
            Ordering::Less => {
                (range.hi.order(k)? == Ordering::Less).then_some(false)
            }
        },
        Eq => {
            if range.admits(k)? {
                // The value could be anywhere in the range, so equality is
                // only settled when the range holds nothing else.
                (range.lo == range.hi && range.lo == k).then_some(true)
            } else {
                Some(false)
            }
        }
        Ne => {
            if range.admits(k)? {
                (range.lo == range.hi && range.lo == k).then_some(false)
            } else {
                Some(true)
            }
        }
        _ => None,
    }
}
