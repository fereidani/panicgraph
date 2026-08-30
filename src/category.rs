//! The panic taxonomy and the bitset used to propagate it.
//!
//! Every panic the analysis can observe is reduced to exactly one
//! [`Category`]. Categories are the unit of suppression: the user asks for a
//! set of categories to be assumed impossible, and the solver removes them
//! before propagation rather than filtering the finished report.

use std::{fmt, str::FromStr};

use serde::{Deserialize, Serialize};

/// How a panic terminates the process or unwinds the stack.
///
/// The distinction matters for suppression. Only an unwinding panic activates
/// the cleanup blocks of its caller, so an aborting sink cannot be the cause
/// of a downstream drop panic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Termination {
    /// Unwinds the stack, running drop glue on the way out.
    Unwind,
    /// Terminates the process without unwinding.
    Abort,
}

/// A kind of panic, as reported to the user.
///
/// The discriminants are stable because they index into [`CategorySet`].
#[derive(
    Debug,
    Clone,
    Copy,
    PartialEq,
    Eq,
    Hash,
    PartialOrd,
    Ord,
    Serialize,
    Deserialize,
)]
#[repr(u8)]
pub enum Category {
    /// Slice or array index out of bounds.
    Index = 0,
    /// Arithmetic overflow. Only present when overflow checks are enabled.
    Overflow = 1,
    /// Integer division by zero.
    DivideByZero = 2,
    /// Integer remainder by zero.
    RemainderByZero = 3,
    /// `Option::unwrap`, `Result::unwrap`, `expect`, and friends.
    Unwrap = 4,
    /// `panic!`, `assert!`, `unreachable!`, `todo!`, and friends.
    Explicit = 5,
    /// Slicing a `str` at a non-character boundary.
    StrBoundary = 6,
    /// A `RefCell` borrow conflict.
    Borrow = 7,
    /// A poisoned `Mutex` or `RwLock`.
    Poison = 8,
    /// A collection grew past the maximum representable capacity.
    CapacityOverflow = 9,
    /// The allocator could not satisfy a request.
    AllocFailure = 10,
    /// An `Rc` or `Arc` strong count overflowed.
    RefCountOverflow = 11,
    /// A panic raised from inside the formatting machinery.
    Fmt = 12,
    /// A null pointer was dereferenced.
    NullDeref = 13,
    /// A reference was constructed from a misaligned pointer.
    MisalignedRef = 14,
    /// A panic whose origin the analysis could not classify.
    Unknown = 15,
    /// A standard library precondition check, present only in a build that
    /// has undefined behaviour checks turned on.
    UbCheck = 16,
    /// A call into foreign code, which has no Rust body to read.
    Foreign = 17,
    /// A dynamic call, whose target set the analysis does not resolve.
    DynCall = 18,
    /// A call through a function pointer, whose target is unknown.
    FnPointer = 19,
    /// A call that resolves only once a caller supplies concrete generic
    /// arguments, so what it reaches is the caller's choice.
    GenericBound = 20,
}

/// Every category, in discriminant order.
pub const ALL: [Category; 21] = [
    Category::Index,
    Category::Overflow,
    Category::DivideByZero,
    Category::RemainderByZero,
    Category::Unwrap,
    Category::Explicit,
    Category::StrBoundary,
    Category::Borrow,
    Category::Poison,
    Category::CapacityOverflow,
    Category::AllocFailure,
    Category::RefCountOverflow,
    Category::Fmt,
    Category::NullDeref,
    Category::MisalignedRef,
    Category::Unknown,
    Category::UbCheck,
    Category::Foreign,
    Category::DynCall,
    Category::FnPointer,
    Category::GenericBound,
];

impl Category {
    /// The lowercase, hyphen-free name accepted on the command line.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Index => "index",
            Self::Overflow => "overflow",
            Self::DivideByZero => "divide-by-zero",
            Self::RemainderByZero => "remainder-by-zero",
            Self::Unwrap => "unwrap",
            Self::Explicit => "explicit",
            Self::StrBoundary => "str-boundary",
            Self::Borrow => "borrow",
            Self::Poison => "poison",
            Self::CapacityOverflow => "capacity-overflow",
            Self::AllocFailure => "alloc-failure",
            Self::RefCountOverflow => "refcount-overflow",
            Self::Fmt => "fmt",
            Self::NullDeref => "null-deref",
            Self::MisalignedRef => "misaligned-ref",
            Self::Unknown => "unknown",
            Self::UbCheck => "ub-check",
            Self::Foreign => "foreign",
            Self::DynCall => "dyn-call",
            Self::FnPointer => "fn-pointer",
            Self::GenericBound => "generic-bound",
        }
    }

    /// A one-line description, used by the `kinds` subcommand.
    #[must_use]
    pub const fn describe(self) -> &'static str {
        match self {
            Self::Index => "slice or array index out of bounds",
            Self::Overflow => "arithmetic overflow",
            Self::DivideByZero => "integer division by zero",
            Self::RemainderByZero => "integer remainder by zero",
            Self::Unwrap => "unwrap or expect on a None or Err value",
            Self::Explicit => "panic!, assert!, unreachable!, or todo!",
            Self::StrBoundary => "str sliced at a non-character boundary",
            Self::Borrow => "RefCell borrow conflict",
            Self::Poison => "poisoned Mutex or RwLock",
            Self::CapacityOverflow => "collection capacity overflow",
            Self::AllocFailure => "allocator could not satisfy a request",
            Self::RefCountOverflow => "Rc or Arc strong count overflow",
            Self::Fmt => "panic from the formatting machinery",
            Self::NullDeref => "null pointer dereference",
            Self::MisalignedRef => "reference from a misaligned pointer",
            Self::Unknown => "unclassified panic",
            Self::UbCheck => "standard library precondition check",
            Self::Foreign => "call into foreign code, which has no Rust body",
            Self::DynCall => "dyn trait call with an unresolved target set",
            Self::FnPointer => "call through a function pointer",
            Self::GenericBound => {
                "call decided by a caller's choice of generic arguments"
            }
        }
    }

    /// The bit this category occupies in a [`CategorySet`].
    #[must_use]
    pub const fn bit(self) -> u32 {
        1u32 << (self as u8)
    }
}

impl fmt::Display for Category {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

impl FromStr for Category {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        ALL.into_iter().find(|c| c.name() == s).ok_or(())
    }
}

/// A set of [`Category`] values, held as a bitset.
///
/// Propagating a set rather than a boolean is what makes suppression cheap:
/// the solver computes one set per function, and a filter is a mask test.
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize,
)]
pub struct CategorySet(u32);

impl CategorySet {
    /// The empty set.
    pub const EMPTY: Self = Self(0);

    /// The set of categories that describe an allocation failure.
    ///
    /// Suppressing these is the tool's headline feature: it means "assume
    /// every allocation succeeds", which is the counterfactual most callers
    /// actually want when auditing for interesting panics.
    ///
    /// `RefCountOverflow` is deliberately excluded. An `Rc` count overflow is
    /// an invariant failure, not allocator exhaustion.
    #[must_use]
    pub const fn oom() -> Self {
        Self(Category::CapacityOverflow.bit() | Category::AllocFailure.bit())
    }

    /// The categories suppressed unless the user asks otherwise.
    ///
    /// Allocation failures are hidden because every growable collection
    /// reaches them. Precondition checks are hidden because a build that
    /// leaves them on is a debug build, and a report about one describes
    /// something the user is not shipping.
    #[must_use]
    pub const fn default_suppressed() -> Self {
        Self(Self::oom().0 | Category::UbCheck.bit())
    }

    /// The categories that stand for code the analysis could not read.
    ///
    /// None of them names a panic. Each says where visibility ended: an
    /// unreadable body, foreign code, a dynamic or pointer call, or a
    /// generic argument a caller has yet to choose.
    #[must_use]
    pub const fn assumed() -> Self {
        Self(
            Category::Unknown.bit()
                | Category::Foreign.bit()
                | Category::DynCall.bit()
                | Category::FnPointer.bit()
                | Category::GenericBound.bit(),
        )
    }

    /// A set holding exactly one category.
    #[must_use]
    pub const fn single(c: Category) -> Self {
        Self(c.bit())
    }

    /// Adds a category to the set.
    pub const fn insert(&mut self, c: Category) {
        self.0 |= c.bit();
    }

    /// Returns whether the category is a member.
    #[must_use]
    pub const fn contains(self, c: Category) -> bool {
        self.0 & c.bit() != 0
    }

    /// Returns whether the set holds no categories.
    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// Returns the union of two sets.
    #[must_use]
    pub const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    /// Returns the categories in `self` that are absent from `other`.
    #[must_use]
    pub const fn difference(self, other: Self) -> Self {
        Self(self.0 & !other.0)
    }

    /// Returns the categories present in both sets.
    #[must_use]
    pub const fn intersection(self, other: Self) -> Self {
        Self(self.0 & other.0)
    }

    /// Returns whether `self` holds every category in `other`.
    #[must_use]
    pub const fn contains_all(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    /// Returns the number of categories in the set.
    #[must_use]
    pub const fn len(self) -> u32 {
        self.0.count_ones()
    }

    /// Iterates the categories in discriminant order.
    pub fn iter(self) -> impl Iterator<Item = Category> {
        ALL.into_iter().filter(move |c| self.contains(*c))
    }
}

impl FromIterator<Category> for CategorySet {
    fn from_iter<I: IntoIterator<Item = Category>>(iter: I) -> Self {
        let mut set = Self::EMPTY;
        for c in iter {
            set.insert(c);
        }
        set
    }
}

impl fmt::Display for CategorySet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, c) in self.iter().enumerate() {
            if i > 0 {
                f.write_str(", ")?;
            }
            write!(f, "{c}")?;
        }
        Ok(())
    }
}

/// Resolves a comma-separated selector into a category set.
///
/// Accepts individual category names plus the group aliases `oom` and `all`.
///
/// # Errors
///
/// Returns the offending token if it names neither a category nor a group.
pub fn parse_selector(s: &str) -> Result<CategorySet, String> {
    let mut set = CategorySet::EMPTY;
    for tok in s.split(',').map(str::trim).filter(|t| !t.is_empty()) {
        match tok {
            "oom" => set = set.union(CategorySet::oom()),
            "assumed" => set = set.union(CategorySet::assumed()),
            "default" => {
                set = set.union(CategorySet::default_suppressed());
            }
            "all" => set = ALL.into_iter().collect(),
            other => match other.parse::<Category>() {
                Ok(c) => set.insert(c),
                Err(()) => return Err(other.to_owned()),
            },
        }
    }
    Ok(set)
}
