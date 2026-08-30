//! The data model the driver emits and the solver consumes.
//!
//! One [`Artifact`] is produced per compiled crate. The command line tool
//! merges every artifact of a build into a single [`Graph`](crate::Graph).

use std::fmt;

use serde::{Deserialize, Serialize};

use crate::category::{Category, Termination};

/// A source position.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Loc {
    /// Path to the source file, as recorded by the compiler.
    pub file: String,
    /// One-based line number.
    pub line: u32,
    /// One-based column number.
    pub col: u32,
}

impl fmt::Display for Loc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}:{}", self.file, self.line, self.col)
    }
}

/// A globally unique identifier for one monomorphized function.
///
/// This is the compiler's symbol name, which stays unique across crates and
/// across instantiations of the same generic function.
#[derive(
    Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize,
)]
pub struct FuncKey(pub String);

impl fmt::Display for FuncKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// How confident the analysis is that a call edge is real.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum EdgeKind {
    /// A statically resolved call. The callee is exact.
    Static,
    /// Drop glue, entered through a `Drop` terminator.
    Drop,
    /// A `dyn Trait` call resolved through a vtable candidate.
    Vtable,
    /// A call through a function pointer, resolved by signature.
    FnPtr,
    /// A call whose target the analysis could not determine.
    Unresolved,
}

impl EdgeKind {
    /// Returns whether the edge is exact rather than a candidate.
    #[must_use]
    pub const fn is_exact(self) -> bool {
        matches!(self, Self::Static | Self::Drop)
    }

    /// The name used in reports.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Static => "static",
            Self::Drop => "drop",
            Self::Vtable => "vtable",
            Self::FnPtr => "fn-ptr",
            Self::Unresolved => "unresolved",
        }
    }
}

/// Why a cleanup block is reachable.
///
/// Cleanup blocks run while a panic unwinds. They are only reachable if the
/// panic that triggers them can actually happen, so suppressing that panic
/// must also suppress everything reachable only through its cleanup path.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum UnwindOrigin {
    /// Reached by the unwind edge of a panic raised in this body. The index
    /// selects a member of [`Body::sites`].
    Site(u32),
    /// Reached by the unwind edge of a call in this body, and therefore live
    /// only if that callee can itself unwind. The index selects a member of
    /// [`Body::calls`].
    Call(u32),
}

/// The condition under which a site or call is reachable.
///
/// Computed once by the driver, and evaluated cheaply for each suppression
/// policy. A guard with `normal` set is always reachable; otherwise it is
/// reachable only while one of its unwind origins is live.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Guard {
    /// Reachable without any panic occurring first.
    pub normal: bool,
    /// Unwind paths that also reach this point.
    pub origins: Vec<UnwindOrigin>,
}

impl Guard {
    /// A guard for a point on the ordinary control flow path.
    #[must_use]
    pub const fn always() -> Self {
        Self {
            normal: true,
            origins: Vec::new(),
        }
    }

    /// Returns whether the guard can never be satisfied.
    #[must_use]
    pub const fn is_dead(&self) -> bool {
        !self.normal && self.origins.is_empty()
    }
}

/// A panic raised directly by a function body.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PanicSite {
    /// What kind of panic this is.
    pub category: Category,
    /// Whether it unwinds or aborts.
    pub termination: Termination,
    /// The compiler's message, where one exists.
    pub reason: String,
    /// The panic entry point that was called, for sites that are calls.
    pub sink: Option<String>,
    /// Where the panic is written.
    pub loc: Option<Loc>,
    /// When this site is reachable.
    pub guard: Guard,
}

/// A call from one function to another.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CallSite {
    /// The resolved callee, absent when the target is unknown.
    pub callee: Option<FuncKey>,
    /// A readable name for the callee, used in reports.
    pub callee_display: String,
    /// How the target was resolved.
    pub kind: EdgeKind,
    /// Where the call is written.
    pub loc: Option<Loc>,
    /// When this call is reachable.
    pub guard: Guard,
}

/// Everything the solver needs to know about one function.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Body {
    /// The function's unique key.
    pub key: FuncKey,
    /// A readable path, for example `mycrate::parse`.
    pub display: String,
    /// The crate the function was defined in.
    pub krate: String,
    /// Where the function is defined.
    pub loc: Option<Loc>,
    /// Panics raised directly by this body.
    pub sites: Vec<PanicSite>,
    /// Calls made by this body.
    pub calls: Vec<CallSite>,
    /// True when the compiler had no MIR for this function, so its behaviour
    /// is unknown rather than known to be panic free.
    pub opaque: bool,
    /// True when the function is foreign, so there is no Rust body to read
    /// and never will be. Reported apart from an opaque Rust function,
    /// which a fuller standard library would have shown.
    #[serde(default)]
    pub foreign: bool,
    /// True when the function is defined in the crate under analysis.
    pub local: bool,
}

impl Body {
    /// The category a body the analysis could not read raises.
    ///
    /// Foreign code is named apart from an opaque Rust function: it has no
    /// Rust body to read and no fuller standard library would produce one.
    #[must_use]
    pub const fn unreadable(&self) -> Category {
        if self.foreign {
            Category::Foreign
        } else {
            Category::Unknown
        }
    }

    /// Creates an opaque record for a function whose MIR was unavailable.
    #[must_use]
    pub const fn opaque(key: FuncKey, display: String, krate: String) -> Self {
        Self {
            key,
            display,
            krate,
            loc: None,
            sites: Vec::new(),
            calls: Vec::new(),
            opaque: true,
            foreign: false,
            local: false,
        }
    }
}

/// How the standard library was made available to the analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum StdMode {
    /// The precompiled standard library shipped with the toolchain. Fast, but
    /// concrete functions in `std` have no MIR and become opaque.
    Shipped,
    /// The standard library rebuilt from source with MIR encoded, giving full
    /// visibility at the cost of a one time rebuild.
    Full,
}

impl StdMode {
    /// The name used on the command line and in reports.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Shipped => "shipped",
            Self::Full => "full",
        }
    }
}

/// The build configuration an analysis ran under.
///
/// Reported alongside every result. Overflow checks in particular change the
/// answer, so a report that does not name its profile is not meaningful.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BuildConfig {
    /// The compiler version string.
    pub rustc: String,
    /// The cargo profile, for example `release`.
    pub profile: String,
    /// Whether debug assertions were enabled.
    pub debug_assertions: bool,
    /// Whether arithmetic overflow checks were enabled.
    pub overflow_checks: bool,
    /// How the standard library was supplied.
    pub std_mode: StdMode,
}

/// One crate's contribution to the graph.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Artifact {
    /// The crate this artifact was produced from.
    pub krate: String,
    /// The build configuration in force.
    pub config: BuildConfig,
    /// The function bodies observed while compiling this crate.
    pub bodies: Vec<Body>,
}
