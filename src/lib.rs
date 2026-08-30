//! Reports which functions can panic, why, and through what call path.
//!
//! The analysis proper is the taxonomy, the graph, the solver and the witness
//! search. None of it depends on the compiler: the driver produces
//! [`Artifact`] values and everything here works from those, which is what
//! lets the whole thing be tested without building a crate first.
//!
//! The binaries are thin shells around these modules, so argument parsing and
//! rendering can be exercised directly by tests.

pub mod category;
pub mod graph;
pub mod model;
pub mod solve;
pub mod util;
pub mod verify;
pub mod witness;

/// Shared by the interactive view and the drawing, so it is only built
/// when one of them is.
#[cfg(any(feature = "serve", feature = "svg"))]
pub mod api;
pub mod args;
pub mod check;
pub mod report;
pub mod run;
#[cfg(feature = "serve")]
pub mod serve;
#[cfg(feature = "svg")]
pub mod svg;

pub use crate::{
    category::{Category, CategorySet, Termination, parse_selector},
    graph::{FuncId, Graph},
    model::{
        Artifact, Body, BuildConfig, CallSite, EdgeKind, FuncKey, Guard, Loc,
        PanicSite, Reified, StdMode, UnwindOrigin,
    },
    solve::{Policy, Solution, Solver},
    witness::{Terminal, Witness},
};
