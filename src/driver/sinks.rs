//! Classification of the functions that actually raise panics.
//!
//! Panic entry points are matched by `DefId`, resolved through the crate name
//! and the unrendered def path. Matching the rendered path string is not
//! reliable: `core::option::unwrap_failed` prints as `std::option::
//! unwrap_failed` once `std` is in the crate graph.

use panicgraph::{Category, Termination};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::{middle::codegen_fn_attrs::CodegenFnAttrFlags, ty::TyCtxt};

use crate::util::Map;

/// A panic entry point and how it terminates.
#[derive(Debug, Clone, Copy)]
pub struct Sink {
    /// The category to report.
    pub category: Category,
    /// Whether reaching it unwinds or aborts.
    pub termination: Termination,
}

const fn unwind(category: Category) -> Sink {
    Sink {
        category,
        termination: Termination::Unwind,
    }
}

const fn abort(category: Category) -> Sink {
    Sink {
        category,
        termination: Termination::Abort,
    }
}

/// Entry points identified by crate name and def path.
///
/// Names drift between compiler releases, so several historical spellings are
/// listed. An entry that no longer exists simply never matches.
const EXACT: &[(&str, &str, Sink)] = &[
    ("core", "panicking::panic", unwind(Category::Explicit)),
    ("core", "panicking::panic_fmt", unwind(Category::Explicit)),
    ("core", "panicking::panic_str", unwind(Category::Explicit)),
    (
        "core",
        "panicking::panic_explicit",
        unwind(Category::Explicit),
    ),
    (
        "core",
        "panicking::panic_display",
        unwind(Category::Explicit),
    ),
    (
        "core",
        "panicking::assert_failed_inner",
        unwind(Category::Explicit),
    ),
    (
        "core",
        "panicking::panic_nounwind",
        abort(Category::Explicit),
    ),
    (
        "core",
        "panicking::panic_nounwind_fmt",
        abort(Category::Explicit),
    ),
    (
        "core",
        "panicking::panic_cannot_unwind",
        abort(Category::Explicit),
    ),
    (
        "core",
        "panicking::panic_bounds_check",
        unwind(Category::Index),
    ),
    ("core", "option::unwrap_failed", unwind(Category::Unwrap)),
    ("core", "option::expect_failed", unwind(Category::Unwrap)),
    ("core", "result::unwrap_failed", unwind(Category::Unwrap)),
    (
        "core",
        "slice::index::slice_index_fail",
        unwind(Category::Index),
    ),
    (
        "core",
        "slice::index::slice_start_index_len_fail",
        unwind(Category::Index),
    ),
    (
        "core",
        "slice::index::slice_end_index_len_fail",
        unwind(Category::Index),
    ),
    (
        "core",
        "slice::index::slice_index_order_fail",
        unwind(Category::Index),
    ),
    (
        "core",
        "str::slice_error_fail",
        unwind(Category::StrBoundary),
    ),
    (
        "core",
        "cell::panic_already_borrowed",
        unwind(Category::Borrow),
    ),
    (
        "core",
        "cell::panic_already_mutably_borrowed",
        unwind(Category::Borrow),
    ),
    (
        "alloc",
        "raw_vec::capacity_overflow",
        unwind(Category::CapacityOverflow),
    ),
    (
        "alloc",
        "raw_vec::handle_error",
        unwind(Category::CapacityOverflow),
    ),
    (
        "alloc",
        "raw_vec::handle_reserve",
        unwind(Category::CapacityOverflow),
    ),
    (
        "alloc",
        "alloc::handle_alloc_error",
        abort(Category::AllocFailure),
    ),
    (
        "std",
        "alloc::handle_alloc_error",
        abort(Category::AllocFailure),
    ),
];

/// Resolves panic entry points and caches the answer per `DefId`.
pub struct SinkTable {
    cache: Map<DefId, Option<Sink>>,
}

impl SinkTable {
    /// Creates an empty table.
    #[must_use]
    pub fn new() -> Self {
        Self {
            cache: Map::default(),
        }
    }

    /// Classifies a function, returning `None` when it is not a panic entry
    /// point.
    pub fn get(&mut self, tcx: TyCtxt<'_>, did: DefId) -> Option<Sink> {
        if let Some(hit) = self.cache.get(&did) {
            return *hit;
        }
        let sink = Self::classify(tcx, did);
        self.cache.insert(did, sink);
        sink
    }

    /// Works out whether a function raises a panic, and of what kind.
    fn classify(tcx: TyCtxt<'_>, did: DefId) -> Option<Sink> {
        let krate = tcx.crate_name(did.krate);
        let krate = krate.as_str();
        let path = Self::def_path(tcx, did);

        for (k, p, sink) in EXACT {
            if *k == krate && *p == path {
                return Some(*sink);
            }
        }

        // Anything else inside the panic machinery still raises a panic.
        if krate == "core" && path.starts_with("panicking::") {
            return Some(unwind(Category::Explicit));
        }

        if let Some(sink) =
            Self::by_leaf_name(path.rsplit("::").next().unwrap_or(&path))
        {
            return Some(sink);
        }

        Self::opaque_divergence(tcx, did, krate)
    }

    /// Classifies a core library function that cannot return and cannot be
    /// read.
    ///
    /// The cold helper a container calls to report a failed check is neither
    /// generic nor inlinable, so the shipped library keeps no body for it and
    /// the analysis would otherwise call the panic inside `copy_from_slice`
    /// unclassified. Nothing in `core` or `alloc` diverges except by
    /// panicking, so the signature alone settles it. The rule is confined to
    /// those two crates because `std` also owns `exit` and `abort`, which
    /// diverge without raising anything.
    fn opaque_divergence(
        tcx: TyCtxt<'_>,
        did: DefId,
        krate: &str,
    ) -> Option<Sink> {
        if !matches!(krate, "core" | "alloc") {
            return None;
        }
        if !matches!(tcx.def_kind(did), DefKind::Fn | DefKind::AssocFn) {
            return None;
        }
        if tcx.is_mir_available(did) {
            return None;
        }
        if !tcx
            .fn_sig(did)
            .skip_binder()
            .skip_binder()
            .output()
            .is_never()
        {
            return None;
        }
        let aborts = tcx
            .codegen_fn_attrs(did)
            .flags
            .contains(CodegenFnAttrFlags::NEVER_UNWIND);
        Some(if aborts {
            abort(Category::Explicit)
        } else {
            unwind(Category::Explicit)
        })
    }

    /// Matches conventional names used by allocation aware containers.
    ///
    /// Third party collections carry their own allocation failure funnels,
    /// for example hashbrown's `Fallibility::capacity_overflow`. Suppressing
    /// allocation panics has to reach those too, otherwise every crate using
    /// a hash map keeps reporting allocation noise.
    fn by_leaf_name(leaf: &str) -> Option<Sink> {
        match leaf {
            "capacity_overflow" => Some(unwind(Category::CapacityOverflow)),
            // Generated by the standard library's ub_checks macro. Treated
            // as a sink so the check itself is reported rather than the
            // generic panic entry point it happens to call.
            "precondition_check" => Some(abort(Category::UbCheck)),
            "handle_alloc_error" | "alloc_err" | "oom" => {
                Some(abort(Category::AllocFailure))
            }
            "panic_arc_overflow" | "panic_rc_overflow" => {
                Some(unwind(Category::RefCountOverflow))
            }
            _ => None,
        }
    }

    /// Renders a def path from its segments, without crate qualification.
    fn def_path(tcx: TyCtxt<'_>, did: DefId) -> String {
        let mut out = String::new();
        for seg in &tcx.def_path(did).data {
            let Some(name) = seg.data.get_opt_name() else {
                continue;
            };
            if !out.is_empty() {
                out.push_str("::");
            }
            out.push_str(name.as_str());
        }
        out
    }
}

impl Default for SinkTable {
    fn default() -> Self {
        Self::new()
    }
}
