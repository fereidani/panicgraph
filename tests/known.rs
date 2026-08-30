//! What the analysis reports for a crate whose panics are known.
//!
//! This is the only test that runs the compiler driver, so it is what keeps
//! the two halves honest: the reachability of a body is decided against the
//! settings of the build in front of it, and a check the arguments settle is
//! not a panic. Both directions matter. Dropping a check that can fail would
//! make a clean report meaningless, and keeping one that cannot fail is the
//! noise the tool exists to remove.

use std::{path::PathBuf, process::Command};

use serde_json::Value;

/// The panic each function must be reported with.
const MUST_PANIC: &[(&str, &str)] = &[
    ("must_index", "index"),
    ("must_divide", "divide-by-zero"),
    ("must_remainder", "remainder-by-zero"),
    ("must_unwrap", "unwrap"),
    ("must_assert", "explicit"),
    ("must_slice_tail", "index"),
    ("must_copy", "explicit"),
    ("must_assert_generic", "explicit"),
    ("must_assert_false", "explicit"),
    ("must_divide_misguarded", "divide-by-zero"),
    ("must_divide_inverted_guard", "divide-by-zero"),
    ("must_divide_once_of_two", "divide-by-zero"),
    ("must_divide_narrowed", "divide-by-zero"),
    ("must_push", "capacity-overflow"),
    ("must_push", "alloc-failure"),
    ("must_rethrow", "explicit"),
    ("must_lock", "poison"),
    ("must_write", "fmt"),
    ("must_rc_clone", "refcount-overflow"),
    ("must_slice_str", "str-boundary"),
    ("must_borrow", "borrow"),
    ("must_dyn", "unknown"),
    ("must_foreign", "foreign"),
    ("must_catch_abort", "alloc-failure"),
    ("must_index_off_by_one", "index"),
    ("must_index_wrong_slice", "index"),
    ("must_modulo_signed", "index"),
];

/// The panics each function must *not* be reported with.
///
/// A check the analysis can settle has to go even where the same function
/// keeps another that it cannot.
const MUST_NOT_PANIC: &[(&str, &str)] = &[
    ("must_divide_once_of_two", "remainder-by-zero"),
    ("must_lock", "unwrap"),
    ("must_write", "unwrap"),
    ("must_not_catch_explicit", "explicit"),
];

/// The functions that must be reported with nothing at all.
const MUST_BE_CLEAN: &[&str] = &[
    "clean_divide_by_constant",
    "clean_fold",
    "clean_count_zeros",
    "clean_sum_by_get",
    "clean_assert_true",
    "clean_guarded_divide",
    "clean_guarded_divide_ne",
    "clean_guarded_remainder",
    "clean_guarded_widening",
    "clean_modulo_index",
    "clean_masked_index",
    "clean_guarded_index",
    "clean_guarded_index_flipped",
    "clean_while_index",
];

/// The functions that must stay clean in a debug build as well.
///
/// A debug build folds the same guards without the optimizer's help: no
/// inlining has merged the comparison into the check, so every settled
/// verdict below is the analysis's own reasoning. The full clean list is
/// not used because a debug build genuinely adds checks inside the standard
/// library that some of those functions reach.
const MUST_BE_CLEAN_IN_DEBUG: &[&str] = &[
    "clean_divide_by_constant",
    "clean_guarded_divide",
    "clean_guarded_divide_ne",
    "clean_guarded_remainder",
    "clean_modulo_index",
    "clean_masked_index",
    "clean_guarded_index",
    "clean_guarded_index_flipped",
    "clean_while_index",
];

/// Analyses the fixture crate and returns the categories reported per
/// function.
///
/// Nothing is suppressed, so the answer is everything the analysis can see.
fn analyse(profile: &str) -> Vec<(String, Vec<String>)> {
    let exe = PathBuf::from(env!("CARGO_BIN_EXE_panicgraph"));
    let fixture = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("known");
    let output = Command::new(&exe)
        .arg("--manifest-dir")
        .arg(&fixture)
        .arg("--profile")
        .arg(profile)
        .arg("--suppress")
        .arg("")
        .arg("--format")
        .arg("json")
        .output()
        .expect("the front end should run");
    let report: Value =
        serde_json::from_slice(&output.stdout).unwrap_or_else(|err| {
            panic!(
                "the report should be json: {err}\n{}",
                String::from_utf8_lossy(&output.stderr)
            )
        });
    let findings = report["findings"]
        .as_array()
        .expect("the report should list findings");
    findings
        .iter()
        .map(|finding| {
            let name = finding["function"].as_str().unwrap_or_default();
            let categories = finding["categories"]
                .as_array()
                .map(|list| {
                    list.iter()
                        .filter_map(|c| c.as_str().map(str::to_owned))
                        .collect()
                })
                .unwrap_or_default();
            (name.to_owned(), categories)
        })
        .collect()
}

#[test]
fn a_known_crate_reports_exactly_its_panics() {
    let reported = analyse("release");
    let found = |name: &str| {
        reported
            .iter()
            .find(|(function, _)| function == name)
            .map(|(_, categories)| categories.clone())
    };

    for (function, category) in MUST_PANIC {
        let categories = found(function).unwrap_or_else(|| {
            panic!("{function} can panic with {category} and was not reported")
        });
        assert!(
            categories.iter().any(|c| c == category),
            "{function} can panic with {category}, but was reported with \
             {categories:?}"
        );
    }

    for (function, category) in MUST_NOT_PANIC {
        let categories = found(function).unwrap_or_default();
        assert!(
            !categories.iter().any(|c| c == category),
            "{function} cannot panic with {category}, but was reported with \
             {categories:?}"
        );
    }

    for function in MUST_BE_CLEAN {
        assert!(
            found(function).is_none(),
            "{function} cannot panic, but was reported with {:?}",
            found(function)
        );
    }
}

#[test]
fn a_debug_build_still_folds_the_guards() {
    let reported = analyse("debug");
    let found = |name: &str| {
        reported
            .iter()
            .find(|(function, _)| function == name)
            .map(|(_, categories)| categories.clone())
    };

    for function in MUST_BE_CLEAN_IN_DEBUG {
        assert!(
            found(function).is_none(),
            "{function} cannot panic in a debug build either, but was \
             reported with {:?}",
            found(function)
        );
    }

    for (function, category) in MUST_PANIC {
        let categories = found(function).unwrap_or_else(|| {
            panic!(
                "{function} can panic with {category} in a debug build and \
                 was not reported"
            )
        });
        assert!(
            categories.iter().any(|c| c == category),
            "{function} can panic with {category}, but a debug build \
             reported {categories:?}"
        );
    }
}
