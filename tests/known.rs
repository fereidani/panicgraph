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
];

/// The panics each function must *not* be reported with.
///
/// A check the analysis can settle has to go even where the same function
/// keeps another that it cannot.
const MUST_NOT_PANIC: &[(&str, &str)] = &[
    ("must_divide_once_of_two", "remainder-by-zero"),
    ("must_lock", "unwrap"),
    ("must_write", "unwrap"),
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
];

/// Analyses the fixture crate and returns the categories reported per
/// function.
///
/// Nothing is suppressed, so the answer is everything the analysis can see.
fn analyse() -> Vec<(String, Vec<String>)> {
    let exe = PathBuf::from(env!("CARGO_BIN_EXE_panicgraph"));
    let fixture = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("known");
    let output = Command::new(&exe)
        .arg("--manifest-dir")
        .arg(&fixture)
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
    let reported = analyse();
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
