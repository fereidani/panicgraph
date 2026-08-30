//! What checking findings against the compiled artifact reports.

mod support;

use crate::support::analyse_fixture_json;

/// The verdict reported for one function and category.
fn verdict_in(
    report: &serde_json::Value,
    function: &str,
    category: &str,
) -> String {
    let findings = report["findings"]
        .as_array()
        .expect("the report should list findings");
    let finding = findings
        .iter()
        .find(|f| f["function"].as_str() == Some(function))
        .unwrap_or_else(|| panic!("{function} should be reported"));
    finding["verified"][category]
        .as_str()
        .unwrap_or_else(|| {
            panic!("{function} should carry a verdict for {category}")
        })
        .to_owned()
}

#[test]
fn the_artifact_settles_what_the_folder_could_not() {
    let report = analyse_fixture_json("release", &["--verify"]);

    assert_eq!(
        verdict_in(&report, "verify_absent_loop", "index"),
        "absent",
        "the optimizer removes the loop's bounds check, and the sweep must \
         see that it is gone"
    );
    assert_eq!(
        verdict_in(&report, "must_index", "index"),
        "confirmed",
        "the bounds check survives, and the sweep must find its entry point"
    );
    assert_eq!(
        verdict_in(&report, "must_divide", "divide-by-zero"),
        "confirmed",
    );
    assert_eq!(
        verdict_in(&report, "must_rc_clone", "refcount-overflow"),
        "unverified",
        "an inlined trap leaves no symbol, so the sweep must not claim \
         either way"
    );
}
