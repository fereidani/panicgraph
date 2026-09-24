//! What the analysis reports for syntax only the pinned nightly accepts.

mod support;

/// The categories one function of the nightly fixture was reported with.
fn categories_of(name: &str) -> Vec<String> {
    let dir = support::fixture("nightly");
    support::findings(&support::analyse_json(&dir, "release", &[]))
        .into_iter()
        .find(|(function, _)| function == name)
        .map(|(_, categories)| categories)
        .unwrap_or_default()
}

#[test]
fn a_tail_call_raises_what_its_callee_raises() {
    let categories = categories_of("must_index_by_tail_call");
    assert!(
        categories.iter().any(|c| c == "index"),
        "the function tail calls one that indexes, so it can panic with \
         index, but it was reported with {categories:?}"
    );
}

#[test]
fn assembly_that_may_unwind_is_code_the_analysis_cannot_read() {
    let unwinding = categories_of("must_run_unwinding_assembly");
    assert!(
        unwinding.iter().any(|c| c == "foreign"),
        "assembly able to unwind is foreign code, got {unwinding:?}"
    );
    let plain = categories_of("clean_run_assembly");
    assert!(
        plain.is_empty(),
        "assembly that cannot unwind raises nothing, got {plain:?}"
    );
}
