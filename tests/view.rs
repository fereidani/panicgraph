//! What the interactive view is sent.

#![cfg(feature = "serve")]

mod support;

use panicgraph::{
    Body, Category, CategorySet, FuncKey, Graph, api, solve::Edges,
};

use crate::support::{BodyBuilder, graph};

/// A generic function read as written, which reaches one category, and an
/// instantiation of it, which reaches another, in that order.
fn written_and_instance() -> Vec<Body> {
    let mut written = BodyBuilder::new("gen").panics(Category::Unwrap).build();
    written.key = FuncKey("generic:gen".to_owned());
    let mut instance = BodyBuilder::new("gen").panics(Category::Index).build();
    instance.key = FuncKey("gen<u8>".to_owned());
    vec![written, instance]
}

/// The index of the first node of a name, which is the one the view keeps
/// for it.
fn first_named(built: &Graph, name: &str) -> usize {
    built
        .iter()
        .find(|(_, body)| body.display == name)
        .map(|(id, _)| id.index())
        .expect("the name should be in the graph")
}

#[test]
fn a_function_frame_names_the_function_it_stands_for() {
    // The closure comes first, so the function's frame is made as the
    // first segment of the closure's path before the function arrives.
    let built = graph(vec![
        BodyBuilder::new("outer::{closure#0}")
            .panics(Category::Unwrap)
            .build(),
        BodyBuilder::new("outer").panics(Category::Index).build(),
    ]);
    let flame = api::flame(&built, CategorySet::EMPTY, Edges::default(), false)
        .expect("the tree should build");
    let rows = flame["nodes"].as_array().cloned().unwrap_or_default();
    for full in ["outer", "outer::{closure#0}"] {
        assert!(
            rows.iter()
                .any(|row| row["kind"] == "function" && row["full"] == full),
            "the view explains a frame by the function frame above it, so \
             `{full}` needs one carrying its whole name, got {rows:#?}"
        );
    }
}

#[test]
fn a_click_explains_a_panic_another_body_of_the_name_reaches() {
    let built = graph(written_and_instance());
    let node = first_named(&built, "gen");
    for category in ["unwrap", "index"] {
        let answer = api::why(
            &built,
            node,
            category,
            CategorySet::EMPTY,
            Edges::default(),
        )
        .expect("the question should be answered");
        assert_eq!(
            answer["found"], true,
            "`gen` is drawn reaching {category}, so a click on it must \
             explain it, got {answer:#}"
        );
    }
}

#[test]
fn the_summary_counts_functions_as_the_report_names_them() {
    let built = graph(written_and_instance());
    let solved = api::solve(&built, CategorySet::EMPTY, Edges::default())
        .expect("the solve should run");
    assert_eq!(
        solved["summary"]["can_panic"], 1,
        "a generic function and its instantiation are one function"
    );
    let index = solved["counterfactual"]
        .as_array()
        .and_then(|rows| rows.iter().find(|row| row["category"] == "index"))
        .cloned()
        .unwrap_or_default();
    assert_eq!(index["functions_reaching"], 1);
}
