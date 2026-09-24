//! Explaining how one function reaches its panics.

mod support;

use panicgraph::{
    Body, Category, CategorySet, FuncKey, Graph, Policy, Solution, Solver,
    args, report,
};

use crate::support::{BodyBuilder, graph};

/// A generic function read as written, which reaches one category, and an
/// instantiation of it, which reaches another. The report names them once.
fn written_and_instance() -> Vec<Body> {
    let mut written = BodyBuilder::new("gen").panics(Category::Unwrap).build();
    written.key = FuncKey("generic:gen".to_owned());
    let mut instance = BodyBuilder::new("gen").panics(Category::Index).build();
    instance.key = FuncKey("gen<u8>".to_owned());
    vec![written, instance]
}

/// Solves a graph with nothing suppressed.
fn solved(built: &Graph) -> Solution {
    Solver::new(
        built,
        Policy {
            suppressed: CategorySet::EMPTY,
            edges: panicgraph::solve::Edges::default(),
        },
    )
    .solve()
    .expect("the solver should converge")
}

#[test]
fn every_panic_the_report_names_is_explained() {
    let built = graph(written_and_instance());
    let solution = solved(&built);
    let mut out = String::new();
    let asked =
        args::parse(["why", "gen"]).expect("the arguments should parse");
    report::why(&built, &solution, &asked, "gen", &mut out)
        .expect("the explanation should render");
    for category in ["unwrap", "index"] {
        assert!(
            out.contains(&format!("gen can panic with `{category}`")),
            "the report names both panics under `gen`, so both are \
             explained, got:\n{out}"
        );
    }
    assert!(
        out.contains("has 2 bodies"),
        "the reader is told why two bodies answer for one name, got:\n{out}"
    );
}

#[test]
fn the_document_names_every_panic_and_where_its_path_starts() {
    let built = graph(written_and_instance());
    let solution = solved(&built);
    let mut out = String::new();
    let asked = args::parse(["--json", "why", "gen"])
        .expect("the arguments should parse");
    report::why(&built, &solution, &asked, "gen", &mut out)
        .expect("the document should render");
    let doc: serde_json::Value =
        serde_json::from_str(&out).expect("the document should be json");
    assert_eq!(doc["bodies"], 2);
    assert_eq!(doc["categories"], serde_json::json!(["index", "unwrap"]));
    let paths = doc["paths"].as_array().cloned().unwrap_or_default();
    assert_eq!(paths.len(), 2, "one path per category, got {doc:#}");
    assert!(
        paths.iter().all(|path| path["from"] == "gen"),
        "each path names the body it starts in, got {doc:#}"
    );
}
