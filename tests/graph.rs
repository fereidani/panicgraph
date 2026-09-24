//! How artifacts merge into one graph.

mod support;

use panicgraph::{Body, Category, FuncKey, Graph, select::Selection};

use crate::support::{BodyBuilder, artifact};

/// A generic function's body from the crate's own build and its copy from
/// a test build, under one key.
fn own_and_test_copy() -> (Body, Body) {
    let own = BodyBuilder::new("generic:first_of")
        .panics(Category::Index)
        .build();
    let mut copy = own.clone();
    copy.from_tests = true;
    (own, copy)
}

/// Whether the selection names the function the key belongs to.
fn shown(graph: &Graph, key: &str) -> bool {
    let id = graph
        .id_of(&FuncKey(key.to_owned()))
        .expect("the key should be in the graph");
    Selection::default()
        .functions(graph)
        .any(|(shown, _)| shown == id)
}

#[test]
fn the_crate_own_body_beats_a_test_copy_whichever_comes_first() {
    for test_copy_first in [true, false] {
        let (own, copy) = own_and_test_copy();
        let artifacts = if test_copy_first {
            vec![artifact(vec![copy]), artifact(vec![own])]
        } else {
            vec![artifact(vec![own]), artifact(vec![copy])]
        };
        let graph = Graph::from_artifacts(artifacts);
        assert_eq!(graph.len(), 1, "one key is one body");
        let id = graph
            .id_of(&FuncKey("generic:first_of".to_owned()))
            .expect("the key should be in the graph");
        assert!(
            !graph.body(id).from_tests,
            "the crate's own build must stand for the function, with the \
             test copy merged {}",
            if test_copy_first { "first" } else { "second" }
        );
        assert!(
            shown(&graph, "generic:first_of"),
            "a function the crate's own build carries is reported"
        );
    }
}

#[test]
fn a_pointer_candidate_unwinds_into_the_cleanup_its_call_does() {
    use panicgraph::{
        CategorySet, EdgeKind, Guard, Policy, Reified, Solver, UnwindOrigin,
        solve::Edges,
    };
    // `caller` calls through a pointer. While that call unwinds, a drop
    // runs and indexes. The one function reified to that signature panics.
    let mut caller = BodyBuilder::new("caller")
        .calls_unresolved(EdgeKind::FnPtr)
        .calls("dropper")
        .build();
    caller.calls[0].sig = Some("fn()".to_owned());
    caller.calls[1].guard = Guard {
        normal: false,
        origins: vec![UnwindOrigin::Call(0)],
    };
    let mut made = artifact(vec![
        caller,
        BodyBuilder::new("dropper").panics(Category::Index).build(),
        BodyBuilder::new("target")
            .panics(Category::Explicit)
            .build(),
    ]);
    made.reified.push(Reified {
        key: FuncKey("target".to_owned()),
        display: "target".to_owned(),
        sig: "fn()".to_owned(),
    });
    let graph = Graph::from_artifacts(vec![made]);
    // With the pointer call suppressed, only the candidate unwinds.
    let solution = Solver::new(
        &graph,
        Policy {
            suppressed: CategorySet::single(Category::FnPointer),
            edges: Edges {
                follow_inexact: true,
                candidates: true,
            },
        },
    )
    .solve()
    .expect("the solver should converge");
    let caller = graph
        .id_of(&FuncKey("caller".to_owned()))
        .expect("the caller should be in the graph");
    let enabled = solution.enabled(caller);
    assert!(
        enabled.contains(Category::Explicit),
        "the candidate is followed, got {enabled:?}"
    );
    assert!(
        enabled.contains(Category::Index),
        "the candidate unwinds into the cleanup, so the drop there runs, \
         got {enabled:?}"
    );
}
