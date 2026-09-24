//! How artifacts merge into one graph.

mod support;

use panicgraph::{Category, FuncKey, Graph};

use crate::support::{BodyBuilder, artifact};

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
