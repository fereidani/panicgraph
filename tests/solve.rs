//! Behaviour of the suppression-aware solver.

mod support;

use panicgraph::{
    Category, CategorySet, FuncKey, Graph, Policy, Solver, witness,
};

use crate::support::{BodyBuilder, artifact};

/// Solves a set of bodies under one suppression policy.
fn solve(
    bodies: Vec<panicgraph::Body>,
    suppressed: CategorySet,
) -> (Graph, panicgraph::Solution) {
    let graph = Graph::from_artifacts(vec![artifact(bodies)]);
    let policy = Policy {
        suppressed,
        follow_inexact: true,
    };
    let solution = Solver::new(&graph, policy)
        .solve()
        .expect("the solver should converge on a finite graph");
    (graph, solution)
}

/// Looks a function up by name.
fn id(graph: &Graph, name: &str) -> panicgraph::FuncId {
    graph
        .id_of(&FuncKey(name.to_owned()))
        .expect("the function should be in the graph")
}

#[test]
fn suppression_is_transitive() {
    let bodies = vec![
        BodyBuilder::new("caller").calls("grow").build(),
        BodyBuilder::new("grow")
            .panics(Category::CapacityOverflow)
            .build(),
    ];

    let (graph, solution) = solve(bodies.clone(), CategorySet::EMPTY);
    assert!(
        solution
            .enabled(id(&graph, "caller"))
            .contains(Category::CapacityOverflow),
        "without suppression the caller inherits the allocation panic"
    );

    let (graph, solution) = solve(bodies, CategorySet::oom());
    assert!(
        solution.is_clean(id(&graph, "caller")),
        "a caller that only panics through allocation is clean once \
         allocation is suppressed"
    );
}

#[test]
fn unrelated_panics_survive_suppression() {
    let bodies = vec![
        BodyBuilder::new("caller")
            .calls("grow")
            .calls("index")
            .build(),
        BodyBuilder::new("grow")
            .panics(Category::CapacityOverflow)
            .build(),
        BodyBuilder::new("index").panics(Category::Index).build(),
    ];

    let (graph, solution) = solve(bodies, CategorySet::oom());
    let enabled = solution.enabled(id(&graph, "caller"));
    assert!(
        enabled.contains(Category::Index),
        "suppressing allocation must not hide an index panic"
    );
    assert!(
        !enabled.contains(Category::CapacityOverflow),
        "the allocation panic is suppressed"
    );
}

#[test]
fn cleanup_reachable_only_through_a_suppressed_panic_is_suppressed() {
    // `caller` calls `grow`, which can only fail by exhausting capacity.
    // While that failure unwinds, a drop runs and panics. Assuming the
    // allocation succeeds means the drop never runs either.
    let bodies = vec![
        BodyBuilder::new("caller")
            .calls("grow")
            .calls_on_unwind_of("drop_glue", 0)
            .build(),
        BodyBuilder::new("grow")
            .panics(Category::CapacityOverflow)
            .build(),
        BodyBuilder::new("drop_glue")
            .panics(Category::Explicit)
            .build(),
    ];

    let (graph, solution) = solve(bodies.clone(), CategorySet::EMPTY);
    assert!(
        solution
            .enabled(id(&graph, "caller"))
            .contains(Category::Explicit),
        "without suppression the unwind path reaches the panicking drop"
    );

    let (graph, solution) = solve(bodies, CategorySet::oom());
    assert!(
        solution.is_clean(id(&graph, "caller")),
        "the drop is only reachable while the suppressed panic unwinds, so \
         it is unreachable too"
    );
}

#[test]
fn cleanup_reachable_normally_survives_suppression() {
    // The same panicking drop, but now also on the ordinary path. It must
    // still be reported.
    let bodies = vec![
        BodyBuilder::new("caller")
            .calls("grow")
            .calls("drop_glue")
            .build(),
        BodyBuilder::new("grow")
            .panics(Category::CapacityOverflow)
            .build(),
        BodyBuilder::new("drop_glue")
            .panics(Category::Explicit)
            .build(),
    ];

    let (graph, solution) = solve(bodies, CategorySet::oom());
    assert!(
        solution
            .enabled(id(&graph, "caller"))
            .contains(Category::Explicit),
        "a drop on the normal path is unaffected by allocation suppression"
    );
}

#[test]
fn recursion_converges() {
    let bodies = vec![
        BodyBuilder::new("a").calls("b").build(),
        BodyBuilder::new("b")
            .calls("a")
            .panics(Category::Index)
            .build(),
    ];

    let (graph, solution) = solve(bodies, CategorySet::EMPTY);
    assert!(
        solution.enabled(id(&graph, "a")).contains(Category::Index),
        "a cycle must still propagate the panic"
    );
}

#[test]
fn missing_callees_are_unknown_not_clean() {
    let bodies = vec![BodyBuilder::new("caller").calls("absent").build()];

    let (graph, solution) = solve(bodies, CategorySet::EMPTY);
    assert!(
        solution
            .enabled(id(&graph, "caller"))
            .contains(Category::Unknown),
        "a callee with no recorded body is unknown, never assumed clean"
    );
}

#[test]
fn witness_names_the_panicking_function() {
    let bodies = vec![
        BodyBuilder::new("caller").calls("middle").build(),
        BodyBuilder::new("middle").calls("leaf").build(),
        BodyBuilder::new("leaf").panics(Category::Unwrap).build(),
    ];

    let (graph, solution) = solve(bodies, CategorySet::EMPTY);
    let path = witness::find(
        &graph,
        &solution,
        id(&graph, "caller"),
        Category::Unwrap,
    )
    .expect("the unwrap should be reachable");

    assert_eq!(graph.body(path.func).display, "leaf");
    assert_eq!(path.hops.len(), 2, "the path runs caller -> middle -> leaf");
    assert_eq!(path.terminal, panicgraph::Terminal::Site(0));
}

#[test]
fn witness_is_absent_when_suppressed() {
    let bodies = vec![
        BodyBuilder::new("caller").calls("grow").build(),
        BodyBuilder::new("grow")
            .panics(Category::CapacityOverflow)
            .build(),
    ];

    let (graph, solution) = solve(bodies, CategorySet::oom());
    assert!(
        witness::find(
            &graph,
            &solution,
            id(&graph, "caller"),
            Category::CapacityOverflow,
        )
        .is_none(),
        "a suppressed category has no witness"
    );
}
