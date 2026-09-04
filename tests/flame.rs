//! Folding runs of single calls into the frame above them.

#![cfg(any(feature = "serve", feature = "svg"))]

use panicgraph::{
    EdgeKind,
    api::{FlameRow, fold_chains},
};

/// A frame standing for a call resolved the given way.
fn hop(id: usize, parent: Option<usize>, kind: &'static str) -> FlameRow {
    FlameRow {
        id,
        parent,
        name: format!("f{id}"),
        category: None,
        kind,
        cleanup: false,
        elided: Vec::new(),
        value: 1,
        verdict: None,
    }
}

/// A chain of three calls ending in a panic, joined by one edge kind.
fn chain(kind: &'static str) -> Vec<FlameRow> {
    let mut rows = vec![hop(0, None, "root"), hop(1, Some(0), kind)];
    rows.push(hop(2, Some(1), kind));
    rows.push(FlameRow {
        category: Some("index"),
        ..hop(3, Some(2), "site")
    });
    rows
}

#[test]
fn every_edge_kind_folds_the_chain_it_joins() {
    for kind in EdgeKind::ALL {
        let folded = fold_chains(&chain(kind.name()));
        assert!(
            folded.len() < chain(kind.name()).len(),
            "a run of {} calls should fold, got {folded:#?}",
            kind.name()
        );
    }
}

#[test]
fn a_folded_run_keeps_the_names_it_swallowed() {
    let folded = fold_chains(&chain(EdgeKind::Generic.name()));
    assert!(
        folded.iter().any(|row| !row.elided.is_empty()),
        "a folded frame must name what it swallowed, got {folded:#?}"
    );
}
