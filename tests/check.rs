//! The gate a continuous integration run applies.

use std::path::PathBuf;

use panicgraph::{
    Artifact, Body, BuildConfig, Category, FuncKey, Graph, PanicSite, Policy,
    Solver, StdMode, Termination,
    args::{self, Args, Check, Command},
    check,
    model::Guard,
};

/// A function that panics with one category, or one that does not.
fn body(name: &str, category: Option<Category>) -> Body {
    Body {
        key: FuncKey(name.to_owned()),
        display: name.to_owned(),
        krate: "test".to_owned(),
        loc: None,
        sites: category
            .map(|category| PanicSite {
                category,
                termination: Termination::Unwind,
                reason: format!("{category} panic"),
                sink: None,
                loc: None,
                guard: Guard::always(),
            })
            .into_iter()
            .collect(),
        calls: Vec::new(),
        opaque: false,
        local: true,
    }
}

/// Builds a graph from the given functions.
fn graph(bodies: Vec<Body>) -> Graph {
    Graph::from_artifacts(vec![Artifact {
        krate: "test".to_owned(),
        config: BuildConfig {
            rustc: "test".to_owned(),
            profile: "release".to_owned(),
            debug_assertions: false,
            overflow_checks: false,
            std_mode: StdMode::Shipped,
        },
        bodies,
    }])
}

/// Parses a check invocation into the settings and its gate.
fn gate(argv: &[&str]) -> (Args, Check) {
    let mut whole = vec!["check"];
    whole.extend_from_slice(argv);
    let settings = args::parse(whole).expect("the arguments should parse");
    let Command::Check(rules) = settings.command.clone() else {
        panic!("expected a check command");
    };
    (settings, rules)
}

/// Runs a gate over the given functions.
fn outcome(bodies: Vec<Body>, argv: &[&str]) -> check::Outcome {
    let built = graph(bodies);
    let (settings, rules) = gate(argv);
    let solution = Solver::new(
        &built,
        Policy {
            suppressed: settings.suppress,
            follow_inexact: true,
        },
    )
    .solve()
    .expect("the solver should converge");
    check::run(&built, &solution, &settings, &rules)
        .expect("the gate should run")
}

/// The functions used by most of these tests.
fn sample() -> Vec<Body> {
    vec![
        body("parse", Some(Category::Unwrap)),
        body("read", Some(Category::Index)),
        body("clean", None),
    ]
}

#[test]
fn with_no_gate_nothing_may_panic() {
    let result = outcome(sample(), &[]);
    assert!(result.failed());
    assert_eq!(
        result.violations.len(),
        2,
        "the two panicking functions are both violations, the clean one is \
         not"
    );
}

#[test]
fn a_pattern_narrows_what_must_not_panic() {
    let result = outcome(sample(), &["--forbid", "^parse$"]);
    assert!(result.failed());
    assert_eq!(result.violations.len(), 1);
    assert_eq!(result.violations[0].finding.function, "parse");
}

#[test]
fn a_pattern_matching_only_clean_functions_passes() {
    let result = outcome(sample(), &["--forbid", "^clean$"]);
    assert!(!result.failed());
    assert_eq!(
        result.findings.len(),
        2,
        "the findings still list everything that panics"
    );
}

#[test]
fn an_allowance_exempts_a_known_exception() {
    let result = outcome(
        sample(),
        &["--forbid", "^(parse|read)$", "--allow", "^read$"],
    );
    assert_eq!(result.violations.len(), 1);
    assert_eq!(result.violations[0].finding.function, "parse");
}

#[test]
fn a_ceiling_replaces_the_default_rule() {
    assert!(
        !outcome(sample(), &["--max", "5"]).failed(),
        "naming a ceiling means the ceiling is the gate, not that nothing \
         may panic"
    );
    let over = outcome(sample(), &["--max", "1"]);
    assert!(over.failed());
    assert_eq!(over.over_max, Some((2, 1)));
}

#[test]
fn an_unusable_pattern_is_rejected() {
    let built = graph(sample());
    let (settings, rules) = gate(&["--forbid", "("]);
    let solution = Solver::new(
        &built,
        Policy {
            suppressed: settings.suppress,
            follow_inexact: true,
        },
    )
    .solve()
    .expect("the solver should converge");
    assert!(check::run(&built, &solution, &settings, &rules).is_err());
}

#[test]
fn a_baseline_round_trips() {
    let file = std::env::temp_dir().join("panicgraph-baseline-round-trip.json");
    let result = outcome(sample(), &[]);
    let (args, _) = gate(&[]);
    check::write_baseline(&file, &args, &result.findings)
        .expect("the baseline should be written");

    let read = check::read_baseline(&file).expect("and read back");
    assert_eq!(read.len(), 2);
    assert_eq!(
        read.get("parse").map(Vec::as_slice),
        Some(&["unwrap".to_owned()][..])
    );
    let _ = std::fs::remove_file(&file);
}

#[test]
fn a_baseline_admits_what_it_records_and_rejects_the_rest() {
    let file = std::env::temp_dir().join("panicgraph-baseline-gate.json");
    let (args, _) = gate(&[]);
    let recorded = outcome(sample(), &[]);
    check::write_baseline(&file, &args, &recorded.findings)
        .expect("the baseline should be written");

    let path = file.to_string_lossy().into_owned();
    let unchanged = outcome(sample(), &["--baseline", &path]);
    assert!(!unchanged.failed(), "nothing changed, so nothing is new");

    let mut grown = sample();
    grown.push(body("added", Some(Category::Explicit)));
    let widened = outcome(grown, &["--baseline", &path]);
    assert!(widened.failed());
    assert_eq!(widened.violations.len(), 1);
    assert_eq!(widened.violations[0].finding.function, "added");

    let _ = std::fs::remove_file(&file);
}

#[test]
fn a_baseline_catches_a_function_that_gains_a_category() {
    let file = std::env::temp_dir().join("panicgraph-baseline-category.json");
    let (args, _) = gate(&[]);
    check::write_baseline(&file, &args, &outcome(sample(), &[]).findings)
        .expect("the baseline should be written");

    let mut changed = sample();
    changed[0] = body("parse", Some(Category::Index));
    let path = file.to_string_lossy().into_owned();
    let result = outcome(changed, &["--baseline", &path]);
    assert!(
        result.failed(),
        "the function was already recorded, but not with this panic"
    );
    let _ = std::fs::remove_file(&file);
}

#[test]
fn a_baseline_reports_what_no_longer_panics() {
    let file = std::env::temp_dir().join("panicgraph-baseline-fixed.json");
    let (args, _) = gate(&[]);
    check::write_baseline(&file, &args, &outcome(sample(), &[]).findings)
        .expect("the baseline should be written");

    let mut fixed = sample();
    fixed[0] = body("parse", None);
    let path = file.to_string_lossy().into_owned();
    let result = outcome(fixed, &["--baseline", &path]);
    assert!(!result.failed(), "removing a panic is not a failure");
    assert_eq!(result.fixed, vec!["parse".to_owned()]);
    let _ = std::fs::remove_file(&file);
}

#[test]
fn a_missing_baseline_says_how_to_make_one() {
    let err = check::read_baseline(&PathBuf::from("/nonexistent/pg.json"))
        .expect_err("the file is not there");
    let text = format!("{err:#}");
    assert!(
        text.contains("panicgraph baseline"),
        "the message should name the command that writes one, got: {text}"
    );
}
