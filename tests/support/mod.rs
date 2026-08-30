//! Builders for the small graphs these tests run on.
//!
//! Every test binary compiles this module on its own, so a builder only some
//! of them reach for is not dead code in the usual sense.
#![allow(dead_code)]

use std::{path::PathBuf, process::Command};

use panicgraph::{
    Artifact, Body, BuildConfig, CallSite, Category, EdgeKind, FuncKey, Graph,
    Guard, PanicSite, StdMode, Termination, UnwindOrigin,
};

/// Builds a function body one piece at a time.
pub struct BodyBuilder {
    body: Body,
}

impl BodyBuilder {
    /// Starts a local, non-opaque body.
    pub fn new(name: &str) -> Self {
        Self {
            body: Body {
                key: FuncKey(name.to_owned()),
                display: name.to_owned(),
                krate: "test".to_owned(),
                loc: None,
                sites: Vec::new(),
                calls: Vec::new(),
                opaque: false,
                foreign: false,
                local: true,
            },
        }
    }

    /// Adds a panic raised on the ordinary control flow path.
    pub fn panics(mut self, category: Category) -> Self {
        self.body.sites.push(site(
            category,
            Termination::Unwind,
            Guard::always(),
        ));
        self
    }

    /// Adds a panic only when one is named, which is how a test asks for a
    /// function that cannot panic.
    pub fn maybe_panics(self, category: Option<Category>) -> Self {
        match category {
            Some(category) => self.panics(category),
            None => self,
        }
    }

    /// Adds a call on the ordinary control flow path.
    pub fn calls(mut self, callee: &str) -> Self {
        self.body.calls.push(call(callee, Guard::always()));
        self
    }

    /// Adds a call that is one possible target rather than the proven one.
    pub fn calls_candidate(mut self, callee: &str) -> Self {
        let mut edge = call(callee, Guard::always());
        edge.candidate = true;
        edge.kind = EdgeKind::Vtable;
        self.body.calls.push(edge);
        self
    }

    /// Adds a call whose unwinding panics are contained, as under a catch.
    pub fn calls_behind_barrier(mut self, callee: &str) -> Self {
        let mut edge = call(callee, Guard::always());
        edge.barrier = true;
        self.body.calls.push(edge);
        self
    }

    /// Adds a panic that aborts rather than unwinds.
    pub fn aborts(mut self, category: Category) -> Self {
        self.body.sites.push(site(
            category,
            Termination::Abort,
            Guard::always(),
        ));
        self
    }

    /// Adds a call reachable only while the given earlier call unwinds.
    pub fn calls_on_unwind_of(mut self, callee: &str, call_index: u32) -> Self {
        self.body.calls.push(call(
            callee,
            Guard {
                normal: false,
                origins: vec![UnwindOrigin::Call(call_index)],
            },
        ));
        self
    }

    /// Finishes the body.
    pub fn build(self) -> Body {
        self.body
    }
}

/// A panic site with the given reachability.
fn site(
    category: Category,
    termination: Termination,
    guard: Guard,
) -> PanicSite {
    PanicSite {
        category,
        termination,
        reason: format!("{category} panic"),
        sink: None,
        loc: None,
        guard,
    }
}

/// A statically resolved call with the given reachability.
fn call(callee: &str, guard: Guard) -> CallSite {
    CallSite {
        callee: Some(FuncKey(callee.to_owned())),
        callee_display: callee.to_owned(),
        kind: EdgeKind::Static,
        loc: None,
        guard,
        barrier: false,
        candidate: false,
        sig: None,
    }
}

/// Builds the graph a set of bodies makes, as one crate's artifact.
pub fn graph(bodies: Vec<Body>) -> Graph {
    Graph::from_artifacts(vec![Artifact {
        reified: Vec::new(),
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

/// Analyses the known fixture crate through the installed front end and
/// returns the categories reported per function.
///
/// Nothing is suppressed, so the answer is everything the analysis can see.
pub fn analyse_fixture(
    profile: &str,
    extra: &[&str],
) -> Vec<(String, Vec<String>)> {
    let report = analyse_fixture_json(profile, extra);
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

/// Analyses the known fixture crate and returns the raw json report.
pub fn analyse_fixture_json(
    profile: &str,
    extra: &[&str],
) -> serde_json::Value {
    let exe = PathBuf::from(env!("CARGO_BIN_EXE_panicgraph"));
    let output = Command::new(&exe)
        .arg("--manifest-dir")
        .arg(fixture_dir())
        .arg("--profile")
        .arg(profile)
        .arg("--suppress")
        .arg("")
        .arg("--format")
        .arg("json")
        .args(extra)
        .output()
        .expect("the front end should run");
    serde_json::from_slice(&output.stdout).unwrap_or_else(|err| {
        panic!(
            "the report should be json: {err}\n{}",
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

/// Where the known fixture crate lives.
pub fn fixture_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("known")
}
