//! Builders for the small graphs the solver tests run on.

use panicgraph::{
    Artifact, Body, BuildConfig, CallSite, Category, EdgeKind, FuncKey, Guard,
    PanicSite, StdMode, Termination, UnwindOrigin,
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
            Guard {
                normal: true,
                origins: Vec::new(),
            },
        ));
        self
    }

    /// Adds a call on the ordinary control flow path.
    pub fn calls(mut self, callee: &str) -> Self {
        self.body.calls.push(call(
            callee,
            Guard {
                normal: true,
                origins: Vec::new(),
            },
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
    }
}

/// Wraps bodies into the single artifact a graph is built from.
pub fn artifact(bodies: Vec<Body>) -> Artifact {
    Artifact {
        krate: "test".to_owned(),
        config: BuildConfig {
            rustc: "test".to_owned(),
            profile: "release".to_owned(),
            debug_assertions: false,
            overflow_checks: false,
            std_mode: StdMode::Shipped,
        },
        bodies,
    }
}
