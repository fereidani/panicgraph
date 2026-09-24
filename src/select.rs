//! Which functions a rendering names, and under what names.
//!
//! Every rendering of the analysis, the report, the gate and the drawing,
//! answers the same question about each function: does it show, and under
//! what name? The answer depends on the policy flags, and it has to be the
//! same everywhere, or a function reported under one name would be drawn
//! under another, or drawn where the report leaves it out. So the rules
//! live here, once.

use crate::{
    Body, CategorySet, FuncId, Graph,
    args::{Closures, Generics},
    util::Map,
};

/// Which functions show, and under what names.
#[derive(Debug, Clone, Copy)]
pub struct Selection {
    /// Functions from dependencies as well as the local crate.
    pub all_crates: bool,
    /// How closures are named.
    pub closures: Closures,
    /// How generic functions report.
    pub generics: Generics,
    /// When set, the only categories shown.
    pub only: Option<CategorySet>,
}

impl Default for Selection {
    /// The local crate, closures as their own functions, generic functions
    /// as written, and every category.
    fn default() -> Self {
        Self {
            all_crates: false,
            closures: Closures::Separate,
            generics: Generics::Written,
            only: None,
        }
    }
}

/// What is known of a name once every body carrying it has been seen.
#[derive(Debug, Clone, Copy, Default)]
struct Named {
    /// Whether the crate's own build carries the name, rather than only a
    /// test target.
    owned: bool,
    /// Whether an instantiation carries the name, rather than only the
    /// body as written.
    instantiated: bool,
}

impl Selection {
    /// The name a body shows under.
    ///
    /// A closure is not an addressable function of the crate's own
    /// interface, so the parent view folds it into the function it is
    /// written in. The separate view stays the default because it is the
    /// precise one: a panic contained by a catch belongs to the closure,
    /// not to its caller.
    #[must_use]
    pub fn name<'a>(&self, body: &'a Body) -> &'a str {
        match self.closures {
            Closures::Separate => &body.display,
            Closures::Parent => body
                .display
                .split("::{closure")
                .next()
                .unwrap_or(&body.display),
        }
    }

    /// The categories of a function that show.
    #[must_use]
    pub fn shown(&self, enabled: CategorySet) -> CategorySet {
        self.only.map_or(enabled, |only| enabled.intersection(only))
    }

    /// Whether a body is read at all: it has one, and it is of the crates
    /// asked for.
    #[must_use]
    pub const fn admits(&self, body: &Body) -> bool {
        !body.opaque && (self.all_crates || body.local)
    }

    /// Every function that shows, in the graph's order.
    ///
    /// Bodies sharing a name are one function: a generic function is read
    /// as written and once per instantiation, and a test target adds
    /// instantiations under the crate's own names. A name only a test
    /// carries is a test, and shows nowhere. Under instantiated generics
    /// the body as written yields to the instantiations wherever there are
    /// any, so what shows is what the build's own uses of the function do.
    pub fn functions<'a>(
        &self,
        graph: &'a Graph,
    ) -> impl Iterator<Item = (FuncId, &'a Body)> + use<'a> {
        let selection = *self;
        let mut names: Map<(&str, &str), Named> = Map::default();
        for (_, body) in graph.iter().filter(|(_, body)| self.admits(body)) {
            let known = names
                .entry((body.krate.as_str(), self.name(body)))
                .or_default();
            known.owned |= !body.from_tests;
            known.instantiated |= !body.key.is_open();
        }
        graph.iter().filter(move |(_, body)| {
            selection.admits(body)
                && names
                    .get(&(body.krate.as_str(), selection.name(body)))
                    .is_some_and(|known| selection.keeps(body, *known))
        })
    }

    /// What each shown function raises across its bodies, keyed by crate and
    /// name, so a total counts functions the way the report does.
    pub fn raised<'a>(
        &self,
        graph: &'a Graph,
        enabled: impl Fn(FuncId) -> CategorySet,
    ) -> Map<(&'a str, &'a str), CategorySet> {
        let mut out: Map<(&str, &str), CategorySet> = Map::default();
        for (id, body) in self.functions(graph) {
            let held = out
                .entry((body.krate.as_str(), self.name(body)))
                .or_default();
            *held = held.union(self.shown(enabled(id)));
        }
        out
    }

    /// The bodies reported under the same name as `id`, with `id` first.
    ///
    /// The report merges a generic function's written body with its
    /// instantiations, and under `--closures parent` a function with its
    /// closures. A body the selection does not show matches every body of
    /// its name in the graph.
    #[must_use]
    pub fn namesakes(&self, graph: &Graph, id: FuncId) -> Vec<FuncId> {
        let body = graph.body(id);
        let named = |(_, other): &(FuncId, &Body)| {
            other.krate == body.krate && self.name(other) == self.name(body)
        };
        let mut ids: Vec<FuncId> = self
            .functions(graph)
            .filter(named)
            .map(|(at, _)| at)
            .collect();
        if ids.is_empty() {
            ids = graph.iter().filter(named).map(|(at, _)| at).collect();
        }
        ids.sort_by_key(|other| *other != id);
        ids
    }

    /// Whether one body of a name shows, given what is known of the name.
    fn keeps(&self, body: &Body, known: Named) -> bool {
        let yields = self.generics == Generics::Instantiated
            && known.instantiated
            && body.key.is_open();
        known.owned && !yields
    }
}
