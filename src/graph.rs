//! The merged call graph.
//!
//! The driver emits one [`Artifact`] per crate. Merging them yields a single
//! graph in which every function has a dense index, which keeps the solver's
//! state in flat vectors.

use crate::{
    model::{Artifact, Body, BuildConfig, CallSite, FuncKey, Reified},
    util::Map,
};

/// A dense index into [`Graph`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FuncId(pub u32);

impl FuncId {
    /// The index as a `usize`, for slicing.
    #[must_use]
    pub const fn index(self) -> usize {
        self.0 as usize
    }

    /// A dense index turned into an identifier.
    ///
    /// A graph that large cannot be built in the first place, so clamping is
    /// only here to keep the conversion total.
    #[must_use]
    pub fn from_index(index: usize) -> Self {
        Self(u32::try_from(index).unwrap_or(u32::MAX))
    }
}

/// A merged, indexed call graph.
#[derive(Debug)]
pub struct Graph {
    bodies: Vec<Body>,
    by_key: Map<FuncKey, FuncId>,
    callers: Vec<Vec<FuncId>>,
    config: Option<BuildConfig>,
}

impl Graph {
    /// Merges per-crate artifacts into one graph.
    ///
    /// A function may be observed more than once, because a generic body is
    /// instantiated in every crate that uses it. The richest record wins: a
    /// body with MIR always replaces an opaque placeholder.
    #[must_use]
    pub fn from_artifacts(artifacts: Vec<Artifact>) -> Self {
        let mut graph = Self {
            bodies: Vec::new(),
            by_key: Map::default(),
            callers: Vec::new(),
            config: None,
        };
        let mut reified: Vec<Reified> = Vec::new();
        for artifact in artifacts {
            if graph.config.is_none() {
                graph.config = Some(artifact.config.clone());
            }
            for body in artifact.bodies {
                graph.insert_body(body);
            }
            reified.extend(artifact.reified);
        }
        graph.expand_fn_pointers(&reified);
        graph.materialize_missing_callees();
        graph.build_reverse_edges();
        graph
    }

    /// Appends candidate edges for calls made through function pointers.
    ///
    /// A reachable function reified to a pointer of the right signature is
    /// what such a call could be. The edges are marked as candidates, so
    /// following them stays the caller's choice, and the unresolved edge
    /// stays alongside them either way.
    fn expand_fn_pointers(&mut self, reified: &[Reified]) {
        if reified.is_empty() {
            return;
        }
        for body in &mut self.bodies {
            let mut extra: Vec<CallSite> = Vec::new();
            for call in &body.calls {
                let Some(sig) = &call.sig else { continue };
                for target in reified {
                    if &target.sig != sig {
                        continue;
                    }
                    let mut candidate = call.clone();
                    candidate.callee = Some(target.key.clone());
                    candidate.callee_display.clone_from(&target.display);
                    candidate.candidate = true;
                    candidate.sig = None;
                    extra.push(candidate);
                }
            }
            body.calls.extend(extra);
        }
    }

    /// Adds or upgrades one body.
    fn insert_body(&mut self, body: Body) {
        if let Some(&id) = self.by_key.get(&body.key) {
            let existing = &mut self.bodies[id.index()];
            // A real body always beats a placeholder, whichever crate each
            // was seen in, and between two of a kind a local definition
            // beats a copy observed from a downstream crate.
            let upgrade = match (existing.opaque, body.opaque) {
                (true, false) => true,
                (false, true) => false,
                _ => !existing.local && body.local,
            };
            if upgrade {
                *existing = body;
            }
            return;
        }
        let id = FuncId::from_index(self.bodies.len());
        self.by_key.insert(body.key.clone(), id);
        self.bodies.push(body);
    }

    /// Creates opaque placeholders for callees nothing ever defined.
    fn materialize_missing_callees(&mut self) {
        let mut missing: Vec<(FuncKey, String)> = Vec::new();
        for body in &self.bodies {
            for call in &body.calls {
                if let Some(key) = &call.callee
                    && !self.by_key.contains_key(key)
                {
                    missing.push((key.clone(), call.callee_display.clone()));
                }
            }
        }
        for (key, display) in missing {
            if self.by_key.contains_key(&key) {
                continue;
            }
            let krate = display
                .split_once("::")
                .map_or_else(|| display.clone(), |(c, _)| c.to_owned());
            self.insert_body(Body::opaque(key, display, krate));
        }
    }

    /// Builds the caller index used to drive the solver's worklist.
    fn build_reverse_edges(&mut self) {
        self.callers = vec![Vec::new(); self.bodies.len()];
        for (i, body) in self.bodies.iter().enumerate() {
            let caller = FuncId::from_index(i);
            for call in &body.calls {
                let Some(key) = &call.callee else { continue };
                let Some(&target) = self.by_key.get(key) else {
                    continue;
                };
                let list = &mut self.callers[target.index()];
                if !list.contains(&caller) {
                    list.push(caller);
                }
            }
        }
    }

    /// The number of functions in the graph.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.bodies.len()
    }

    /// Returns whether the graph holds no functions.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.bodies.is_empty()
    }

    /// The body behind an index.
    #[must_use]
    pub fn body(&self, id: FuncId) -> &Body {
        &self.bodies[id.index()]
    }

    /// Every body, with its index.
    pub fn iter(&self) -> impl Iterator<Item = (FuncId, &Body)> {
        self.bodies
            .iter()
            .enumerate()
            .map(|(i, b)| (FuncId::from_index(i), b))
    }

    /// Looks a function up by key.
    #[must_use]
    pub fn id_of(&self, key: &FuncKey) -> Option<FuncId> {
        self.by_key.get(key).copied()
    }

    /// The functions that call `id`.
    #[must_use]
    pub fn callers(&self, id: FuncId) -> &[FuncId] {
        &self.callers[id.index()]
    }

    /// The build configuration the artifacts were produced under.
    #[must_use]
    pub const fn config(&self) -> Option<&BuildConfig> {
        self.config.as_ref()
    }

    /// Finds functions whose display path contains `needle`.
    ///
    /// Used to turn a user supplied name into an index without requiring the
    /// full mangled symbol. The closest match comes first: a path equal to
    /// the needle beats one that merely contains it, and a shorter path beats
    /// a longer one, so asking about `parse` explains `parse` rather than the
    /// closure inside it.
    #[must_use]
    pub fn find_by_display(&self, needle: &str) -> Vec<FuncId> {
        let mut out: Vec<FuncId> = self
            .iter()
            .filter(|(_, b)| b.display.contains(needle))
            .map(|(id, _)| id)
            .collect();
        out.sort_by(|a, b| {
            let (a, b) = (&self.bodies[a.index()], &self.bodies[b.index()]);
            (a.display != needle, a.display.len(), &a.display).cmp(&(
                b.display != needle,
                b.display.len(),
                &b.display,
            ))
        });
        out
    }
}
