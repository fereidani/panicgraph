//! The suppression-aware reachability solver.
//!
//! Suppressing a category does not hide findings, it assumes the panic cannot
//! happen. That assumption has to be applied before propagation, because a
//! caller that only panics through a suppressed callee is genuinely clean, and
//! it has to reach into control flow, because a cleanup block that is only
//! reachable while a suppressed panic unwinds is unreachable too.

use std::collections::VecDeque;

use anyhow::{Result, ensure};

use crate::{
    category::{ALL, Category, CategorySet, Termination},
    graph::{FuncId, Graph},
    model::{Body, CallSite, Guard, UnwindOrigin},
};

/// What the user wants assumed impossible.
#[derive(Debug, Clone, Copy)]
pub struct Policy {
    /// Categories treated as though they cannot occur.
    pub suppressed: CategorySet,
    /// Whether to follow edges that are candidates rather than exact, namely
    /// vtable and function pointer calls.
    pub follow_inexact: bool,
}

impl Default for Policy {
    fn default() -> Self {
        Self {
            suppressed: CategorySet::oom(),
            follow_inexact: true,
        }
    }
}

/// The solved state of one function.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct NodeState {
    /// Categories this function can raise, after suppression.
    pub enabled: CategorySet,
    /// Whether this function can unwind into its caller's cleanup blocks.
    pub unwinds: bool,
}

/// Which sites and calls of one body are reachable under a policy.
#[derive(Debug, Clone, Default)]
pub struct Activity {
    /// Reachability of each entry in [`Body::sites`].
    pub sites: Vec<bool>,
    /// Reachability of each entry in [`Body::calls`].
    pub calls: Vec<bool>,
}

/// Shared evaluation logic, used both while solving and while explaining.
struct Eval<'a> {
    graph: &'a Graph,
    policy: Policy,
    states: &'a [NodeState],
}

impl Eval<'_> {
    /// The state a target the analysis cannot read contributes.
    const fn unreadable(&self, category: Category) -> NodeState {
        let enabled =
            CategorySet::single(category).difference(self.policy.suppressed);
        NodeState {
            enabled,
            unwinds: !enabled.is_empty(),
        }
    }

    /// Computes one function's state from the current state of its callees.
    fn evaluate(&self, id: FuncId) -> NodeState {
        let body = self.graph.body(id);
        if body.opaque {
            // An opaque body is unknown, not proven clean. Foreign code is
            // named apart: it has no Rust body to read and no fuller
            // standard library would produce one.
            return self.unreadable(if body.foreign {
                Category::Foreign
            } else {
                Category::Unknown
            });
        }

        let activity = self.activity(body);
        let mut state = NodeState::default();

        for (i, site) in body.sites.iter().enumerate() {
            if !activity.sites[i]
                || self.policy.suppressed.contains(site.category)
            {
                continue;
            }
            state.enabled.insert(site.category);
            state.unwinds |= site.termination == Termination::Unwind;
        }

        for (i, call) in body.calls.iter().enumerate() {
            if !activity.calls[i] || !self.follows(call) {
                continue;
            }
            let callee = self.callee_state(call);
            state.enabled = state.enabled.union(callee.enabled);
            state.unwinds |= callee.unwinds;
        }

        state
    }

    /// Determines which sites and calls of a body are reachable.
    ///
    /// Ordinary control flow is reachable unconditionally. Cleanup paths are
    /// reachable only while the panic that unwinds into them is enabled, so
    /// this runs to a local fixpoint.
    fn activity(&self, body: &Body) -> Activity {
        let mut act = Activity {
            sites: vec![false; body.sites.len()],
            calls: vec![false; body.calls.len()],
        };
        // Each productive round sets at least one flag, and flags never
        // clear, so the number of flags bounds the number of rounds.
        let rounds = body.sites.len() + body.calls.len();
        for _ in 0..=rounds {
            let mut changed = false;
            for i in 0..body.sites.len() {
                if !act.sites[i]
                    && self.guard_live(&body.sites[i].guard, body, &act)
                {
                    act.sites[i] = true;
                    changed = true;
                }
            }
            for i in 0..body.calls.len() {
                if !act.calls[i]
                    && self.guard_live(&body.calls[i].guard, body, &act)
                {
                    act.calls[i] = true;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        act
    }

    /// Evaluates a reachability guard against the current local activity.
    fn guard_live(&self, guard: &Guard, body: &Body, act: &Activity) -> bool {
        if guard.normal {
            return true;
        }
        guard.origins.iter().any(|origin| match *origin {
            UnwindOrigin::Site(i) => {
                let i = i as usize;
                body.sites.get(i).is_some_and(|site| {
                    act.sites[i]
                        && site.termination == Termination::Unwind
                        && !self.policy.suppressed.contains(site.category)
                })
            }
            UnwindOrigin::Call(i) => {
                let i = i as usize;
                body.calls.get(i).is_some_and(|call| {
                    act.calls[i]
                        && self.follows(call)
                        && self.callee_state(call).unwinds
                })
            }
        })
    }

    /// Whether the policy admits this edge.
    const fn follows(&self, call: &CallSite) -> bool {
        self.policy.follow_inexact || call.kind.is_exact()
    }

    /// The current state of a call's target.
    fn callee_state(&self, call: &CallSite) -> NodeState {
        let Some(key) = &call.callee else {
            // An unresolved target is unknown, and unknown code may unwind.
            return self.unreadable(Category::Unknown);
        };
        self.graph
            .id_of(key)
            .map_or_else(NodeState::default, |id| self.states[id.index()])
    }
}

/// The result of solving a graph under one policy.
#[derive(Debug)]
pub struct Solution {
    states: Vec<NodeState>,
    policy: Policy,
}

impl Solution {
    /// The categories a function can raise under the solved policy.
    #[must_use]
    pub fn enabled(&self, id: FuncId) -> CategorySet {
        self.states[id.index()].enabled
    }

    /// Whether a function can unwind under the solved policy.
    #[must_use]
    pub fn unwinds(&self, id: FuncId) -> bool {
        self.states[id.index()].unwinds
    }

    /// Whether a function raises nothing the user asked to see.
    #[must_use]
    pub fn is_clean(&self, id: FuncId) -> bool {
        self.states[id.index()].enabled.is_empty()
    }

    /// The policy this solution was produced under.
    #[must_use]
    pub const fn policy(&self) -> Policy {
        self.policy
    }

    /// Which sites and calls of a function are reachable under the policy.
    #[must_use]
    pub fn activity(&self, graph: &Graph, id: FuncId) -> Activity {
        let eval = Eval {
            graph,
            policy: self.policy,
            states: &self.states,
        };
        eval.activity(graph.body(id))
    }

    /// Whether the policy admits an edge.
    #[must_use]
    pub const fn follows(&self, call: &CallSite) -> bool {
        self.policy.follow_inexact || call.kind.is_exact()
    }
}

/// Solves a graph under one suppression policy.
pub struct Solver<'g> {
    graph: &'g Graph,
    policy: Policy,
    states: Vec<NodeState>,
}

impl<'g> Solver<'g> {
    /// Prepares a solver over `graph`.
    #[must_use]
    pub fn new(graph: &'g Graph, policy: Policy) -> Self {
        Self {
            graph,
            policy,
            states: vec![NodeState::default(); graph.len()],
        }
    }

    /// Runs the fixpoint to convergence.
    ///
    /// # Errors
    ///
    /// Returns an error if the iteration bound is exceeded, which would mean
    /// the transfer function stopped being monotone.
    pub fn solve(mut self) -> Result<Solution> {
        let n = self.graph.len();
        let mut queued = vec![true; n];
        let mut queue: VecDeque<FuncId> = (0..n)
            .map(|i| FuncId(u32::try_from(i).unwrap_or(u32::MAX)))
            .collect();

        // Termination: a node's state only ever grows, since categories are
        // added and never removed and `unwinds` only moves from false to
        // true. Each accepted update therefore consumes at least one of the
        // finitely many bits, giving the bound below.
        let bound = n.saturating_mul(ALL.len() + 1).saturating_add(1);
        let mut updates = 0usize;

        while let Some(id) = queue.pop_front() {
            queued[id.index()] = false;
            let next = {
                let eval = Eval {
                    graph: self.graph,
                    policy: self.policy,
                    states: &self.states,
                };
                eval.evaluate(id)
            };
            if next == self.states[id.index()] {
                continue;
            }
            self.states[id.index()] = next;
            updates += 1;
            ensure!(
                updates <= bound,
                "panic propagation failed to converge after {updates} \
                 updates over {n} functions"
            );
            for &caller in self.graph.callers(id) {
                if !queued[caller.index()] {
                    queued[caller.index()] = true;
                    queue.push_back(caller);
                }
            }
        }

        Ok(Solution {
            states: self.states,
            policy: self.policy,
        })
    }
}
