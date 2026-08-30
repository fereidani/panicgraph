//! Shortest call path from a function to a panic it can reach.
//!
//! Paths are reconstructed on demand rather than stored during solving, which
//! keeps the solver's state to one word per function.

use std::collections::VecDeque;

use crate::{
    category::Category,
    graph::{FuncId, Graph},
    model::{EdgeKind, Loc},
    solve::Solution,
    util::Map,
};

/// One call in a witness path.
#[derive(Debug, Clone)]
pub struct Hop {
    /// The function making the call.
    pub caller: FuncId,
    /// The function being called.
    pub callee: FuncId,
    /// Where the call is written.
    pub loc: Option<Loc>,
    /// How the target was resolved.
    pub kind: EdgeKind,
    /// True when this call runs only while an earlier panic is unwinding.
    pub cleanup: bool,
}

/// What the end of a witness path actually is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Terminal {
    /// A panic raised directly by the function, by site index.
    Site(usize),
    /// The function has no recorded body, so its behaviour is unknown.
    Opaque,
    /// A call whose target could not be determined, by call index.
    Unresolved(usize),
}

/// A path from a root function to a reachable panic.
#[derive(Debug, Clone)]
pub struct Witness {
    /// The calls traversed, in order, from the root.
    pub hops: Vec<Hop>,
    /// The function the path ends at.
    pub func: FuncId,
    /// Why the path ends there.
    pub terminal: Terminal,
}

/// Finds a shortest path from `root` to a panic of `category`.
///
/// Returns `None` when the category is not reachable under the solution's
/// policy. Breadth first search gives the shortest path, which is the most
/// readable explanation.
#[must_use]
pub fn find(
    graph: &Graph,
    solution: &Solution,
    root: FuncId,
    category: Category,
) -> Option<Witness> {
    if !solution.enabled(root).contains(category) {
        return None;
    }

    let mut came_from: Map<FuncId, Hop> = Map::default();
    let mut seen = vec![false; graph.len()];
    let mut queue = VecDeque::new();
    seen[root.index()] = true;
    queue.push_back(root);

    // Every function enters the queue at most once, so the search visits at
    // most `graph.len()` nodes.
    while let Some(id) = queue.pop_front() {
        let body = graph.body(id);

        // A function with no recorded body is the source of an unknown.
        if body.opaque && category == Category::Unknown {
            return Some(Witness {
                hops: rebuild(&came_from, root, id),
                func: id,
                terminal: Terminal::Opaque,
            });
        }

        let activity = solution.activity(graph, id);

        for (i, site) in body.sites.iter().enumerate() {
            if activity.sites.get(i).copied().unwrap_or(false)
                && site.category == category
                && !solution.policy().suppressed.contains(category)
            {
                return Some(Witness {
                    hops: rebuild(&came_from, root, id),
                    func: id,
                    terminal: Terminal::Site(i),
                });
            }
        }

        if category == Category::Unknown {
            let unresolved = body.calls.iter().enumerate().find(|(i, call)| {
                call.callee.is_none()
                    && activity.calls.get(*i).copied().unwrap_or(false)
                    && solution.follows(call)
            });
            if let Some((i, _)) = unresolved {
                return Some(Witness {
                    hops: rebuild(&came_from, root, id),
                    func: id,
                    terminal: Terminal::Unresolved(i),
                });
            }
        }

        for (i, call) in body.calls.iter().enumerate() {
            if !activity.calls.get(i).copied().unwrap_or(false)
                || !solution.follows(call)
            {
                continue;
            }
            let Some(key) = &call.callee else { continue };
            let Some(next) = graph.id_of(key) else {
                continue;
            };
            if seen[next.index()] || !solution.enabled(next).contains(category)
            {
                continue;
            }
            seen[next.index()] = true;
            came_from.insert(
                next,
                Hop {
                    caller: id,
                    callee: next,
                    loc: call.loc.clone(),
                    kind: call.kind,
                    cleanup: !call.guard.normal,
                },
            );
            queue.push_back(next);
        }
    }

    None
}

/// Walks predecessor links back to the root and returns them in call order.
fn rebuild(
    came_from: &Map<FuncId, Hop>,
    root: FuncId,
    mut at: FuncId,
) -> Vec<Hop> {
    let mut hops = Vec::new();
    // Each step moves strictly closer to the root in the search tree, so the
    // number of predecessor links bounds the loop.
    for _ in 0..=came_from.len() {
        if at == root {
            break;
        }
        let Some(hop) = came_from.get(&at) else { break };
        hops.push(hop.clone());
        at = hop.caller;
    }
    hops.reverse();
    hops
}
