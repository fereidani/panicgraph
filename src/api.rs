//! JSON payloads served to the interactive view.
//!
//! The browser is a pure view. Every question it asks is answered by the same
//! solver the command line uses, so there is exactly one implementation of
//! the suppression semantics.

use std::path::Path;

use anyhow::{Context, Result, bail};
use serde_json::{Value, json};

use crate::{
    Category, CategorySet, FuncId, Graph, Solution, Solver, Terminal,
    category::ALL,
    solve::Policy,
    util::{Map, Set},
    witness,
};

/// Largest source file the view will fetch, to keep a stray request from
/// reading something enormous into memory.
const MAX_SOURCE_BYTES: u64 = 4 * 1024 * 1024;

/// The static shape of the graph, sent once.
#[must_use]
pub fn graph(graph: &Graph) -> Value {
    let nodes: Vec<Value> = graph
        .iter()
        .map(|(id, body)| {
            json!({
                "id": id.index(),
                "display": body.display,
                "krate": body.krate,
                "loc": body.loc.as_ref().map(ToString::to_string),
                "local": body.local,
                "opaque": body.opaque,
                "sites": sites(graph, id),
                "calls": calls(graph, id),
            })
        })
        .collect();

    json!({
        "config": graph.config(),
        "categories": ALL
            .iter()
            .map(|c| json!({ "name": c.name(), "describe": c.describe() }))
            .collect::<Vec<_>>(),
        "nodes": nodes,
    })
}

/// The panic sites of one function.
fn sites(graph: &Graph, id: FuncId) -> Vec<Value> {
    graph
        .body(id)
        .sites
        .iter()
        .map(|s| {
            json!({
                "category": s.category.name(),
                "termination": format!("{:?}", s.termination),
                "reason": s.reason,
                "sink": s.sink,
                "loc": s.loc.as_ref().map(ToString::to_string),
                "cleanup": !s.guard.normal,
            })
        })
        .collect()
}

/// The outgoing edges of one function.
fn calls(graph: &Graph, id: FuncId) -> Vec<Value> {
    graph
        .body(id)
        .calls
        .iter()
        .map(|c| {
            let to = c.callee.as_ref().and_then(|k| graph.id_of(k));
            json!({
                "to": to.map(FuncId::index),
                "display": c.callee_display,
                "kind": c.kind.name(),
                "loc": c.loc.as_ref().map(ToString::to_string),
                "cleanup": !c.guard.normal,
            })
        })
        .collect()
}

/// Runs the solver under one policy and reports the result.
///
/// # Errors
///
/// Returns an error if the fixpoint does not converge.
pub fn solve(
    g: &Graph,
    suppressed: CategorySet,
    follow_inexact: bool,
) -> Result<Value> {
    let policy = Policy {
        suppressed,
        follow_inexact,
    };
    let solution = Solver::new(g, policy).solve()?;

    let nodes: Vec<Value> = g
        .iter()
        .map(|(id, _)| {
            json!({
                "id": id.index(),
                "categories": solution
                    .enabled(id)
                    .iter()
                    .map(Category::name)
                    .collect::<Vec<_>>(),
                "unwinds": solution.unwinds(id),
            })
        })
        .collect();

    let dirty = local_dirty(g, &solution);
    Ok(json!({
        "suppressed": suppressed.iter().map(Category::name).collect::<Vec<_>>(),
        "nodes": nodes,
        "summary": {
            "analysed": g.len(),
            "can_panic": dirty,
            "clean_by_suppression": clean_by_suppression(g, &solution)?,
        },
        "counterfactual": counterfactual(g, suppressed, follow_inexact, dirty)?,
    }))
}

/// How many local functions can panic under a solution.
fn local_dirty(g: &Graph, solution: &Solution) -> usize {
    g.iter()
        .filter(|(_, b)| b.local && !b.opaque)
        .filter(|(id, _)| !solution.is_clean(*id))
        .count()
}

/// How many local functions are clean only because of the current policy.
fn clean_by_suppression(g: &Graph, solution: &Solution) -> Result<usize> {
    let bare = Solver::new(
        g,
        Policy {
            suppressed: CategorySet::EMPTY,
            follow_inexact: solution.policy().follow_inexact,
        },
    )
    .solve()?;
    Ok(g.iter()
        .filter(|(_, b)| b.local && !b.opaque)
        .filter(|(id, _)| solution.is_clean(*id) && !bare.is_clean(*id))
        .count())
}

/// The marginal effect of each category on the result.
///
/// This is the number the user is actually reasoning about: not how many
/// panic sites a category has, but how many functions it moves. For a
/// category that is not suppressed, that is how many functions would stop
/// being interesting if it were. For one that is already suppressed, it is
/// how many functions the assumption is currently clearing, which is the same
/// quantity measured from the other side.
fn counterfactual(
    g: &Graph,
    suppressed: CategorySet,
    follow_inexact: bool,
    baseline: usize,
) -> Result<Vec<Value>> {
    let mut out = Vec::with_capacity(ALL.len());
    for category in ALL {
        let sites = g
            .iter()
            .flat_map(|(_, b)| b.sites.iter())
            .filter(|s| s.category == category)
            .count();
        let alternative = if suppressed.contains(category) {
            suppressed.difference(CategorySet::single(category))
        } else {
            suppressed.union(CategorySet::single(category))
        };
        let policy = Policy {
            suppressed: alternative,
            follow_inexact,
        };
        let solution = Solver::new(g, policy).solve()?;
        let other = local_dirty(g, &solution);
        let cleared = if suppressed.contains(category) {
            other.saturating_sub(baseline)
        } else {
            baseline.saturating_sub(other)
        };
        out.push(json!({
            "category": category.name(),
            "sites": sites,
            "functions_cleared": cleared,
            "suppressed": suppressed.contains(category),
        }));
    }
    Ok(out)
}

/// A shortest call path from one function to a reachable panic.
///
/// # Errors
///
/// Returns an error if the fixpoint does not converge or the arguments name
/// something that is not in the graph.
pub fn why(
    g: &Graph,
    node: usize,
    category: &str,
    suppressed: CategorySet,
    follow_inexact: bool,
) -> Result<Value> {
    let Ok(category) = category.parse::<Category>() else {
        bail!("unknown panic category `{category}`");
    };
    if node >= g.len() {
        bail!("no function with index {node}");
    }
    let root = FuncId(u32::try_from(node).unwrap_or(u32::MAX));
    let policy = Policy {
        suppressed,
        follow_inexact,
    };
    let solution = Solver::new(g, policy).solve()?;

    let Some(path) = witness::find(g, &solution, root, category) else {
        return Ok(json!({ "found": false }));
    };
    let hops: Vec<Value> = path
        .hops
        .iter()
        .map(|h| {
            json!({
                "from": h.caller.index(),
                "to": h.callee.index(),
                "from_display": g.body(h.caller).display,
                "to_display": g.body(h.callee).display,
                "kind": h.kind.name(),
                "cleanup": h.cleanup,
                "loc": h.loc.as_ref().map(ToString::to_string),
            })
        })
        .collect();

    Ok(json!({
        "found": true,
        "category": category.name(),
        "root": g.body(root).display,
        "hops": hops,
        "func": path.func.index(),
        "func_display": g.body(path.func).display,
        "terminal": terminal(g, &path),
    }))
}

/// Describes where a witness path ends.
fn terminal(g: &Graph, path: &witness::Witness) -> Value {
    let body = g.body(path.func);
    match path.terminal {
        Terminal::Site(i) => body.sites.get(i).map_or_else(
            || json!({ "kind": "site" }),
            |s| {
                json!({
                    "kind": "site",
                    "category": s.category.name(),
                    "reason": s.reason,
                    "sink": s.sink,
                    "loc": s.loc.as_ref().map(ToString::to_string),
                })
            },
        ),
        Terminal::Opaque => json!({
            "kind": "opaque",
            "reason": "no MIR available, so panics here are unknown",
        }),
        Terminal::Unresolved(i) => body.calls.get(i).map_or_else(
            || json!({ "kind": "unresolved" }),
            |c| {
                json!({
                    "kind": "unresolved",
                    "display": c.callee_display,
                    "edge": c.kind.name(),
                    "loc": c.loc.as_ref().map(ToString::to_string),
                })
            },
        ),
    }
}

/// A prefix tree of every witness path in the crate.
///
/// Merging the shortest path from each local function to each panic it can
/// reach produces exactly the shape of a flame graph: width is the number of
/// reachable panics, depth is call depth. Returned flat, with parent links,
/// so the view can build the hierarchy without this code recursing.
///
/// # Errors
///
/// Returns an error if the fixpoint does not converge.
pub fn flame(
    g: &Graph,
    suppressed: CategorySet,
    follow_inexact: bool,
    fold: bool,
) -> Result<Value> {
    let rows = flame_rows(g, suppressed, follow_inexact, fold)?;
    let nodes: Vec<Value> = rows
        .iter()
        .map(|row| {
            json!({
                "id": row.id,
                "parent": row.parent,
                "name": row.name,
                "category": row.category,
                "kind": row.kind,
                "cleanup": row.cleanup,
                "elided": row.elided,
                "value": row.value,
            })
        })
        .collect();
    Ok(json!({ "nodes": nodes }))
}

/// One frame of the tree.
#[derive(Debug, Clone)]
pub struct FlameRow {
    /// Position in the returned list.
    pub id: usize,
    /// The frame this one sits under.
    pub parent: Option<usize>,
    /// What to write on it.
    pub name: String,
    /// Set when the frame is a panic rather than a call.
    pub category: Option<&'static str>,
    /// How the call was resolved, or the kind of ending.
    pub kind: &'static str,
    /// Whether it runs only while an earlier panic unwinds.
    pub cleanup: bool,
    /// Calls folded into this frame.
    pub elided: Vec<String>,
    /// Panics ending here, for a leaf.
    pub value: usize,
}

/// Builds the tree, optionally folding runs of single calls.
///
/// # Errors
///
/// Returns an error if the fixpoint does not converge.
pub fn flame_rows(
    g: &Graph,
    suppressed: CategorySet,
    follow_inexact: bool,
    fold: bool,
) -> Result<Vec<FlameRow>> {
    let policy = Policy {
        suppressed,
        follow_inexact,
    };
    let solution = Solver::new(g, policy).solve()?;

    let mut tree = Tree::new();
    for (id, body) in g.iter() {
        if !body.local || body.opaque {
            continue;
        }
        for category in solution.enabled(id).iter() {
            let Some(path) = witness::find(g, &solution, id, category) else {
                continue;
            };
            tree.insert(g, id, &path, category);
        }
    }
    let rows = tree.finish();
    Ok(if fold { fold_chains(&rows) } else { rows })
}

/// Frames that stand for a call rather than a module or a panic.
const EDGE_KINDS: [&str; 5] =
    ["static", "drop", "vtable", "fn-ptr", "unresolved"];

/// Folds runs of single calls into the frame above them.
///
/// Most of the tree is a chain rather than a fan, and a run of frames that
/// each call exactly one thing says only "and then it called this". Folding
/// them keeps every ending, so nothing the graph claims is lost.
#[must_use]
pub fn fold_chains(rows: &[FlameRow]) -> Vec<FlameRow> {
    let mut children: Map<usize, Vec<usize>> = Map::default();
    for row in rows {
        if let Some(parent) = row.parent {
            children.entry(parent).or_default().push(row.id);
        }
    }

    let mut kept: Vec<FlameRow> = Vec::new();
    let mut remap: Map<usize, usize> = Map::default();
    let mut stack = vec![(0usize, None::<usize>, Vec::<String>::new())];
    // Every frame is visited at most once, so this ends within the input.
    while let Some((id, parent, mut elided)) = stack.pop() {
        let mut kids = children.get(&id).cloned().unwrap_or_default();
        for _ in 0..rows.len() {
            if kids.len() != 1 {
                break;
            }
            let only = kids[0];
            let row = &rows[only];
            let grand = children.get(&only).cloned().unwrap_or_default();
            if row.category.is_some()
                || !EDGE_KINDS.contains(&row.kind)
                || grand.is_empty()
            {
                break;
            }
            elided.push(row.name.clone());
            kids = grand;
        }
        let new_id = kept.len();
        remap.insert(id, new_id);
        let mut row = rows[id].clone();
        row.id = new_id;
        row.parent = parent;
        row.elided = elided;
        kept.push(row);
        for kid in kids {
            stack.push((kid, Some(new_id), Vec::new()));
        }
    }
    kept
}

/// Accumulates witness paths into a prefix tree held in a flat vector.
struct Tree {
    names: Vec<String>,
    parents: Vec<Option<usize>>,
    categories: Vec<Option<&'static str>>,
    kinds: Vec<&'static str>,
    values: Vec<usize>,
    cleanup: Vec<bool>,
    index: Map<(Option<usize>, String), usize>,
}

impl Tree {
    fn new() -> Self {
        let mut tree = Self {
            names: Vec::new(),
            parents: Vec::new(),
            categories: Vec::new(),
            kinds: Vec::new(),
            values: Vec::new(),
            cleanup: Vec::new(),
            index: Map::default(),
        };
        tree.node(None, "crate".to_owned(), None, "root");
        tree
    }

    /// Finds or creates one child.
    fn node(
        &mut self,
        parent: Option<usize>,
        name: String,
        category: Option<&'static str>,
        kind: &'static str,
    ) -> usize {
        let key = (parent, name.clone());
        if let Some(&existing) = self.index.get(&key) {
            return existing;
        }
        let id = self.names.len();
        self.names.push(name);
        self.parents.push(parent);
        self.categories.push(category);
        self.kinds.push(kind);
        self.values.push(0);
        self.cleanup.push(false);
        self.index.insert(key, id);
        id
    }

    /// Adds one witness path, incrementing the count along its length.
    fn insert(
        &mut self,
        g: &Graph,
        root: FuncId,
        path: &witness::Witness,
        category: Category,
    ) {
        // Nest the root under its module path. Without this the first row is
        // one sliver per function, which carries no shape; with it the row is
        // a handful of crates that can actually be read and zoomed into.
        let display = &g.body(root).display;
        let segments = split_path(display);
        let mut at = 0usize;
        let last = segments.len().saturating_sub(1);
        for (i, segment) in segments.iter().enumerate() {
            let kind = if i == last { "function" } else { "module" };
            at = self.node(Some(at), segment.clone(), None, kind);
            self.values[at] += 1;
        }
        for hop in &path.hops {
            let name = g.body(hop.callee).display.clone();
            at = self.node(Some(at), name, None, hop.kind.name());
            self.values[at] += 1;
            if hop.cleanup {
                self.cleanup[at] = true;
            }
        }
        let leaf = match path.terminal {
            Terminal::Site(_) => "site",
            Terminal::Opaque => "opaque",
            Terminal::Unresolved(_) => "unresolved",
        };
        let at = self.node(
            Some(at),
            category.name().to_owned(),
            Some(category.name()),
            leaf,
        );
        self.values[at] += 1;
    }

    /// Emits the tree as flat records with parent links.
    fn finish(self) -> Vec<FlameRow> {
        (0..self.names.len())
            .map(|i| FlameRow {
                id: i,
                parent: self.parents[i],
                name: self.names[i].clone(),
                category: self.categories[i],
                kind: self.kinds[i],
                cleanup: self.cleanup[i],
                elided: Vec::new(),
                value: self.values[i],
            })
            .collect()
    }
}

/// Splits a display path on its module separators.
///
/// Generic arguments carry their own separators, so a naive split would cut
/// `Vec<alloc::string::String>` into pieces. Only separators outside angle
/// brackets divide the path.
fn split_path(display: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut depth = 0i32;
    let mut chars = display.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '<' => {
                depth += 1;
                current.push(c);
            }
            '>' => {
                depth -= 1;
                current.push(c);
            }
            ':' if depth == 0 && chars.peek() == Some(&':') => {
                chars.next();
                if !current.is_empty() {
                    parts.push(std::mem::take(&mut current));
                }
            }
            _ => current.push(c),
        }
    }
    if !current.is_empty() {
        parts.push(current);
    }
    if parts.is_empty() {
        parts.push(display.to_owned());
    }
    parts
}

/// Every source file the graph refers to.
///
/// The view may only read files in this set. Serving an arbitrary path would
/// turn a local analysis tool into a way to read the whole filesystem.
#[must_use]
pub fn source_allowlist(g: &Graph) -> Set<String> {
    let mut out = Set::default();
    for (_, body) in g.iter() {
        let locs = body
            .loc
            .iter()
            .chain(body.sites.iter().filter_map(|s| s.loc.as_ref()))
            .chain(body.calls.iter().filter_map(|c| c.loc.as_ref()));
        for loc in locs {
            out.insert(loc.file.clone());
        }
    }
    out
}

/// Reads one source file, if the graph refers to it.
///
/// # Errors
///
/// Returns an error if the file is not referenced by the analysis, is too
/// large, or cannot be read.
pub fn source(allowed: &Set<String>, file: &str) -> Result<Value> {
    if !allowed.contains(file) {
        bail!("`{file}` is not referenced by this analysis");
    }
    let path = Path::new(file);
    let meta = std::fs::metadata(path)
        .with_context(|| format!("could not stat {file}"))?;
    if meta.len() > MAX_SOURCE_BYTES {
        bail!("`{file}` is larger than this view will load");
    }
    let text = std::fs::read_to_string(path)
        .with_context(|| format!("could not read {file}"))?;
    Ok(json!({ "file": file, "text": text }))
}
