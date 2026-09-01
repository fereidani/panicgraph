//! JSON payloads served to the interactive view.
//!
//! The browser is a pure view. Every question it asks is answered by the same
//! solver the command line uses, so there is exactly one implementation of
//! the suppression semantics.

use std::{fs::File, io::Read};

use anyhow::{Context, Result, bail};
use serde::Serialize;
use serde_json::{Value, json};

use crate::{
    Body, Category, CategorySet, FuncId, Graph, Solution, Solver, Terminal,
    category::ALL,
    solve::{Edges, Policy},
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
                "sites": sites(body),
                "calls": calls(graph, body),
            })
        })
        .collect();

    json!({
        "config": graph.config(),
        "categories": ALL
            .iter()
            .map(|c| {
                json!({
                    "name": c.name(),
                    "describe": c.describe(),
                    // Whether the name stands for a panic or for a place
                    // the analysis could not read. The view separates the
                    // two, since an unread call is not a finding.
                    "assumed": CategorySet::assumed().contains(*c),
                })
            })
            .collect::<Vec<_>>(),
        "nodes": nodes,
    })
}

/// The panic sites of one function.
fn sites(body: &Body) -> Vec<Value> {
    body.sites
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
fn calls(graph: &Graph, body: &Body) -> Vec<Value> {
    body.calls
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

/// Solves the graph under the policy a request describes.
fn solved(
    g: &Graph,
    suppressed: CategorySet,
    edges: Edges,
) -> Result<Solution> {
    Solver::new(g, Policy { suppressed, edges }).solve()
}

/// Runs the solver under one policy and reports the result.
///
/// # Errors
///
/// Returns an error if the fixpoint does not converge.
pub fn solve(
    g: &Graph,
    suppressed: CategorySet,
    edges: Edges,
) -> Result<Value> {
    let solution = solved(g, suppressed, edges)?;

    let nodes: Vec<Value> = g
        .iter()
        .map(|(id, _)| {
            json!({
                "id": id.index(),
                "categories": solution
                    .enabled(id).names(),
                "unwinds": solution.unwinds(id),
            })
        })
        .collect();

    let dirty = local_dirty(g, &solution);
    Ok(json!({
        "suppressed": suppressed.names(),
        "nodes": nodes,
        "summary": {
            "analysed": g.len(),
            "can_panic": dirty,
            "clean_by_suppression": solution.cleared_by_suppression(g)?,
        },
        "counterfactual": counterfactual(g, &solution, dirty)?,
    }))
}

/// How many local functions can panic under a solution.
fn local_dirty(g: &Graph, solution: &Solution) -> usize {
    g.locals().filter(|(id, _)| !solution.is_clean(*id)).count()
}

/// How many local functions reach one category under a solution.
fn local_reaching(g: &Graph, solution: &Solution, kind: Category) -> usize {
    g.locals()
        .filter(|(id, _)| solution.enabled(*id).contains(kind))
        .count()
}

/// The reach and the marginal effect of each category on the result.
///
/// Two different questions, and a category can answer them differently.
/// `functions_reaching` is whether the category occurs here at all.
/// `functions_cleared` is how many functions it alone is keeping
/// interesting: for a category that is not suppressed, how many would stop
/// being reported if it were, and for one already suppressed, how many the
/// assumption is currently clearing, which is the same quantity measured
/// from the other side. A category every one of whose functions also reaches
/// something else clears nobody while still reaching plenty, so a reader
/// told only the second number would conclude it is not here.
///
/// `sites` counts the panics the driver wrote down, which is zero for the
/// categories the solver synthesizes for a body it cannot read.
fn counterfactual(
    g: &Graph,
    solution: &Solution,
    baseline: usize,
) -> Result<Vec<Value>> {
    let policy = solution.policy();
    let mut out = Vec::with_capacity(ALL.len());
    for category in ALL {
        let sites = g
            .iter()
            .flat_map(|(_, b)| b.sites.iter())
            .filter(|s| s.category == category)
            .count();
        let assumed = policy.suppressed.contains(category);
        let alternative = if assumed {
            policy.suppressed.difference(CategorySet::single(category))
        } else {
            policy.suppressed.union(CategorySet::single(category))
        };
        let other_solution = solved(g, alternative, policy.edges)?;
        let other = local_dirty(g, &other_solution);
        let cleared = if assumed {
            other.saturating_sub(baseline)
        } else {
            baseline.saturating_sub(other)
        };
        // A category the policy assumes impossible reaches nothing by
        // construction, so what it would reach is read from the solution
        // that puts it back.
        let reaching = if assumed {
            local_reaching(g, &other_solution, category)
        } else {
            local_reaching(g, solution, category)
        };
        out.push(json!({
            "category": category.name(),
            "sites": sites,
            "functions_reaching": reaching,
            "functions_cleared": cleared,
            "suppressed": assumed,
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
    edges: Edges,
) -> Result<Value> {
    let Ok(category) = category.parse::<Category>() else {
        bail!("unknown panic category `{category}`");
    };
    if node >= g.len() {
        bail!("no function with index {node}");
    }
    let root = FuncId::from_index(node);
    let solution = solved(g, suppressed, edges)?;

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
        // Foreign code is named apart, as the printed report does: no
        // fuller standard library will ever produce a body for it, so
        // sending the reader off to rebuild one would waste their time.
        Terminal::Opaque if body.foreign => json!({
            "kind": "opaque",
            "reason": "foreign code, which has no Rust body to read",
        }),
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
    edges: Edges,
    fold: bool,
) -> Result<Value> {
    let rows = flame_rows(g, suppressed, edges, fold)?;
    Ok(json!({ "nodes": rows }))
}

/// One frame of the tree.
///
/// The field names are the keys the view reads, so the frame serializes as
/// itself.
#[derive(Debug, Clone, Serialize)]
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
    edges: Edges,
    fold: bool,
) -> Result<Vec<FlameRow>> {
    let solution = solved(g, suppressed, edges)?;
    let mut tree = Tree::new();
    for (id, _) in g.locals() {
        for category in solution.enabled(id).iter() {
            let Some(path) = witness::find(g, &solution, id, category) else {
                continue;
            };
            tree.insert(g, id, &path, category);
        }
    }
    let rows = tree.rows;
    Ok(if fold { fold_chains(&rows) } else { rows })
}

/// The frames sitting directly under each frame, by identifier.
#[must_use]
pub fn children_of(rows: &[FlameRow]) -> Map<usize, Vec<usize>> {
    let mut children: Map<usize, Vec<usize>> = Map::default();
    for row in rows {
        if let Some(parent) = row.parent {
            children.entry(parent).or_default().push(row.id);
        }
    }
    children
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
    let children = children_of(rows);
    let mut kept: Vec<FlameRow> = Vec::new();
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
    rows: Vec<FlameRow>,
    index: Map<(Option<usize>, String), usize>,
}

impl Tree {
    fn new() -> Self {
        let mut tree = Self {
            rows: Vec::new(),
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
        let id = self.rows.len();
        self.rows.push(FlameRow {
            id,
            parent,
            name,
            category,
            kind,
            cleanup: false,
            elided: Vec::new(),
            value: 0,
        });
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
            self.rows[at].value += 1;
        }
        for hop in &path.hops {
            let name = g.body(hop.callee).display.clone();
            at = self.node(Some(at), name, None, hop.kind.name());
            self.rows[at].value += 1;
            self.rows[at].cleanup |= hop.cleanup;
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
        self.rows[at].value += 1;
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
    // Read through one handle and stop a byte past the limit. Asking the
    // filesystem for a size and reading afterwards measures a file that
    // need not be the one that arrives.
    let mut raw = Vec::new();
    File::open(file)
        .with_context(|| format!("could not read {file}"))?
        .take(MAX_SOURCE_BYTES + 1)
        .read_to_end(&mut raw)
        .with_context(|| format!("could not read {file}"))?;
    if u64::try_from(raw.len()).unwrap_or(u64::MAX) > MAX_SOURCE_BYTES {
        bail!("`{file}` is larger than this view will load");
    }
    let text = String::from_utf8(raw)
        .with_context(|| format!("`{file}` is not valid utf-8"))?;
    Ok(json!({ "file": file, "text": text }))
}
