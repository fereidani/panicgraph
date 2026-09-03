//! Verification of findings against the compiled artifact.
//!
//! The analysis reads MIR, which is what the program means; the artifact is
//! what the optimizer kept. A check the folder could not settle is often
//! settled by the optimizer anyway, so each finding is looked up in the
//! compiled code: a panic entry point still reachable from the function
//! confirms it, a function whose calls are all accounted for and reach no
//! entry point shows the optimizer removed it, and anything else stays
//! unverified. The verdict is a confidence tier, never a removal.
//!
//! The sweep reads relocations, so a call the compiler emitted without one,
//! an indirect tail call for example, is invisible; functions making calls
//! through registers are therefore never claimed panic free.

use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use anyhow::{Context, Result, bail, ensure};

use crate::{
    Category, CategorySet, FuncId, FuncKey, Graph, Solution, run,
    util::{Map, Set},
};

/// How a finding relates to the compiled artifact.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// A matching panic entry point is reachable from the compiled code.
    Confirmed,
    /// The compiled code reaches no matching entry point, and every call it
    /// makes was seen, so the optimizer removed the panic path.
    Absent,
    /// The artifact cannot settle it: the function was inlined away, calls
    /// code the sweep cannot see into, or the category leaves no symbol.
    Unverified,
}

impl Verdict {
    /// The name used in reports.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Confirmed => "confirmed",
            Self::Absent => "absent",
            Self::Unverified => "unverified",
        }
    }
}

/// What one compiled function was seen to do.
#[derive(Debug, Clone, Default)]
struct Facts {
    /// What each panic entry point reachable from it could stand for. A
    /// funnel serves several categories, so each entry point is kept as
    /// the set of them rather than folded into one.
    reaches: Vec<CategorySet>,
    /// Whether it reaches code the sweep cannot follow.
    open: bool,
}

/// A function the compiled artifact reaches a panic from that the analysis
/// did not report it with.
#[derive(Debug, Clone)]
pub struct Missed {
    /// The function.
    pub id: FuncId,
    /// What each entry point reached could stand for, none of which the
    /// analysis reported.
    pub reaches: Vec<CategorySet>,
}

/// Verdicts for every function the artifact defines.
#[derive(Debug, Default)]
pub struct Verdicts {
    facts: Map<String, Facts>,
}

impl Verdicts {
    /// The verdict for one function and category.
    #[must_use]
    pub fn of(&self, key: &FuncKey, category: Category) -> Verdict {
        // A reference count overflow aborts through an inlined trap
        // instruction, and the assumed categories name missing knowledge
        // rather than an entry point, so a symbol sweep can neither
        // confirm nor rule either out.
        if CategorySet::assumed().contains(category)
            || category == Category::RefCountOverflow
        {
            return Verdict::Unverified;
        }
        let Some(facts) = self.facts.get(&key.0) else {
            return Verdict::Unverified;
        };
        if facts.reaches.iter().any(|set| set.contains(category)) {
            return Verdict::Confirmed;
        }
        if facts.open {
            return Verdict::Unverified;
        }
        Verdict::Absent
    }

    /// The functions the artifact reaches a panic from that the analysis
    /// reported clean of it.
    ///
    /// This is the sweep read the other way round. A finding is looked up
    /// in the artifact to confirm it; here every function the artifact
    /// defines is looked up in the report, so a panic the analysis settled
    /// that the optimizer nonetheless kept is surfaced rather than hidden
    /// behind the proof. An entry point is missed when none of what it
    /// could stand for was reported, leaving aside what the policy assumes
    /// impossible, since that was never asked for, and leaving alone a
    /// function reported with a category that stands for code the analysis
    /// could not read, since that admits anything already.
    ///
    /// What is listed is worth a look rather than a verdict: the artifact
    /// reads a function with its callees folded in, so a check a callee
    /// keeps for other callers counts against this one, a panic caught
    /// inside the function still names its entry point, and a check the
    /// optimizer could not settle is kept whether or not it can fail.
    #[must_use]
    pub fn missed(&self, graph: &Graph, solution: &Solution) -> Vec<Missed> {
        let assumed = solution.policy().suppressed;
        let mut out = Vec::new();
        for (id, body) in graph.locals() {
            let Some(facts) = self.facts.get(&body.key.0) else {
                continue;
            };
            let reported = solution.enabled(id);
            if !reported.intersection(CategorySet::assumed()).is_empty() {
                continue;
            }
            let reaches: Vec<CategorySet> = facts
                .reaches
                .iter()
                .map(|set| set.difference(assumed))
                .filter(|set| {
                    !set.is_empty() && set.intersection(reported).is_empty()
                })
                .collect();
            if !reaches.is_empty() {
                out.push(Missed { id, reaches });
            }
        }
        out.sort_by(|a, b| {
            graph.body(a.id).display.cmp(&graph.body(b.id).display)
        });
        out
    }
}

/// Panic entry points by demangled name, most specific first.
///
/// An entry maps to every category its symbol could stand for: the funnels
/// serve several, and claiming the narrowest would confirm too little.
fn entry_categories(demangled: &str) -> Option<CategorySet> {
    use Category::{
        AllocFailure, Borrow, CapacityOverflow, DivideByZero, Explicit, Fmt,
        Index, MisalignedRef, NullDeref, Overflow, Poison, RemainderByZero,
        StrBoundary, UbCheck, Unwrap,
    };
    // Storing the categories as a slice keeps the whole table a constant
    // rather than a set rebuilt on every lookup.
    let table: &[(&str, &[Category])] = &[
        ("core::panicking::panic_bounds_check", &[Index]),
        ("core::slice::index::slice_", &[Index]),
        ("core::str::slice_error_fail", &[StrBoundary]),
        ("core::option::unwrap_failed", &[Unwrap, Poison, Fmt]),
        ("core::option::expect_failed", &[Unwrap, Poison, Fmt]),
        ("core::result::unwrap_failed", &[Unwrap, Poison, Fmt]),
        ("core::cell::panic_already", &[Borrow]),
        ("alloc::raw_vec::capacity_overflow", &[CapacityOverflow]),
        (
            "alloc::raw_vec::handle_error",
            &[CapacityOverflow, AllocFailure],
        ),
        (
            "alloc::raw_vec::handle_reserve",
            &[CapacityOverflow, AllocFailure],
        ),
        ("handle_alloc_error", &[AllocFailure]),
        ("panic_const_div_by_zero", &[DivideByZero]),
        ("panic_const_rem_by_zero", &[RemainderByZero]),
        ("panic_const_coroutine", &[Explicit]),
        ("panic_const_async", &[Explicit]),
        ("panic_const_gen_fn", &[Explicit]),
        ("panic_const_", &[Overflow]),
        ("panic_misaligned_pointer", &[MisalignedRef]),
        ("panic_null_pointer", &[NullDeref]),
        ("core::panicking::panic_nounwind", &[Explicit, UbCheck]),
        ("resume_unwind", &[Explicit]),
        ("len_mismatch_fail", &[Explicit]),
        ("core::panicking::", &[Explicit]),
    ];
    table
        .iter()
        .find(|(name, _)| demangled.contains(name))
        .map(|(_, set)| set.iter().copied().collect())
}

/// Sweeps the compiled libraries under an analysis build tree.
///
/// # Errors
///
/// Returns an error when no library is found or a tool cannot run.
pub fn sweep(tree: &Path, profile: &str) -> Result<Verdicts> {
    let objects = libraries_in(tree, run::profile_dir(profile));
    if objects.is_empty() {
        bail!(
            "no compiled library found under {} for the {profile} profile; \
             run the analysis first",
            tree.display()
        );
    }
    let objdump = llvm_tool("llvm-objdump")?;
    let mut graph = Graphed::default();
    for object in &objects {
        let listing = Command::new(&objdump)
            .arg("-d")
            .arg("-r")
            .arg("--no-show-raw-insn")
            .arg(object)
            .output()
            .with_context(|| {
                format!("could not disassemble {}", object.display())
            })?;
        // A listing cut short reads as a function that calls nothing, which
        // is the shape of a panic the optimizer removed. Refuse the sweep
        // rather than report an absence the tool never established.
        ensure!(
            listing.status.success(),
            "disassembling {} failed: {}",
            object.display(),
            String::from_utf8_lossy(&listing.stderr).trim()
        );
        graph.read(&String::from_utf8_lossy(&listing.stdout));
    }
    Ok(graph.resolve())
}

/// The call graph read out of the disassembly.
#[derive(Debug, Default)]
struct Graphed {
    calls: Map<String, Set<String>>,
    open: Set<String>,
}

impl Graphed {
    /// Reads one disassembly listing into the graph.
    fn read(&mut self, listing: &str) {
        let mut current: Option<String> = None;
        let mut taking = false;
        for line in listing.lines() {
            if let Some(label) = function_label(line) {
                self.calls.entry(label.clone()).or_default();
                current = Some(label);
                taking = false;
                continue;
            }
            let Some(function) = &current else { continue };
            if let Some(target) = relocation_target(line) {
                if taking {
                    // Handing a function's address to something else is
                    // not calling it. Where the pointer goes is invisible
                    // here, so the function is left open rather than
                    // credited with reaching what it only names.
                    self.open.insert(function.clone());
                } else {
                    self.calls
                        .entry(function.clone())
                        .or_default()
                        .insert(target);
                }
                continue;
            }
            if let Some(word) = mnemonic(line) {
                taking = word.starts_with("lea");
            }
            // A call through a bare register has no relocation to name its
            // target. A load-and-call through the GOT is not one: its
            // target arrives on the next relocation line.
            if line.contains("call") && line.contains("*%") {
                self.open.insert(function.clone());
            }
        }
    }

    /// Settles what every defined function reaches.
    fn resolve(self) -> Verdicts {
        let mut out = Verdicts::default();
        for name in self.calls.keys() {
            let mut facts = Facts::default();
            let mut seen: Set<&str> = Set::default();
            let mut stack: Vec<&str> = vec![name];
            // Each symbol enters `seen` once, so the walk is bounded by the
            // number of symbols in the artifact.
            while let Some(at) = stack.pop() {
                if !seen.insert(at) {
                    continue;
                }
                if self.open.contains(at) {
                    facts.open = true;
                }
                let Some(callees) = self.calls.get(at) else {
                    // Defined nowhere in the sweep. A panic entry point is
                    // the whole story; anything else could do anything.
                    // The alternate form drops crate disambiguators, so the
                    // table can match plain paths.
                    let readable =
                        format!("{:#}", rustc_demangle::demangle(at));
                    match entry_categories(&readable) {
                        Some(set) => {
                            if !facts.reaches.contains(&set) {
                                facts.reaches.push(set);
                            }
                        }
                        None => facts.open = true,
                    }
                    continue;
                };
                for callee in callees {
                    stack.push(callee);
                }
            }
            out.facts.insert(name.clone(), facts);
        }
        out
    }
}

/// The function a disassembly label line defines.
fn function_label(line: &str) -> Option<String> {
    let rest = line.strip_suffix(">:")?;
    let (address, name) = rest.split_once(" <")?;
    if address.is_empty() || !address.bytes().all(|b| b.is_ascii_hexdigit()) {
        return None;
    }
    Some(name.to_owned())
}

/// The mnemonic of a disassembled instruction line.
///
/// A relocation line carries an address too, so it is told apart by the
/// relocation kind that follows it rather than by shape.
fn mnemonic(line: &str) -> Option<&str> {
    let (address, rest) = line.split_once(':')?;
    let address = address.trim();
    if address.is_empty() || !address.bytes().all(|b| b.is_ascii_hexdigit()) {
        return None;
    }
    let word = rest.split_whitespace().next()?;
    (!word.starts_with("R_")).then_some(word)
}

/// The symbol a relocation line points at, when it is code.
fn relocation_target(line: &str) -> Option<String> {
    if !line.contains(":  R_") {
        return None;
    }
    let raw = line.split_whitespace().last()?;
    let raw = raw
        .rfind(['+', '-'])
        .filter(|at| raw[at + 1..].starts_with("0x"))
        .map_or(raw, |at| &raw[..at]);
    if let Some(inner) = raw.split_once("._R").map(|(_, sym)| sym) {
        // A relocation against a text section names the function through
        // the section that holds it.
        return raw.starts_with(".text").then(|| format!("_R{inner}"));
    }
    if let Some(inner) = raw.split_once("._ZN").map(|(_, sym)| sym) {
        return raw.starts_with(".text").then(|| format!("_ZN{inner}"));
    }
    if raw.starts_with('.') {
        // Data the code refers to. Reading it is not calling it, and an
        // actual call through it shows up as a register call.
        return None;
    }
    Some(raw.to_owned())
}

/// Every local library compiled by the analysis build.
///
/// Dependencies are skipped: a finding is about a local function, whose
/// compiled body sits in the crate's own library.
fn libraries_in(tree: &Path, profile_dir: &str) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut stack = vec![tree.to_path_buf()];
    // Each directory is visited once, so the walk is bounded by the size of
    // the build tree.
    while let Some(dir) = stack.pop() {
        let Ok(entries) = fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries.filter_map(Result::ok) {
            let path = entry.path();
            // Take the kind from the entry, which does not follow a
            // symbolic link. Descending through one could walk a cycle,
            // and the walk above is only bounded because it does not.
            let Ok(kind) = entry.file_type() else {
                continue;
            };
            if kind.is_dir() {
                if path.file_name().is_some_and(|name| name == "deps") {
                    continue;
                }
                stack.push(path);
                continue;
            }
            let named_lib = path
                .file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| {
                    name.starts_with("lib")
                        && Path::new(name)
                            .extension()
                            .is_some_and(|ext| ext == "rlib")
                });
            // Only the profile's own output. An artifact left by another
            // profile was built under other settings, and one under a build
            // script's directory is not what the report describes.
            let under_profile = path
                .parent()
                .and_then(Path::file_name)
                .is_some_and(|name| name == profile_dir);
            if named_lib && under_profile {
                out.push(path);
            }
        }
    }
    out
}

/// A tool shipped with the pinned toolchain.
fn llvm_tool(name: &str) -> Result<PathBuf> {
    // Ask through the same pinned compiler the analysis ran under. A crate
    // that selects another toolchain would otherwise be verified with tools
    // from a sysroot that never built the artifact.
    let sysroot = run::sysroot()?.context("rustc did not report a sysroot")?;
    let tool = PathBuf::from(sysroot)
        .join("lib")
        .join("rustlib")
        .join(run::host_triple()?)
        .join("bin")
        .join(name);
    if !tool.exists() {
        bail!(
            "{name} is missing from the toolchain; install the llvm-tools \
             component"
        );
    }
    Ok(tool)
}
