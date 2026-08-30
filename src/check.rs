//! The gate a continuous integration run applies to the findings.
//!
//! A check answers one question: are the functions that must not panic still
//! unable to? Everything here exists to make the answer legible when it is
//! no, and quiet when it is yes.

use std::{fmt::Write as _, fs, path::Path};

use anyhow::{Context, Result, bail};
use regex::RegexSet;
use serde_json::{Value, json};

use crate::{
    Category, CategorySet, Graph, Solution,
    args::{Args, Check, Format},
    report::{reportable, workflow_location},
    util::{Map, Set},
};

/// The format version written into a baseline.
const BASELINE_VERSION: u32 = 1;

/// One function that can panic.
#[derive(Debug, Clone)]
pub struct Finding {
    /// The function's readable path.
    pub function: String,
    /// The crate it is defined in.
    pub krate: String,
    /// Where it is defined.
    pub loc: Option<String>,
    /// The categories it can raise, in reporting order.
    pub categories: Vec<String>,
}

/// Why a finding failed the gate.
#[derive(Debug, Clone)]
pub enum Reason {
    /// The function is covered by a pattern that forbids panicking.
    Forbidden,
    /// The function is absent from the baseline, or gained a category.
    New,
    /// The analysis could not classify what it reaches.
    Unclassified,
}

impl Reason {
    /// A short phrase naming the failure.
    const fn describe(&self) -> &'static str {
        match self {
            Self::Forbidden => "must not panic",
            Self::New => "not in the baseline",
            Self::Unclassified => "reaches an unclassified panic",
        }
    }
}

/// One failure of the gate.
#[derive(Debug, Clone)]
pub struct Violation {
    /// The offending finding.
    pub finding: Finding,
    /// Why it failed.
    pub reason: Reason,
}

/// Everything a check concluded.
#[derive(Debug, Default)]
pub struct Outcome {
    /// Every local function that can panic.
    pub findings: Vec<Finding>,
    /// The ones that failed a gate.
    pub violations: Vec<Violation>,
    /// Functions the baseline recorded that no longer panic.
    pub fixed: Vec<String>,
    /// Set when more functions panic than the ceiling allows.
    pub over_max: Option<(usize, usize)>,
}

impl Outcome {
    /// Whether anything failed.
    #[must_use]
    pub const fn failed(&self) -> bool {
        !self.violations.is_empty() || self.over_max.is_some()
    }
}

/// Applies the gate to a solved graph.
///
/// # Errors
///
/// Returns an error for an unusable pattern or an unreadable baseline.
pub fn run(
    graph: &Graph,
    solution: &Solution,
    args: &Args,
    check: &Check,
) -> Result<Outcome> {
    let findings = collect(graph, solution, args);
    let mut outcome = Outcome {
        findings,
        ..Outcome::default()
    };

    let forbid = compile(&check.forbid, "--forbid")?;
    let allow = compile(&check.allow, "--allow")?;
    // With no gate at all the whole crate is covered, which is the check a
    // crate that must not panic asks for. Naming any gate replaces that
    // default rather than stacking with it, so a ceiling means a ceiling.
    let gate_everything = check.forbid.is_empty()
        && check.max.is_none()
        && check.baseline.is_none();

    let baseline = match &check.baseline {
        Some(path) => Some(read_baseline(path)?),
        None => None,
    };

    for finding in &outcome.findings {
        if allow.is_match(&finding.function) {
            continue;
        }
        let covered = gate_everything || forbid.is_match(&finding.function);
        let reason = baseline.as_ref().map_or_else(
            || covered.then_some(Reason::Forbidden),
            |known| is_new(known, finding).then_some(Reason::New),
        );
        let reason = reason.or_else(|| {
            let assumed = |name: &String| {
                name.parse::<Category>()
                    .is_ok_and(|c| CategorySet::assumed().contains(c))
            };
            (check.fail_on_unknown
                && covered
                && finding.categories.iter().any(assumed))
            .then_some(Reason::Unclassified)
        });
        if let Some(reason) = reason {
            outcome.violations.push(Violation {
                finding: finding.clone(),
                reason,
            });
        }
    }

    if let Some(known) = &baseline {
        let live: Set<&str> = outcome
            .findings
            .iter()
            .map(|f| f.function.as_str())
            .collect();
        outcome.fixed = known
            .iter()
            .filter(|(name, _)| !live.contains(name.as_str()))
            .filter(|(_, recorded)| in_view(args.only, recorded))
            .map(|(name, _)| name.clone())
            .collect();
        outcome.fixed.sort();
    }

    if let Some(max) = check.max
        && outcome.findings.len() > max
    {
        outcome.over_max = Some((outcome.findings.len(), max));
    }

    Ok(outcome)
}

/// Whether the reported categories could have shown a baseline entry.
///
/// Absence from the findings means a function no longer panics only when the
/// analysis was looking for what the baseline recorded. Under `--only`, an
/// entry outside the selection is not gone, it is out of view, and calling it
/// fixed would send the reader off to refresh a baseline that is current.
fn in_view(only: Option<CategorySet>, recorded: &[String]) -> bool {
    let Some(only) = only else {
        return true;
    };
    recorded
        .iter()
        .filter_map(|name| name.parse::<Category>().ok())
        .any(|category| only.contains(category))
}

/// Whether a finding is absent from the baseline, or has grown a category.
fn is_new(known: &Map<String, Vec<String>>, finding: &Finding) -> bool {
    known.get(&finding.function).is_none_or(|recorded| {
        finding
            .categories
            .iter()
            .any(|category| !recorded.contains(category))
    })
}

/// Every local function that can panic under the solved policy.
///
/// A generic function has one node per instantiation and they all report
/// under the same name, so they are merged: the gate asks whether a function
/// can panic, and it can if any of its instantiations can.
fn collect(graph: &Graph, solution: &Solution, args: &Args) -> Vec<Finding> {
    let mut findings: Vec<Finding> = Vec::new();
    let mut index: Map<(String, String), usize> = Map::default();
    for (_, body, categories) in reportable(graph, solution, args) {
        let finding = Finding {
            function: body.display.clone(),
            krate: body.krate.clone(),
            loc: body.loc.as_ref().map(ToString::to_string),
            categories: categories
                .iter()
                .map(|c| c.name().to_owned())
                .collect(),
        };
        let name = (finding.krate.clone(), finding.function.clone());
        if let Some(&at) = index.get(&name) {
            merge(&mut findings[at], finding);
        } else {
            index.insert(name, findings.len());
            findings.push(finding);
        }
    }
    findings.sort_by(|a, b| a.function.cmp(&b.function));
    findings
}

/// Folds a second instantiation of the same function into the first.
///
/// Categories stay in the order the taxonomy declares them, which is the
/// order every other report uses.
fn merge(into: &mut Finding, other: Finding) {
    let mut set = CategorySet::EMPTY;
    for name in into.categories.iter().chain(&other.categories) {
        if let Ok(category) = name.parse::<Category>() {
            set.insert(category);
        }
    }
    into.categories = set.iter().map(|c| c.name().to_owned()).collect();
    if into.loc.is_none() {
        into.loc = other.loc;
    }
}

/// Compiles a set of patterns, naming the flag when one is unusable.
fn compile(patterns: &[String], flag: &str) -> Result<RegexSet> {
    RegexSet::new(patterns)
        .with_context(|| format!("a pattern given to {flag} is not valid"))
}

/// Writes the findings so a later run can gate on what changed.
///
/// # Errors
///
/// Returns an error if the file cannot be written.
pub fn write_baseline(
    path: &Path,
    args: &Args,
    findings: &[Finding],
) -> Result<()> {
    let doc = json!({
        "version": BASELINE_VERSION,
        "profile": args.profile,
        "std_mode": format!("{:?}", args.std_mode).to_lowercase(),
        "suppressed": args.suppress.iter()
            .map(Category::name).collect::<Vec<_>>(),
        "findings": findings.iter().map(|f| json!({
            "function": f.function,
            "categories": f.categories,
        })).collect::<Vec<_>>(),
    });
    let text = serde_json::to_string_pretty(&doc)?;
    fs::write(path, format!("{text}\n"))
        .with_context(|| format!("could not write {}", path.display()))
}

/// Reads a baseline into the categories recorded per function.
///
/// # Errors
///
/// Returns an error if the file is missing, unreadable, or not a baseline.
pub fn read_baseline(path: &Path) -> Result<Map<String, Vec<String>>> {
    let text = fs::read_to_string(path).with_context(|| {
        format!(
            "could not read {}; write one with `panicgraph baseline {}`",
            path.display(),
            path.display()
        )
    })?;
    let doc: Value = serde_json::from_str(&text)
        .with_context(|| format!("{} is not valid json", path.display()))?;
    let version = doc.get("version").and_then(Value::as_u64).unwrap_or(0);
    if version != u64::from(BASELINE_VERSION) {
        bail!(
            "{} was written by a different version of this tool; write a \
             fresh one with `panicgraph baseline {}`",
            path.display(),
            path.display()
        );
    }
    let mut out = Map::default();
    let entries = doc.get("findings").and_then(Value::as_array);
    for entry in entries.into_iter().flatten() {
        let Some(name) = entry.get("function").and_then(Value::as_str) else {
            continue;
        };
        let categories = entry
            .get("categories")
            .and_then(Value::as_array)
            .map(|list| {
                list.iter()
                    .filter_map(Value::as_str)
                    .map(ToOwned::to_owned)
                    .collect()
            })
            .unwrap_or_default();
        out.insert(name.to_owned(), categories);
    }
    Ok(out)
}

/// Renders the outcome.
///
/// # Errors
///
/// Returns an error if JSON serialisation fails.
pub fn render(
    outcome: &Outcome,
    args: &Args,
    check: &Check,
    out: &mut String,
) -> Result<()> {
    match args.format {
        #[cfg(feature = "svg")]
        Format::Svg => human(outcome, check, out),
        Format::Human => human(outcome, check, out),
        Format::Github => github(outcome, out),
        Format::Json => {
            let doc = json!({
                "passed": !outcome.failed(),
                "analysed": outcome.findings.len(),
                "violations": outcome.violations.iter().map(|v| json!({
                    "function": v.finding.function,
                    "reason": v.reason.describe(),
                    "categories": v.finding.categories,
                    "location": v.finding.loc,
                })).collect::<Vec<_>>(),
                "fixed": outcome.fixed,
            });
            out.push_str(&serde_json::to_string_pretty(&doc)?);
            out.push('\n');
        }
    }
    Ok(())
}

/// The suffix that makes a count read as English.
const fn plural(count: usize) -> &'static str {
    if count == 1 { "" } else { "s" }
}

/// Writes the human readable verdict.
fn human(outcome: &Outcome, check: &Check, out: &mut String) {
    if !outcome.violations.is_empty() {
        let _ = writeln!(
            out,
            "{} function{} must not panic and can:\n",
            outcome.violations.len(),
            plural(outcome.violations.len())
        );
        for violation in &outcome.violations {
            let _ = writeln!(out, "{}", violation.finding.function);
            if let Some(loc) = &violation.finding.loc {
                let _ = writeln!(out, "    at {loc}");
            }
            let _ = writeln!(
                out,
                "    {} ({})",
                violation.finding.categories.join(", "),
                violation.reason.describe()
            );
        }
        out.push('\n');
    }

    if let Some((actual, max)) = outcome.over_max {
        let _ = writeln!(
            out,
            "{actual} functions can panic, which is more than the {max} \
             allowed.\n"
        );
    }

    if !outcome.fixed.is_empty() {
        let _ = writeln!(
            out,
            "{} in the baseline no longer panics. Refresh it with \
             `panicgraph baseline`.",
            if outcome.fixed.len() == 1 {
                "1 function".to_owned()
            } else {
                format!("{} functions", outcome.fixed.len())
            }
        );
        for name in outcome.fixed.iter().take(10) {
            let _ = writeln!(out, "    {name}");
        }
        out.push('\n');
    }

    if outcome.failed() {
        let _ = writeln!(
            out,
            "Run `panicgraph why <function>` to see how one of them gets \
             there."
        );
        return;
    }

    // Say which gate passed. A check that reports something other than what
    // was asked for reads as though it checked the wrong thing.
    let total = outcome.findings.len();
    if check.baseline.is_some() {
        let _ = writeln!(
            out,
            "No panic that the baseline does not already record. {total} \
             function{} can panic.",
            plural(total)
        );
    } else if let Some(max) = check.max {
        let _ = writeln!(
            out,
            "{total} function{} can panic, within the {max} allowed.",
            plural(total)
        );
    } else if check.forbid.is_empty() {
        let _ = writeln!(out, "No function can panic under this policy.");
    } else {
        let _ = writeln!(
            out,
            "No function matching {} can panic. {total} can in total.",
            check.forbid.join(" or ")
        );
    }
}

/// Writes workflow commands a continuous integration log will annotate.
fn github(outcome: &Outcome, out: &mut String) {
    for violation in &outcome.violations {
        let where_at = workflow_location(violation.finding.loc.as_deref());
        let _ = writeln!(
            out,
            "::error {where_at}title=Function can panic::{} can panic with \
             {} ({})",
            violation.finding.function,
            violation.finding.categories.join(", "),
            violation.reason.describe()
        );
    }
    if let Some((actual, max)) = outcome.over_max {
        let _ = writeln!(
            out,
            "::error title=Too many panicking functions::{actual} functions \
             can panic, more than the {max} allowed"
        );
    }
    for name in &outcome.fixed {
        let _ = writeln!(
            out,
            "::notice title=Baseline is stale::{name} no longer panics"
        );
    }
}
