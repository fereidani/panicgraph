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
    Category, FuncId, Graph, Solution,
    args::{Args, Check, Format},
    util::Map,
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
            (check.fail_on_unknown
                && covered
                && finding.categories.iter().any(|c| c == "unknown"))
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
        let live: Vec<&str> = outcome
            .findings
            .iter()
            .map(|f| f.function.as_str())
            .collect();
        outcome.fixed = known
            .keys()
            .filter(|name| !live.contains(&name.as_str()))
            .cloned()
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
fn collect(graph: &Graph, solution: &Solution, args: &Args) -> Vec<Finding> {
    let mut findings: Vec<Finding> = graph
        .iter()
        .filter(|(_, body)| args.all_crates || body.local)
        .filter(|(_, body)| !body.opaque)
        .filter_map(|(id, _)| build(graph, solution, args, id))
        .collect();
    findings.sort_by(|a, b| a.function.cmp(&b.function));
    findings
}

/// Turns one function into a finding, when it has anything to report.
fn build(
    graph: &Graph,
    solution: &Solution,
    args: &Args,
    id: FuncId,
) -> Option<Finding> {
    let mut categories = solution.enabled(id);
    if let Some(only) = args.only {
        categories = categories.intersection(only);
    }
    if categories.is_empty() {
        return None;
    }
    let body = graph.body(id);
    Some(Finding {
        function: body.display.clone(),
        krate: body.krate.clone(),
        loc: body.loc.as_ref().map(ToString::to_string),
        categories: categories.iter().map(|c| c.name().to_owned()).collect(),
    })
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

/// Writes the human readable verdict.
fn human(outcome: &Outcome, check: &Check, out: &mut String) {
    if !outcome.violations.is_empty() {
        let _ = writeln!(
            out,
            "{} function{} must not panic and can:\n",
            outcome.violations.len(),
            if outcome.violations.len() == 1 {
                ""
            } else {
                "s"
            }
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
            if total == 1 { "" } else { "s" }
        );
    } else if let Some(max) = check.max {
        let _ = writeln!(
            out,
            "{total} function{} can panic, within the {max} allowed.",
            if total == 1 { "" } else { "s" }
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
        let where_at = violation
            .finding
            .loc
            .as_deref()
            .and_then(location)
            .unwrap_or_default();
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

/// Splits `file:line:col` into the fields a workflow command wants.
fn location(loc: &str) -> Option<String> {
    let mut parts = loc.rsplitn(3, ':');
    let col = parts.next()?;
    let line = parts.next()?;
    let file = parts.next()?;
    Some(format!("file={file},line={line},col={col},"))
}
