//! Rendering of analysis results.

use std::fmt::Write as _;

use anyhow::Result;

use crate::{
    Body, Category, CategorySet, FuncId, Graph, Solution, Terminal,
    args::{Args, Closures, Format, Generics},
    util::Map,
    verify::{Missed, Verdict, Verdicts},
    witness,
};

/// One reported function.
pub(crate) struct Finding<'a> {
    /// The crate the function is defined in.
    pub krate: &'a str,
    /// The name it reports under.
    pub name: &'a str,
    /// Every node that renders under this name. A generic function has one
    /// per instantiation, and they share a source location, so reporting
    /// them separately would print the same line several times.
    pub ids: Vec<FuncId>,
    pub categories: CategorySet,
    /// What the body read as written raises, with its parameters open.
    written: CategorySet,
    /// What the instantiations the build makes raise, and whether there
    /// are any.
    instantiated: Option<CategorySet>,
    /// Whether the crate's own build has the function at all. A name seen
    /// only in a test crate is a test's own generic helper, not a function
    /// of the crate.
    owned: bool,
}

impl Finding<'_> {
    /// The node the report describes the function through.
    fn id(&self) -> FuncId {
        self.ids.first().copied().unwrap_or(FuncId(0))
    }
}

/// Renders the result of an analysis.
///
/// # Errors
///
/// Returns an error if JSON serialisation fails.
pub fn analysis(
    graph: &Graph,
    solution: &Solution,
    args: &Args,
    verdicts: Option<&Verdicts>,
    out: &mut String,
) -> Result<()> {
    let findings = collect(graph, solution, args);
    match args.format {
        Format::Human => {
            human(graph, solution, args, &findings, verdicts, out);
        }
        Format::Json => {
            json(graph, solution, &findings, args, verdicts, out)?;
        }
        Format::Github => github(graph, &findings, args, out),
        // Handled before the report is built, because it draws the tree
        // rather than the list of findings.
        #[cfg(feature = "svg")]
        Format::Svg => {}
    }
    Ok(())
}

/// The artifact's verdict on one finding and category.
///
/// A finding can merge several instantiations of one function; whichever
/// the artifact confirms decides, and only unanimity can call it absent.
fn verdict_of(
    graph: &Graph,
    verdicts: &Verdicts,
    finding: &Finding<'_>,
    category: Category,
) -> Verdict {
    let mut all_absent = true;
    for &id in &finding.ids {
        match verdicts.of(&graph.body(id).key, category) {
            Verdict::Confirmed => return Verdict::Confirmed,
            Verdict::Absent => {}
            Verdict::Unverified => all_absent = false,
        }
    }
    if all_absent {
        Verdict::Absent
    } else {
        Verdict::Unverified
    }
}

/// Every function the report considers, with what it reports under, which
/// may be nothing at all.
///
/// A function that reports nothing still matters: an instantiation of a
/// generic function that raises nothing is what the instantiation view
/// reads instead of the body as written.
fn considered<'a>(
    graph: &'a Graph,
    solution: &'a Solution,
    args: &'a Args,
) -> impl Iterator<Item = (FuncId, &'a Body, CategorySet)> {
    graph.iter().filter_map(move |(id, body)| {
        if body.opaque || !(args.all_crates || body.local) {
            return None;
        }
        let enabled = solution.enabled(id);
        let categories =
            args.only.map_or(enabled, |only| enabled.intersection(only));
        Some((id, body, categories))
    })
}

/// The name a body reports under.
///
/// A closure is not an addressable function of the crate's own interface,
/// so the parent view folds it into the function it is written in. The
/// separate view stays the default because it is the precise one: a panic
/// contained by a catch belongs to the closure, not to its caller.
pub(crate) fn reported_name<'a>(body: &'a Body, args: &Args) -> &'a str {
    match args.closures {
        Closures::Separate => &body.display,
        Closures::Parent => body
            .display
            .split("::{closure")
            .next()
            .unwrap_or(&body.display),
    }
}

/// Whether anything at all would be reported under these settings.
///
/// The exit code is what a continuous integration run reads, so it has to
/// agree with what the report prints rather than with the unfiltered
/// solution: a run that names no finding has nothing to report.
#[must_use]
pub fn any_finding(graph: &Graph, solution: &Solution, args: &Args) -> bool {
    !collect(graph, solution, args).is_empty()
}

/// Selects the functions worth reporting, one entry per name.
///
/// The report and the gate both group here, so a function that reports
/// under one name cannot be gated under another. A generic function is
/// read as written and once per instantiation, and which of those the
/// name reports is the caller's choice: everything, or the instantiations
/// alone where there are any.
pub(crate) fn collect<'a>(
    graph: &'a Graph,
    solution: &'a Solution,
    args: &'a Args,
) -> Vec<Finding<'a>> {
    let mut findings: Vec<Finding<'a>> = Vec::new();
    let mut index: Map<(&str, &str), usize> = Map::default();
    for (id, body, categories) in considered(graph, solution, args) {
        let name = reported_name(body, args);
        let key = (body.krate.as_str(), name);
        let at = if let Some(&at) = index.get(&key) {
            at
        } else {
            index.insert(key, findings.len());
            findings.push(Finding {
                krate: &body.krate,
                name,
                ids: Vec::new(),
                categories: CategorySet::EMPTY,
                written: CategorySet::EMPTY,
                instantiated: None,
                owned: false,
            });
            findings.len().saturating_sub(1)
        };
        let Some(finding) = findings.get_mut(at) else {
            continue;
        };
        finding.ids.push(id);
        finding.owned |= !body.from_tests;
        if body.key.is_open() {
            finding.written = finding.written.union(categories);
        } else {
            let held = finding.instantiated.unwrap_or(CategorySet::EMPTY);
            finding.instantiated = Some(held.union(categories));
        }
    }
    for finding in &mut findings {
        finding.categories = match (args.generics, finding.instantiated) {
            (Generics::Instantiated, Some(instantiated)) => instantiated,
            (_, instantiated) => finding
                .written
                .union(instantiated.unwrap_or(CategorySet::EMPTY)),
        };
    }
    findings.retain(|finding| finding.owned && !finding.categories.is_empty());
    findings.sort_by(|a, b| a.name.cmp(b.name));
    findings
}

/// Writes the functions the artifact reaches a panic from that the report
/// does not name them with.
fn missed_prose(graph: &Graph, missed: &[Missed], out: &mut String) {
    if missed.is_empty() {
        return;
    }
    out.push_str(
        "The compiled artifact reaches panics the analysis did not report:\n\n",
    );
    for entry in missed {
        let body = graph.body(entry.id);
        let _ = writeln!(out, "{}", body.display);
        if let Some(loc) = &body.loc {
            let _ = writeln!(out, "    defined at {loc}");
        }
        for set in &entry.reaches {
            let _ = writeln!(out, "    {}", set.names().join(", or "));
        }
        out.push('\n');
    }
}

/// Writes the human readable report.
fn human(
    graph: &Graph,
    solution: &Solution,
    args: &Args,
    findings: &[Finding<'_>],
    verdicts: Option<&Verdicts>,
    out: &mut String,
) {
    header(graph, args, findings.len(), out);

    if findings.is_empty() {
        out.push_str("\nNo function can panic under this policy.\n");
        return;
    }

    out.push('\n');
    for finding in findings {
        let body = graph.body(finding.id());
        let _ = writeln!(out, "{}", reported_name(body, args));
        if let Some(loc) = &body.loc {
            let _ = writeln!(out, "    defined at {loc}");
        }
        for category in finding.categories.iter() {
            match direct_site(graph, solution, finding, category) {
                Some(site) => {
                    let _ = write!(out, "    {category:<18} {}", site.0);
                    if let Some(loc) = site.1 {
                        let _ = write!(out, " at {loc}");
                    }
                }
                None => {
                    let _ = write!(
                        out,
                        "    {category:<18} reached through a call"
                    );
                }
            }
            if let Some(verdicts) = verdicts {
                let word = match verdict_of(graph, verdicts, finding, category)
                {
                    Verdict::Confirmed => "confirmed in",
                    Verdict::Absent => "absent from",
                    Verdict::Unverified => "unverified in",
                };
                let _ = write!(out, " ({word} the compiled artifact)");
            }
            out.push('\n');
        }
        out.push('\n');
    }

    if let Some(verdicts) = verdicts {
        missed_prose(graph, &verdicts.missed(graph, solution), out);
    }

    let _ =
        writeln!(out, "Run `panicgraph why <function>` to see a call path.");
}

/// The reason and place of a panic this function raises itself.
///
/// Returns nothing when the category is only reached through a call.
fn direct_site<'a>(
    graph: &'a Graph,
    solution: &Solution,
    finding: &Finding<'_>,
    category: Category,
) -> Option<(&'a str, Option<String>)> {
    for &id in &finding.ids {
        let body = graph.body(id);
        let activity = solution.activity(graph, id);
        let hit =
            body.sites.iter().enumerate().find(|(i, site)| {
                site.category == category && activity.site(*i)
            });
        if let Some((_, site)) = hit {
            return Some((
                site.reason.as_str(),
                site.loc.as_ref().map(ToString::to_string),
            ));
        }
    }
    None
}

/// Writes the analysis preamble.
fn header(graph: &Graph, args: &Args, found: usize, out: &mut String) {
    out.push_str("Analysis\n");
    if let Some(config) = graph.config() {
        let _ = writeln!(out, "    rustc              {}", config.rustc);
        let _ = writeln!(
            out,
            "    profile            {} (debug assertions {}, overflow \
             checks {})",
            config.profile,
            on_off(config.debug_assertions),
            on_off(config.overflow_checks),
        );
        let _ =
            writeln!(out, "    standard library   {}", config.std_mode.name());
        if let Some(level) = config.mir_opt_level {
            let _ = writeln!(out, "    mir opt level      {level}");
        }
    }
    let suppressed = if args.suppress.is_empty() {
        "nothing".to_owned()
    } else {
        args.suppress.to_string()
    };
    let _ = writeln!(out, "    suppressed         {suppressed}");
    let _ = writeln!(
        out,
        "    functions          {} analysed, {found} can panic",
        graph.len()
    );
}

/// Writes the machine readable report.
fn json(
    graph: &Graph,
    solution: &Solution,
    findings: &[Finding<'_>],
    args: &Args,
    verdicts: Option<&Verdicts>,
    out: &mut String,
) -> Result<()> {
    let items: Vec<serde_json::Value> = findings
        .iter()
        .map(|f| {
            let body = graph.body(f.id());
            let mut item = serde_json::json!({
                "function": reported_name(body, args),
                "crate": body.krate,
                "location": body.loc.as_ref().map(ToString::to_string),
                "categories": f
                    .categories.names(),
            });
            if let Some(verdicts) = verdicts {
                let verified: serde_json::Map<String, serde_json::Value> = f
                    .categories
                    .iter()
                    .map(|category| {
                        (
                            category.name().to_owned(),
                            verdict_of(graph, verdicts, f, category)
                                .name()
                                .into(),
                        )
                    })
                    .collect();
                item["verified"] = verified.into();
            }
            item
        })
        .collect();
    let mut doc = serde_json::json!({
        "config": graph.config(),
        "analysed": graph.len(),
        "findings": items,
    });
    if let Some(verdicts) = verdicts {
        let missed: Vec<serde_json::Value> = verdicts
            .missed(graph, solution)
            .iter()
            .map(|entry| {
                let body = graph.body(entry.id);
                serde_json::json!({
                    "function": reported_name(body, args),
                    "crate": body.krate,
                    "location": body.loc.as_ref().map(ToString::to_string),
                    "reaches": entry
                        .reaches
                        .iter()
                        .map(|set| set.names())
                        .collect::<Vec<_>>(),
                })
            })
            .collect();
        doc["missed"] = missed.into();
    }
    out.push_str(&serde_json::to_string_pretty(&doc)?);
    out.push('\n');
    Ok(())
}

/// Splits a `file:line:col` location into the fields a workflow command
/// wants, or nothing at all when there is no location to name.
pub(crate) fn workflow_location(loc: Option<&str>) -> String {
    fn split(loc: &str) -> Option<String> {
        let mut parts = loc.rsplitn(3, ':');
        let col = parts.next()?;
        let line = parts.next()?;
        let file = parts.next()?;
        Some(format!("file={file},line={line},col={col},"))
    }
    loc.and_then(split).unwrap_or_default()
}

/// Writes one workflow command per finding, which a continuous integration
/// log turns into an annotation against the source.
fn github(
    graph: &Graph,
    findings: &[Finding<'_>],
    args: &Args,
    out: &mut String,
) {
    for finding in findings {
        let body = graph.body(finding.id());
        let loc = body.loc.as_ref().map(ToString::to_string);
        let where_at = workflow_location(loc.as_deref());
        let _ = writeln!(
            out,
            "::warning {where_at}title=Function can panic::{} can panic \
             with {}",
            reported_name(body, args),
            finding.categories.names().join(", ")
        );
    }
}

/// Explains one function's panics for a machine.
///
/// The same walk the prose takes, written as the path itself: every hop
/// names the callee it reaches and the edge it was resolved through, and
/// the ending says what raises.
///
/// # Errors
///
/// Returns an error if the document cannot be serialized.
pub fn why_json(
    graph: &Graph,
    solution: &Solution,
    name: &str,
    out: &mut String,
) -> Result<()> {
    let matches = graph.find_by_display(name);
    let doc = match matches.first() {
        None => serde_json::json!({ "query": name, "matched": 0 }),
        Some(&id) => {
            let body = graph.body(id);
            let paths: Vec<serde_json::Value> = solution
                .enabled(id)
                .iter()
                .filter_map(|category| {
                    let path = witness::find(graph, solution, id, category)?;
                    Some(serde_json::json!({
                        "category": category.name(),
                        "hops": path
                            .hops
                            .iter()
                            .map(|hop| serde_json::json!({
                                "function": graph.body(hop.callee).display,
                                "kind": hop.kind.name(),
                                "location": hop
                                    .loc
                                    .as_ref()
                                    .map(ToString::to_string),
                            }))
                            .collect::<Vec<_>>(),
                        "ending": ending(graph, &path),
                    }))
                })
                .collect();
            serde_json::json!({
                "query": name,
                "matched": matches.len(),
                "function": body.display,
                "crate": body.krate,
                "location": body.loc.as_ref().map(ToString::to_string),
                "categories": solution.enabled(id).names(),
                "paths": paths,
            })
        }
    };
    out.push_str(&serde_json::to_string_pretty(&doc)?);
    out.push('\n');
    Ok(())
}

/// What the end of a witness path raises, as a document.
fn ending(graph: &Graph, path: &witness::Witness) -> serde_json::Value {
    let body = graph.body(path.func);
    match path.terminal {
        Terminal::Site(i) => body.sites.get(i).map_or_else(
            || serde_json::json!({ "kind": "site" }),
            |site| {
                serde_json::json!({
                    "kind": "site",
                    "reason": site.reason,
                    "location": site.loc.as_ref().map(ToString::to_string),
                })
            },
        ),
        Terminal::Opaque => serde_json::json!({
            "kind": if body.foreign { "foreign" } else { "opaque" },
        }),
        Terminal::Unresolved(i) => body.calls.get(i).map_or_else(
            || serde_json::json!({ "kind": "unresolved" }),
            |call| {
                serde_json::json!({
                    "kind": "unresolved",
                    "callee": call.callee_display,
                    "edge": call.kind.name(),
                    "location": call.loc.as_ref().map(ToString::to_string),
                })
            },
        ),
    }
}

/// Explains how one function reaches a panic.
pub fn why(graph: &Graph, solution: &Solution, name: &str, out: &mut String) {
    let matches = graph.find_by_display(name);
    let Some(&id) = matches.first() else {
        let _ = writeln!(out, "No function matching `{name}` was analysed.");
        return;
    };
    let body = graph.body(id);
    if matches.len() > 1 {
        let same = matches
            .iter()
            .filter(|&&other| graph.body(other).display == body.display)
            .count();
        if same == matches.len() {
            let _ = writeln!(
                out,
                "`{name}` names {same} instantiations of the same function; \
                 explaining one.\n"
            );
        } else {
            let _ = writeln!(
                out,
                "`{name}` matched {} functions; explaining `{}`.\n",
                matches.len(),
                body.display
            );
        }
    }

    let categories = solution.enabled(id);
    if categories.is_empty() {
        let _ =
            writeln!(out, "{} cannot panic under this policy.", body.display);
        return;
    }

    for category in categories.iter() {
        let Some(path) = witness::find(graph, solution, id, category) else {
            continue;
        };
        let _ =
            writeln!(out, "{} can panic with `{category}`:\n", body.display);
        let _ = writeln!(out, "  {}", body.display);
        for hop in &path.hops {
            if let Some(loc) = &hop.loc {
                let _ = writeln!(out, "      at {loc}  [{}]", hop.kind.name());
            }
            let _ = writeln!(out, "  -> {}", graph.body(hop.callee).display);
        }
        describe_terminal(graph, &path, out);
        out.push('\n');
    }
}

/// Writes the last line of a witness path.
fn describe_terminal(graph: &Graph, path: &witness::Witness, out: &mut String) {
    let body = graph.body(path.func);
    match path.terminal {
        Terminal::Site(i) => {
            let Some(site) = body.sites.get(i) else {
                return;
            };
            let _ = write!(out, "      {}", site.reason);
            if let Some(loc) = &site.loc {
                let _ = write!(out, " at {loc}");
            }
            out.push('\n');
        }
        Terminal::Opaque if body.foreign => {
            let _ = writeln!(
                out,
                "      foreign code, which has no Rust body to read"
            );
        }
        Terminal::Opaque => {
            let _ = writeln!(
                out,
                "      no MIR available for this function, so its panics \
                 are unknown"
            );
            let _ = writeln!(
                out,
                "      re-run with `--std full` to see inside the standard \
                 library"
            );
        }
        Terminal::Unresolved(i) => {
            let Some(call) = body.calls.get(i) else {
                return;
            };
            let _ = write!(
                out,
                "      calls {} through a {} edge, target unknown",
                call.callee_display,
                call.kind.name()
            );
            if let Some(loc) = &call.loc {
                let _ = write!(out, " at {loc}");
            }
            out.push('\n');
        }
    }
}

/// Lists the categories and what each means, for a machine.
///
/// # Errors
///
/// Returns an error if the document cannot be serialized.
pub fn kinds_json(out: &mut String) -> Result<()> {
    let doc = serde_json::json!({
        "categories": crate::category::ALL
            .iter()
            .map(|category| serde_json::json!({
                "name": category.name(),
                "describe": category.describe(),
                // Whether the name stands for a panic or for a place the
                // analysis could not read.
                "assumed": CategorySet::assumed().contains(*category),
            }))
            .collect::<Vec<_>>(),
        "aliases": serde_json::json!({
            "oom": CategorySet::oom().names(),
            "default": CategorySet::default_suppressed().names(),
            "assumed": CategorySet::assumed().names(),
            "all": crate::category::ALL
                .iter()
                .map(|category| category.name())
                .collect::<Vec<_>>(),
        }),
    });
    out.push_str(&serde_json::to_string_pretty(&doc)?);
    out.push('\n');
    Ok(())
}

/// Writes the taxonomy as prose.
pub fn kinds(out: &mut String) {
    out.push_str("Panic categories\n\n");
    for category in crate::category::ALL {
        let _ =
            writeln!(out, "  {:<18} {}", category.name(), category.describe());
    }
    out.push_str(
        "\nGroup aliases: `oom` covers capacity-overflow and alloc-failure, \
         `default` adds ub-check, `assumed` covers what the analysis could \
         not read, `all` covers everything.\n",
    );
}

/// Renders a flag as text.
const fn on_off(value: bool) -> &'static str {
    if value { "on" } else { "off" }
}

/// Suppressed categories that were nonetheless observed, for the hint line.
///
/// # Errors
///
/// Returns an error if the graph cannot be solved without the suppression,
/// which is what the count is measured against.
pub fn suppressed_hint(
    graph: &Graph,
    solution: &Solution,
    args: &Args,
) -> Result<Option<String>> {
    if args.suppress.is_empty() {
        return Ok(None);
    }
    let hidden = solution.cleared_by_suppression(graph)?;
    Ok((hidden > 0).then(|| {
        format!(
            "{hidden} local functions panic only through suppressed \
             categories ({}).",
            args.suppress
        )
    }))
}
