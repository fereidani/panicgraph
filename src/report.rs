//! Rendering of analysis results.

use std::fmt::Write as _;

use anyhow::Result;

use crate::{
    Category, CategorySet, FuncId, Graph, Solution, Terminal,
    args::{Args, Format},
    witness,
};

/// One reported function.
struct Finding {
    id: FuncId,
    categories: CategorySet,
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
    out: &mut String,
) -> Result<()> {
    let findings = collect(graph, solution, args);
    match args.format {
        Format::Human => human(graph, solution, args, &findings, out),
        Format::Json => json(graph, &findings, out)?,
        Format::Github => github(graph, &findings, out),
        // Handled before the report is built, because it draws the tree
        // rather than the list of findings.
        #[cfg(feature = "svg")]
        Format::Svg => {}
    }
    Ok(())
}

/// Selects the functions worth reporting.
fn collect(graph: &Graph, solution: &Solution, args: &Args) -> Vec<Finding> {
    let mut findings: Vec<Finding> = graph
        .iter()
        .filter(|(_, body)| args.all_crates || body.local)
        .filter(|(_, body)| !body.opaque)
        .filter_map(|(id, _)| {
            let mut categories = solution.enabled(id);
            if let Some(only) = args.only {
                categories = categories.intersection(only);
            }
            (!categories.is_empty()).then_some(Finding { id, categories })
        })
        .collect();
    findings.sort_by(|a, b| {
        graph.body(a.id).display.cmp(&graph.body(b.id).display)
    });
    findings
}

/// Writes the human readable report.
fn human(
    graph: &Graph,
    solution: &Solution,
    args: &Args,
    findings: &[Finding],
    out: &mut String,
) {
    header(graph, args, findings.len(), out);

    if findings.is_empty() {
        out.push_str("\nNo function can panic under this policy.\n");
        return;
    }

    out.push('\n');
    for finding in findings {
        let body = graph.body(finding.id);
        let _ = writeln!(out, "{}", body.display);
        if let Some(loc) = &body.loc {
            let _ = writeln!(out, "    defined at {loc}");
        }
        let activity = solution.activity(graph, finding.id);
        for category in finding.categories.iter() {
            let direct = body
                .sites
                .iter()
                .enumerate()
                .filter(|(i, _)| {
                    activity.sites.get(*i).copied().unwrap_or(false)
                })
                .find(|(_, s)| s.category == category);
            match direct {
                Some((_, site)) => {
                    let _ = write!(out, "    {category:<18} {}", site.reason);
                    if let Some(loc) = &site.loc {
                        let _ = write!(out, " at {loc}");
                    }
                    out.push('\n');
                }
                None => {
                    let _ = writeln!(
                        out,
                        "    {category:<18} reached through a call"
                    );
                }
            }
        }
        out.push('\n');
    }

    let _ =
        writeln!(out, "Run `panicgraph why <function>` to see a call path.");
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
fn json(graph: &Graph, findings: &[Finding], out: &mut String) -> Result<()> {
    let items: Vec<serde_json::Value> = findings
        .iter()
        .map(|f| {
            let body = graph.body(f.id);
            serde_json::json!({
                "function": body.display,
                "crate": body.krate,
                "location": body.loc.as_ref().map(ToString::to_string),
                "categories": f
                    .categories
                    .iter()
                    .map(crate::Category::name)
                    .collect::<Vec<_>>(),
            })
        })
        .collect();
    let doc = serde_json::json!({
        "config": graph.config(),
        "findings": items,
    });
    out.push_str(&serde_json::to_string_pretty(&doc)?);
    out.push('\n');
    Ok(())
}

/// Writes one workflow command per finding, which a continuous integration
/// log turns into an annotation against the source.
fn github(graph: &Graph, findings: &[Finding], out: &mut String) {
    for finding in findings {
        let body = graph.body(finding.id);
        let where_at = body
            .loc
            .as_ref()
            .map(ToString::to_string)
            .and_then(|loc| {
                let mut parts = loc.rsplitn(3, ':');
                let col = parts.next()?;
                let line = parts.next()?;
                let file = parts.next()?;
                Some(format!("file={file},line={line},col={col},"))
            })
            .unwrap_or_default();
        let _ = writeln!(
            out,
            "::warning {where_at}title=Function can panic::{} can panic \
             with {}",
            body.display,
            finding
                .categories
                .iter()
                .map(Category::name)
                .collect::<Vec<_>>()
                .join(", ")
        );
    }
}

/// Explains how one function reaches a panic.
pub fn why(graph: &Graph, solution: &Solution, name: &str, out: &mut String) {
    let matches = graph.find_by_display(name);
    let Some(&id) = matches.first() else {
        let _ = writeln!(out, "No function matching `{name}` was analysed.");
        return;
    };
    if matches.len() > 1 {
        let _ = writeln!(
            out,
            "`{name}` matched {} functions; explaining the first.\n",
            matches.len()
        );
    }

    let body = graph.body(id);
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

/// Lists the categories and what each means.
pub fn kinds(out: &mut String) {
    out.push_str("Panic categories\n\n");
    for category in crate::category::ALL {
        let _ =
            writeln!(out, "  {:<18} {}", category.name(), category.describe());
    }
    out.push_str(
        "\nGroup aliases: `oom` covers capacity-overflow and alloc-failure, \
         `default` adds ub-check, `all` covers everything.\n",
    );
}

/// Renders a flag as text.
const fn on_off(value: bool) -> &'static str {
    if value { "on" } else { "off" }
}

/// Suppressed categories that were nonetheless observed, for the hint line.
#[must_use]
pub fn suppressed_hint(
    graph: &Graph,
    solution: &Solution,
    args: &Args,
) -> Option<String> {
    if args.suppress.is_empty() {
        return None;
    }
    let hidden = graph
        .iter()
        .filter(|(_, body)| body.local && !body.opaque)
        .filter(|(id, _)| solution.enabled(*id).is_empty())
        .count();
    (hidden > 0).then(|| {
        format!(
            "{hidden} local functions panic only through suppressed \
             categories ({}).",
            args.suppress
        )
    })
}
