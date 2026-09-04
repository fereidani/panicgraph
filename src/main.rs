//! Reports which functions can panic, why, and through what call path.

use std::{fmt::Write as _, process::ExitCode};

use anyhow::Result;
use clap::Parser;
use panicgraph::{
    Graph, Policy, Solution, Solver,
    args::{Args, Check, Cli, Command},
    check, report, run,
    solve::Edges,
};

/// Nothing to report.
const EXIT_CLEAN: u8 = 0;
/// At least one function can panic, or a check failed.
const EXIT_FINDINGS: u8 = 1;
/// The tool could not complete.
const EXIT_ERROR: u8 = 2;

fn main() -> ExitCode {
    match dispatch() {
        Ok(code) => ExitCode::from(code),
        Err(err) => {
            eprintln!("error: {err:#}");
            ExitCode::from(EXIT_ERROR)
        }
    }
}

/// Parses arguments and runs the requested command.
fn dispatch() -> Result<u8> {
    let args = Cli::parse().resolve()?;
    let mut out = String::new();

    let code = match &args.command {
        Command::Kinds => {
            match args.format {
                panicgraph::args::Format::Json => {
                    report::kinds_json(&mut out)?;
                }
                _ => report::kinds(&mut out),
            }
            EXIT_CLEAN
        }
        #[cfg(feature = "serve")]
        Command::Analyze if args.listen.is_some() => {
            return listen(&args).map(|()| EXIT_CLEAN);
        }
        #[cfg(feature = "svg")]
        Command::Analyze if args.format == panicgraph::args::Format::Svg => {
            // The drawing solves the graph for itself, so solving here as
            // well would run the fixpoint twice for one picture.
            let graph = Graph::from_artifacts(run::collect(&args)?);
            let view = panicgraph::svg::View {
                suppressed: args.suppress,
                only: args.only,
                edges: edges_of(&args),
                fold: true,
                theme: args.theme,
            };
            panicgraph::svg::render(&graph, view, &mut out)?;
            EXIT_CLEAN
        }
        Command::Analyze => analyze(&args, &mut out)?,
        Command::Why { function } => {
            let (graph, solution) = solve(&args)?;
            match args.format {
                panicgraph::args::Format::Json => {
                    report::why_json(&graph, &solution, function, &mut out)?;
                }
                _ => report::why(&graph, &solution, function, &mut out),
            }
            EXIT_CLEAN
        }
        Command::Check(gate) => gate_check(&args, gate, &mut out)?,
        Command::Baseline { file } => {
            let (graph, solution) = solve(&args)?;
            let outcome =
                check::run(&graph, &solution, &args, &Check::default())?;
            check::write_baseline(file, &args, &outcome.findings)?;
            match args.format {
                panicgraph::args::Format::Json => {
                    let doc = serde_json::json!({
                        "recorded": outcome.findings.len(),
                        "baseline": file.display().to_string(),
                    });
                    out.push_str(&serde_json::to_string_pretty(&doc)?);
                    out.push('\n');
                }
                _ => {
                    let _ = writeln!(
                        out,
                        "recorded {} findings in {}",
                        outcome.findings.len(),
                        file.display()
                    );
                }
            }
            EXIT_CLEAN
        }
    };

    print!("{out}");
    Ok(code)
}

/// Applies the gate and reports what failed.
fn gate_check(args: &Args, gate: &Check, out: &mut String) -> Result<u8> {
    let (graph, solution) = solve(args)?;
    let outcome = check::run(&graph, &solution, args, gate)?;
    check::render(&outcome, args, gate, out)?;
    Ok(if outcome.failed() {
        EXIT_FINDINGS
    } else {
        EXIT_CLEAN
    })
}

/// Serves the interactive view.
#[cfg(feature = "serve")]
fn listen(args: &Args) -> Result<()> {
    let Some(addr) = args.listen else {
        return Ok(());
    };
    let artifacts = run::collect(args)?;
    let graph = Graph::from_artifacts(artifacts);
    panicgraph::serve::run(graph, addr, edges_of(args))
}

/// Runs the analysis and renders the report.
fn analyze(args: &Args, out: &mut String) -> Result<u8> {
    let (graph, solution) = solve(args)?;
    let verdicts = if args.verify {
        Some(panicgraph::verify::sweep(
            &run::build_tree(args)?,
            &args.profile,
        )?)
    } else {
        None
    };
    report::analysis(&graph, &solution, args, verdicts.as_ref(), out)?;
    // The hint is prose, so it belongs only in the rendering that is prose.
    // Appending it to json left the output unparseable.
    if matches!(args.format, panicgraph::args::Format::Human)
        && let Some(hint) = report::suppressed_hint(&graph, &solution, args)?
    {
        out.push('\n');
        out.push_str(&hint);
        out.push('\n');
    }
    Ok(if report::any_finding(&graph, &solution, args) {
        EXIT_FINDINGS
    } else {
        EXIT_CLEAN
    })
}

/// The edge policy the arguments describe.
const fn edges_of(args: &Args) -> Edges {
    Edges {
        follow_inexact: !args.static_only,
        candidates: args.candidates,
    }
}

/// Builds the crate, merges the artifacts, and solves the graph.
fn solve(args: &Args) -> Result<(Graph, Solution)> {
    let artifacts = run::collect(args)?;
    let graph = Graph::from_artifacts(artifacts);
    let policy = Policy {
        suppressed: args.suppress,
        edges: edges_of(args),
    };
    let solution = Solver::new(&graph, policy).solve()?;
    Ok((graph, solution))
}
