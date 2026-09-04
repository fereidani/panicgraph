//! Command line parsing.

#[cfg(feature = "serve")]
use std::net::{IpAddr, Ipv4Addr, SocketAddr, ToSocketAddrs};
use std::path::PathBuf;

#[cfg(feature = "serve")]
use anyhow::Context;
use anyhow::{Result, bail};
use clap::{Args as Group, Parser, Subcommand, ValueEnum};

use crate::{CategorySet, StdMode, parse_selector};

/// Trailing help that explains the shared vocabulary once.
const SELECTOR_HELP: &str = "\
A category LIST is comma separated. It accepts category names plus the group
aliases `oom`, `assumed`, `default`, and `all`. Run `panicgraph kinds` for the
names.

Allocation failure, capacity overflow, and standard library precondition
checks are assumed impossible by default: every growable collection reaches
the first two, and the third only exists in a standard library built with
undefined behaviour checks enabled. Pass `--suppress ''` to see everything.

EXIT CODES
  0  nothing to report
  1  findings, or a failed check
  2  the tool could not complete
";

/// The layout of the help text, with the version named on the first line
/// so that the help says which release it describes.
const HELP_TEMPLATE: &str = "\
{before-help}{name} {version}
{about-with-newline}
{usage-heading} {usage}

{all-args}{after-help}";

/// Reports which functions can panic, why, and through what call path.
#[derive(Debug, Parser)]
#[command(name = "panicgraph", version, about, long_about = None)]
#[command(after_help = SELECTOR_HELP, help_template = HELP_TEMPLATE)]
#[command(disable_version_flag = true)]
pub struct Cli {
    /// What to do. Reports the findings when omitted.
    #[command(subcommand)]
    pub command: Option<Command>,

    /// Print the version.
    // Declared by hand rather than left to the default so that the short
    // form is the lower case letter as well as the upper case one.
    #[arg(
        short = 'v',
        short_alias = 'V',
        long,
        action = clap::ArgAction::Version,
        global = true
    )]
    pub version: (),

    #[command(flatten)]
    pub scope: Scope,

    #[command(flatten)]
    pub policy: Policy,

    /// Serve an interactive view instead of printing.
    ///
    /// A bare port binds the loopback interface only. Listening more widely
    /// has to be asked for, because this serves the source of the crate
    /// being analysed.
    #[cfg(feature = "serve")]
    #[arg(short = 'l', long, value_name = "PORT|HOST:PORT", global = true)]
    pub listen: Option<String>,

    /// How to render the result.
    #[arg(long, value_enum, default_value_t = Format::Human, global = true)]
    pub format: Format,
}

/// Which crate, and how it is built.
#[derive(Debug, Clone, Group)]
pub struct Scope {
    /// Directory of the crate to analyse.
    #[arg(long, value_name = "DIR", global = true)]
    pub manifest_dir: Option<PathBuf>,

    /// Cargo package to analyse.
    #[arg(short, long, value_name = "PKG", global = true)]
    pub package: Option<String>,

    /// Cargo profile to analyse.
    ///
    /// The profile decides the answer: overflow checks do not exist in a
    /// build that has them turned off.
    #[arg(long, default_value = "release", global = true)]
    pub profile: String,

    /// How the standard library is supplied.
    ///
    /// Defaults to the shipped library, and to `full` for `check` and
    /// `baseline`, which read the categories rather than the count.
    #[arg(long = "std", value_enum, global = true)]
    pub std_mode: Option<Std>,

    /// The compiler's MIR optimization level to build the analysis with.
    ///
    /// The compiler settles some checks itself before the analysis reads a
    /// body, and a higher level settles more: level 3 turns on its own
    /// dataflow constant propagation. The artifact then differs from the
    /// one a plain build produces, so the report names the level.
    #[arg(long, value_name = "N", value_parser = clap::value_parser!(u8).range(0..=4), global = true)]
    pub mir_opt_level: Option<u8>,

    /// Build the crate's test targets as well, so the instantiations they
    /// make of its generic functions join the analysis.
    ///
    /// Only those instantiations are reported: the tests themselves are
    /// not, and the crate's own code compiled again for its unit tests is
    /// not reported twice. A test build needs the dev-dependencies; one
    /// that fails is said so and left out rather than failing the
    /// analysis.
    #[arg(long, global = true)]
    pub with_tests: bool,
}

/// What the analysis is allowed to assume.
#[derive(Debug, Clone, Group)]
#[allow(
    clippy::struct_excessive_bools,
    reason = "each flag is an independent, orthogonal policy choice"
)]
pub struct Policy {
    /// Categories to assume impossible.
    #[arg(long, value_name = "LIST", default_value = "default", global = true)]
    pub suppress: String,

    /// Report only these categories.
    #[arg(long, value_name = "LIST", global = true)]
    pub only: Option<String>,

    /// Ignore vtable and function pointer edges.
    #[arg(long, global = true)]
    pub static_only: bool,

    /// Follow candidate targets for dyn and function pointer calls.
    ///
    /// Candidates are every concrete implementation of the trait and every
    /// reachable function reified to a pointer of a matching signature. The
    /// dyn-call and fn-pointer categories remain either way: candidates
    /// narrow what the unknown code could be, they do not close the set.
    #[arg(long, global = true)]
    pub candidates: bool,

    /// Check each finding against the compiled artifact and say which
    /// survived the optimizer.
    ///
    /// A finding the artifact confirms still calls a panic entry point; an
    /// absent one was removed by the optimizer; the rest cannot be settled
    /// at the binary level. The verdict annotates the finding, it never
    /// removes it.
    #[arg(long, global = true)]
    pub verify: bool,

    /// How closures report: as their own functions, or folded into the
    /// function each is written in.
    ///
    /// Separate is the precise view: a panic contained by a catch belongs
    /// to the closure, and folding it upward would pin it on a caller that
    /// cannot raise it. Parent is the compact view for triage.
    #[arg(long, value_enum, default_value = "separate", global = true)]
    pub closures: Closures,

    /// Include dependencies, not just the local crate.
    #[arg(long, global = true)]
    pub all_crates: bool,

    /// How a generic function reports: as written, or through the
    /// instantiations the build makes of it.
    ///
    /// As written, a generic body is read with its parameters left open, so
    /// a check on a const parameter or on the size of a type parameter can
    /// fail and a call through a bound is unknown. Instantiated reports
    /// what the build's own uses of the function do, and falls back to the
    /// written body only for a function nothing instantiates. Test crates
    /// count as uses under `--with-tests`.
    #[arg(long, value_enum, default_value = "written", global = true)]
    pub generics: Generics,
}

/// What the user asked the tool to do.
#[derive(Debug, Clone, Subcommand)]
pub enum Command {
    /// Report every function that can panic.
    Analyze,

    /// Explain how one function reaches a panic.
    Why {
        /// Part of the function's path, for example `parse` or `Vec::push`.
        function: String,
    },

    /// Fail when functions that must not panic can.
    ///
    /// With no gate given, no function in the crate may panic, which is the
    /// check an allocation free or embedded crate wants.
    Check(Check),

    /// Write the current findings so later runs can gate on changes.
    Baseline {
        /// Where to write them.
        #[arg(value_name = "FILE")]
        file: PathBuf,
    },

    /// List the panic categories and what they mean.
    Kinds,
}

/// The gates a check applies.
///
/// The default gates nothing, which is what `baseline` wants: it records the
/// findings rather than judging them.
#[derive(Debug, Clone, Default, Group)]
pub struct Check {
    /// Functions matching this pattern must not panic. May be repeated.
    #[arg(long, value_name = "REGEX")]
    pub forbid: Vec<String>,

    /// Functions matching this pattern are exempt. May be repeated.
    ///
    /// Applied after the forbidding patterns, so a broad rule can carry a
    /// short list of known exceptions rather than being weakened.
    #[arg(long, value_name = "REGEX")]
    pub allow: Vec<String>,

    /// Fail when more than this many functions can panic.
    #[arg(long, value_name = "N")]
    pub max: Option<usize>,

    /// Fail only on findings absent from this file.
    #[arg(long, value_name = "FILE")]
    pub baseline: Option<PathBuf>,

    /// Treat a function that reaches code the analysis could not read as a
    /// failure.
    ///
    /// This covers every assumed category: unknown, foreign, dyn-call,
    /// fn-pointer, and generic-bound. None of them means clean; each names
    /// where visibility ended.
    #[arg(long)]
    pub fail_on_unknown: bool,
}

/// How generic functions report.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum Generics {
    /// The body as written, with its parameters left open.
    Written,
    /// The instantiations the build makes, falling back to the written body
    /// where there are none.
    Instantiated,
}

impl Generics {
    /// The name used on the command line and in reports.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Written => "written",
            Self::Instantiated => "instantiated",
        }
    }
}

/// How closures report.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum Closures {
    /// Each closure reports as its own function.
    Separate,
    /// A closure reports under the function it is written in.
    Parent,
}

impl Command {
    /// The name used on the command line and in messages.
    #[must_use]
    pub const fn name(&self) -> &'static str {
        match self {
            Self::Analyze => "analyze",
            Self::Why { .. } => "why",
            Self::Check(_) => "check",
            Self::Baseline { .. } => "baseline",
            Self::Kinds => "kinds",
        }
    }
}

impl Closures {
    /// The name used on the command line and in reports.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Separate => "separate",
            Self::Parent => "parent",
        }
    }
}

/// Output rendering.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum Format {
    /// Human readable text.
    Human,
    /// Machine readable JSON.
    Json,
    /// Workflow commands a continuous integration log will annotate.
    Github,
    /// A standalone flame graph that can be opened or attached to a report.
    #[cfg(feature = "svg")]
    Svg,
}

/// The standard library a command reads when the user does not name one.
///
/// A gate is read by its category names, not its count, and the shipped
/// library hides them: a reachable `unwrap` inside it reports as `unknown`.
/// Rebuilding costs one sub-minute build that later runs reuse, so `check`
/// and `baseline` pay it. They also have to agree with each other, since a
/// baseline written against one library disagrees with a check run against
/// the other about every function.
const fn default_std(command: &Command) -> StdMode {
    match command {
        Command::Check(_) | Command::Baseline { .. } => StdMode::Full,
        _ => StdMode::Shipped,
    }
}

/// How the standard library is supplied.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum Std {
    /// The precompiled library shipped with the toolchain.
    Shipped,
    /// Rebuilt from source with its bodies kept, so nothing is opaque.
    Full,
}

impl From<Std> for StdMode {
    fn from(value: Std) -> Self {
        match value {
            Std::Shipped => Self::Shipped,
            Std::Full => Self::Full,
        }
    }
}

/// The resolved settings the rest of the program reads.
#[derive(Debug, Clone)]
#[allow(
    clippy::struct_excessive_bools,
    reason = "each flag is an independent, orthogonal policy choice"
)]
pub struct Args {
    /// The subcommand.
    pub command: Command,
    /// Categories assumed impossible.
    pub suppress: CategorySet,
    /// When set, only these categories are reported.
    pub only: Option<CategorySet>,
    /// Cargo profile to analyse.
    pub profile: String,
    /// How the standard library is supplied.
    pub std_mode: StdMode,
    /// The compiler's MIR optimization level, when one was asked for.
    pub mir_opt_level: Option<u8>,
    /// Build the test targets too, for the instantiations they make.
    pub with_tests: bool,
    /// How generic functions report.
    pub generics: Generics,
    /// Output rendering.
    pub format: Format,
    /// Ignore vtable and function pointer edges.
    pub static_only: bool,
    /// Follow candidate targets for dyn and function pointer calls.
    pub candidates: bool,
    /// Annotate findings with what the compiled artifact still contains.
    pub verify: bool,
    /// How closures report.
    pub closures: Closures,
    /// Report functions from dependencies as well as the local crate.
    pub all_crates: bool,
    /// Directory holding the crate to analyse.
    pub manifest_dir: Option<PathBuf>,
    /// Cargo package to analyse.
    pub package: Option<String>,
    /// When set, serve an interactive view on this address.
    #[cfg(feature = "serve")]
    pub listen: Option<SocketAddr>,
}

impl Cli {
    /// Resolves the parsed command line into the settings used downstream.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown category name or a listen address
    /// that does not resolve.
    pub fn resolve(self) -> Result<Args> {
        #[cfg(feature = "serve")]
        let listen = self.listen.as_deref().map(listen_addr).transpose()?;
        let only = self.policy.only.as_deref().map(selector).transpose()?;
        let command = self.command.unwrap_or(Command::Analyze);
        // A drawing is a picture of the whole graph, so it is the report
        // and nothing else. Rendering prose instead would answer a question
        // that was not asked.
        // The view is the graph with the report drawn over it, so there
        // is nothing for it to show of a command that answers one question.
        #[cfg(feature = "serve")]
        if listen.is_some() && !matches!(command, Command::Analyze) {
            bail!(
                "`--listen` serves the graph, so it belongs to the analysis \
                 rather than to `{}`",
                command.name()
            );
        }
        if self.format == Format::Svg && !matches!(command, Command::Analyze) {
            bail!(
                "`--format svg` draws the whole graph, so it belongs \
                 to the analysis rather than to `{}`",
                command.name()
            );
        }
        let std_mode = self
            .scope
            .std_mode
            .map_or_else(|| default_std(&command), StdMode::from);
        Ok(Args {
            command,
            suppress: selector(&self.policy.suppress)?,
            only,
            profile: self.scope.profile,
            std_mode,
            mir_opt_level: self.scope.mir_opt_level,
            with_tests: self.scope.with_tests,
            generics: self.policy.generics,
            format: self.format,
            static_only: self.policy.static_only,
            candidates: self.policy.candidates,
            verify: self.policy.verify,
            closures: self.policy.closures,
            all_crates: self.policy.all_crates,
            manifest_dir: self.scope.manifest_dir,
            package: self.scope.package,
            #[cfg(feature = "serve")]
            listen,
        })
    }
}

/// Parses arguments, without the program name.
///
/// # Errors
///
/// Returns an error when the arguments are rejected or cannot be resolved.
pub fn parse<I, S>(input: I) -> Result<Args>
where
    I: IntoIterator<Item = S>,
    S: Into<std::ffi::OsString> + Clone,
{
    let mut argv: Vec<std::ffi::OsString> = vec!["panicgraph".into()];
    argv.extend(input.into_iter().map(Into::into));
    Cli::try_parse_from(argv)?.resolve()
}

/// Resolves a `PORT` or `HOST:PORT` listen argument.
///
/// # Errors
///
/// Returns an error if the argument is neither a port number nor an address
/// that resolves.
#[cfg(feature = "serve")]
fn listen_addr(text: &str) -> Result<SocketAddr> {
    if let Ok(port) = text.parse::<u16>() {
        return Ok(SocketAddr::new(IpAddr::V4(Ipv4Addr::LOCALHOST), port));
    }
    let mut resolved = text
        .to_socket_addrs()
        .with_context(|| format!("could not resolve `{text}`"))?;
    match resolved.next() {
        Some(addr) => Ok(addr),
        None => bail!("`{text}` resolved to no address"),
    }
}

/// Parses a comma separated category selector.
fn selector(text: &str) -> Result<CategorySet> {
    match parse_selector(text) {
        Ok(set) => Ok(set),
        Err(bad) => bail!(
            "unknown panic category `{bad}`; run `panicgraph kinds` for \
             the list"
        ),
    }
}
