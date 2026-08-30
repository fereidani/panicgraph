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
aliases `oom`, `default`, and `all`. Run `panicgraph kinds` for the names.

Allocation failure, capacity overflow, and standard library precondition
checks are assumed impossible by default: every growable collection reaches
the first two, and the third only exists in a standard library built with
undefined behaviour checks enabled. Pass `--suppress ''` to see everything.

EXIT CODES
  0  nothing to report
  1  findings, or a failed check
  2  the tool could not complete
";

/// Reports which functions can panic, why, and through what call path.
#[derive(Debug, Parser)]
#[command(name = "panicgraph", version, about, long_about = None)]
#[command(after_help = SELECTOR_HELP)]
pub struct Cli {
    /// What to do. Reports the findings when omitted.
    #[command(subcommand)]
    pub command: Option<Command>,

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
}

/// What the analysis is allowed to assume.
#[derive(Debug, Clone, Group)]
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

    /// Include dependencies, not just the local crate.
    #[arg(long, global = true)]
    pub all_crates: bool,
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

    /// Treat a function whose panics could not be classified as a failure.
    ///
    /// An unclassified panic means the analysis could not see inside
    /// something, not that the function is clean.
    #[arg(long)]
    pub fail_on_unknown: bool,
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
    /// Output rendering.
    pub format: Format,
    /// Ignore vtable and function pointer edges.
    pub static_only: bool,
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
        let listen = match self.listen {
            Some(text) => Some(listen_addr(&text)?),
            None => None,
        };
        let only = match self.policy.only {
            Some(text) => Some(selector(&text)?),
            None => None,
        };
        let command = self.command.unwrap_or(Command::Analyze);
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
            format: self.format,
            static_only: self.policy.static_only,
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
