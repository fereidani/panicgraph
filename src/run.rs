//! Drives a cargo build through the analysis wrapper and loads the results.

use std::{
    env,
    ffi::OsString,
    fs, path,
    path::{Path, PathBuf},
    process::Command,
};

use anyhow::{Context, Result, bail, ensure};

use crate::{Artifact, StdMode, args::Args};

/// The toolchain this tool was built with.
///
/// The driver links against a specific compiler, so the analysis build has to
/// run under that same toolchain. Without this, cargo would pick whatever the
/// analysed crate's directory resolves to and the driver would be handed a
/// sysroot it cannot read.
const TOOLCHAIN: Option<&str> = option_env!("RUSTUP_TOOLCHAIN");

/// The compiler this tool was built against, as `rustc --version` prints it.
///
/// Absent when the build could not ask, in which case the check is skipped
/// rather than guessed at.
const BUILT_AGAINST: Option<&str> = option_env!("PANICGRAPH_RUSTC");

/// Where the driver writes artifacts and where the analysis build happens.
struct Layout {
    out: PathBuf,
    target: PathBuf,
    /// Whether the build tree is the one every project shares, which goes
    /// stale on its own terms rather than with one project's artifacts.
    shared: bool,
}

/// The crate under analysis and the tree it is built in.
struct Workspace {
    /// The directory the analysis build runs in.
    root: PathBuf,
    /// Whether the tree is the standard library's own workspace.
    ///
    /// The library's build applies rules of its own to every crate in the
    /// workspace, and the analysis build has to apply the same or the
    /// library does not compile.
    library: bool,
}

impl Workspace {
    /// Locates the crate under analysis and tells which tree it is in.
    fn locate(args: &Args) -> Result<Self> {
        let root = crate_root(args)?;
        let library = is_library_workspace(&root)?;
        Ok(Self { root, library })
    }
}

/// Builds the crate under the wrapper and returns every artifact produced.
///
/// # Errors
///
/// Returns an error if the driver is missing, the build fails, or an
/// artifact cannot be read.
pub fn collect(args: &Args) -> Result<Vec<Artifact>> {
    let driver = driver_path()?;
    check_toolchain()?;
    // The analysis build runs in the crate's own directory, so a relative
    // path here would resolve against that rather than against where the
    // tool was started: the artifacts would be written one tree deeper than
    // they are read back from, and the run would either report nothing or
    // report whatever an earlier run left behind.
    let workspace = Workspace::locate(args)?;
    let layout = prepare(&workspace.root, &driver, args)?;

    build(args, &driver, &workspace, &layout, false)?;
    let mut artifacts = load(&layout.out)?;

    if artifacts.is_empty() {
        // Cargo recompiles nothing when the build is already current, so the
        // wrapper never runs and records nothing. Discarding the analysis
        // build is the only way to observe a crate that is already cached.
        clear(&layout.target)?;
        build(args, &driver, &workspace, &layout, false)?;
        artifacts = load(&layout.out)?;
    }

    if args.with_tests {
        // The tests need the dev-dependencies and may not build at all,
        // and what they add is more instantiations rather than the crate
        // itself, so a failure is said and the analysis goes on without.
        if let Err(err) = build(args, &driver, &workspace, &layout, true) {
            eprintln!(
                "warning: the test targets could not be built, so their \
                 instantiations are left out: {err:#}"
            );
        } else {
            artifacts = load(&layout.out)?;
        }
    }

    if artifacts.is_empty() {
        bail!("the build produced no analysis artifacts");
    }
    Ok(artifacts)
}

/// The directory of the crate under analysis.
fn crate_root(args: &Args) -> Result<PathBuf> {
    args.manifest_dir.as_ref().map_or_else(
        || {
            env::current_dir()
                .context("could not determine the current directory")
        },
        |dir| {
            path::absolute(dir)
                .with_context(|| format!("could not resolve {}", dir.display()))
        },
    )
}

/// Whether a directory builds in the standard library's own workspace.
///
/// Cargo names the workspace manifest, and the manifest says. A manifest
/// cargo cannot read fails the build itself, with cargo's own diagnosis,
/// so it is not judged here.
fn is_library_workspace(root: &Path) -> Result<bool> {
    let mut cmd = cargo(root);
    cmd.args(["locate-project", "--workspace", "--message-format", "plain"]);
    let out = cmd
        .output()
        .context("could not run cargo; is it on the PATH?")?;
    if !out.status.success() {
        return Ok(false);
    }
    let path =
        String::from_utf8(out.stdout).context("cargo printed invalid utf-8")?;
    let path = path.trim();
    if path.is_empty() {
        return Ok(false);
    }
    let manifest = fs::read_to_string(path)
        .with_context(|| format!("could not read {path}"))?;
    Ok(is_library_manifest(&manifest))
}

/// The table in which the standard library's workspace replaces the shim
/// crate its vendored dependencies name with the one in its own tree.
const PATCH_TABLE: &str = "patch.crates-io";

/// The same patch, written as a table of its own.
const PATCH_ENTRY: &str = "patch.crates-io.rustc-std-workspace-core";

/// The shim crate the library's vendored dependencies stand on.
const LIBRARY_SHIM: &str = "rustc-std-workspace-core";

/// Whether a workspace manifest is the standard library's own.
///
/// The crates vendored into the library depend on a shim crate that the
/// library's workspace, and nothing else, patches in from its own tree.
/// Depending on the shim is what a vendored crate does, so only the patch
/// tells. The manifest is scanned by table rather than parsed, since two
/// names in one table are all there is to find.
#[must_use]
pub fn is_library_manifest(manifest: &str) -> bool {
    let mut patching = false;
    for line in manifest.lines() {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix('[') {
            let table = rest.split(']').next().unwrap_or_default();
            if spells(table, PATCH_ENTRY) {
                return true;
            }
            patching = spells(table, PATCH_TABLE);
        } else if patching {
            let key = line.split('=').next().unwrap_or_default();
            if spells(key, LIBRARY_SHIM) {
                return true;
            }
        }
    }
    false
}

/// Whether a name in a manifest reads as `name` once quoting is dropped.
fn spells(text: &str, name: &str) -> bool {
    text.chars()
        .filter(|c| !matches!(c, '"' | '\'' | ' ' | '\t'))
        .eq(name.chars())
}

/// Where the analysis build for these settings compiles into.
///
/// # Errors
///
/// Returns an error when the crate directory cannot be resolved.
pub fn build_tree(args: &Args) -> Result<PathBuf> {
    let root = crate_root(args)?;
    analysis_target(&root, args).map(|(tree, _)| tree)
}

/// Reports a toolchain that has moved since this tool was installed.
///
/// The driver links the compiler's own libraries, which carry the hash of the
/// build they came from, so a toolchain update leaves it unable to start at
/// all. Saying so here turns a loader error naming a missing file into the
/// one instruction that fixes it.
fn check_toolchain() -> Result<()> {
    let (Some(built), Some(current)) = (BUILT_AGAINST, rustc_version()?) else {
        return Ok(());
    };
    ensure!(
        current == built,
        "this tool was built against {built}, but the toolchain now offers \
         {current}. The analysis driver links that compiler's own libraries \
         and cannot run against another build of it, so reinstall with \
         `cargo install --path .`"
    );
    Ok(())
}

/// The compiler's version, as `rustc --version` prints it.
fn rustc_version() -> Result<Option<String>> {
    let text = rustc_output(&["--version"])?;
    let line = text.lines().next().unwrap_or_default().trim().to_owned();
    Ok((!line.is_empty()).then_some(line))
}

/// Runs one analysis build, of the crate itself or of its test targets.
fn build(
    args: &Args,
    driver: &Path,
    workspace: &Workspace,
    layout: &Layout,
    tests: bool,
) -> Result<()> {
    let mut cmd = cargo(&workspace.root);
    cmd.arg("build")
        .arg("--profile")
        .arg(cargo_profile(&args.profile))
        .arg("--target-dir")
        .arg(&layout.target);

    // Benches are left out: one without the harness is an ordinary
    // binary, and everything in it would then be reported as the crate's
    // own.
    if tests {
        cmd.arg("--tests");
    }
    if let Some(pkg) = &args.package {
        cmd.arg("--package").arg(pkg);
    }
    if args.features.all {
        cmd.arg("--all-features");
    }
    if args.features.no_default {
        cmd.arg("--no-default-features");
    }
    if !args.features.named.is_empty() {
        cmd.arg("--features").arg(args.features.named.join(","));
    }
    if args.std_mode == StdMode::Full {
        cmd.arg("-Z")
            .arg("build-std=core,alloc,std")
            .arg("--target")
            .arg(host_triple()?);
    }

    // The build reads nothing from standard input, so it is handed a pipe
    // with nothing behind it rather than what the caller left there, and
    // rather than the null device, which is not on every machine what it
    // should be.
    cmd.stdin(std::process::Stdio::piped())
        .env("RUSTC_WRAPPER", driver)
        .env("PANICGRAPH_OUT", &layout.out)
        .env("PANICGRAPH_PROFILE", &args.profile)
        .env("PANICGRAPH_STD_MODE", args.std_mode.name());
    if let Some(level) = args.mir_opt_level {
        cmd.env("PANICGRAPH_MIR_OPT_LEVEL", level.to_string());
    }
    if workspace.library {
        cmd.env("PANICGRAPH_LIBRARY_WORKSPACE", "1");
    }
    if let Some(path) = library_path()? {
        cmd.env("LD_LIBRARY_PATH", path);
    }

    let mut child = cmd
        .spawn()
        .context("could not run cargo; is it on the PATH?")?;
    // Closing the writing end at once is what makes the pipe read as
    // empty: nothing is ever written, and a reader sees the end.
    drop(child.stdin.take());
    let status = child.wait().context("could not wait for cargo")?;
    if !status.success() {
        bail!("the analysis build failed; the errors above are from cargo");
    }
    Ok(())
}

/// Name of the marker written into every directory this version owns.
///
/// Earlier versions wrote artifacts into differently named directories, and
/// those linger as caches nothing will ever read again. The marker tells the
/// two apart without having to guess from the directory name.
const SLOT_MARKER: &str = ".panicgraph-slot";

/// Creates the directories the analysis build writes into.
///
/// Artifacts are deliberately kept between runs. Each is named after the
/// crate that produced it, so cargo rewrites exactly the ones it recompiles
/// and the rest stay valid.
fn prepare(root: &Path, driver: &Path, args: &Args) -> Result<Layout> {
    // Artifacts are kept between runs, so the directory has to separate
    // every input that changes what they describe. The standard library mode
    // changes how crates are compiled and so changes their symbol names, and
    // a different package selection analyses a different program: merging
    // those would silently report one crate's panics against another's.
    let base = root.join("target").join("panicgraph");
    let slot = format!(
        "{}-{}-{}{}{}{}",
        args.profile,
        args.std_mode.name(),
        args.package.as_deref().unwrap_or("all"),
        mir_opt_suffix(args),
        if args.with_tests { "-tests" } else { "" },
        feature_suffix(args),
    );
    let (target, shared) = analysis_target(root, args)?;
    let layout = Layout {
        out: base.join(&slot),
        target,
        shared,
    };
    let stamp = driver_stamp(driver);
    let marker = format!("{slot}\n{stamp}\n");
    discard_if_stale(&layout, &marker, &stamp)?;
    fs::create_dir_all(&layout.out).with_context(|| {
        format!("could not create {}", layout.out.display())
    })?;
    fs::write(layout.out.join(SLOT_MARKER), marker.as_bytes()).with_context(
        || format!("could not write the marker in {}", layout.out.display()),
    )?;
    prune_stale(&base, &layout);
    Ok(layout)
}

/// Identifies the build of the driver that produced a set of artifacts.
///
/// Cargo does not rebuild a crate because the wrapper changed, so results
/// written by an earlier driver would be read back as though the current one
/// had produced them. Size and modification time distinguish the two without
/// reading the whole binary.
fn driver_stamp(driver: &Path) -> String {
    let Ok(meta) = fs::metadata(driver) else {
        return "unknown".to_owned();
    };
    let modified = meta
        .modified()
        .ok()
        .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
        .map_or(0, |d| d.as_nanos());
    format!("{}-{modified}", meta.len())
}

/// Throws away results a different driver wrote.
///
/// Both directories go: the artifacts because they describe an analysis this
/// driver did not perform, and the build tree because cargo would otherwise
/// consider every crate current and never run the wrapper again.
///
/// A shared build tree is the exception. It belongs to no one project, so it
/// is judged by the driver alone: keying it on a slot as well would have
/// each project in turn discard the standard library the last one rebuilt,
/// which is the one cost the sharing exists to pay once.
fn discard_if_stale(layout: &Layout, marker: &str, stamp: &str) -> Result<()> {
    let path = layout.out.join(SLOT_MARKER);
    let fresh = layout.out.exists()
        && fs::read_to_string(&path).is_ok_and(|found| found == marker);
    if !fresh {
        clear(&layout.out)?;
        if !layout.shared {
            clear(&layout.target)?;
        }
    }
    if layout.shared {
        discard_shared_if_stale(&layout.target, stamp)?;
    }
    Ok(())
}

/// Throws away a shared build tree an earlier driver filled.
fn discard_shared_if_stale(target: &Path, stamp: &str) -> Result<()> {
    let path = target.join(SLOT_MARKER);
    if target.exists()
        && !fs::read_to_string(&path).is_ok_and(|found| found == stamp)
    {
        clear(target)?;
    }
    fs::create_dir_all(target)
        .with_context(|| format!("could not create {}", target.display()))?;
    fs::write(&path, stamp.as_bytes()).with_context(|| {
        format!("could not write the marker in {}", target.display())
    })
}

/// Removes a directory and everything under it, if it is there at all.
///
/// The tree is moved aside before it is taken apart. Two runs against the
/// same crate can each decide to discard the same stale results, and pulling
/// a tree apart while another process walks it fails part way through. The
/// rename is atomic, so exactly one run owns the old tree and the other
/// finds nothing to move; a directory that has already gone is the result
/// this asks for, however it went.
fn clear(dir: &Path) -> Result<()> {
    let (Some(parent), Some(name)) = (dir.parent(), dir.file_name()) else {
        return Ok(());
    };
    let aside = parent.join(format!(
        "{}.discarded-{}",
        name.to_string_lossy(),
        std::process::id()
    ));
    match fs::rename(dir, &aside) {
        Ok(()) => {}
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => {
            return Ok(());
        }
        Err(err) => {
            return Err(err)
                .with_context(|| format!("could not clear {}", dir.display()));
        }
    }
    // The tree carries this run's own name now, so nothing else is walking
    // it and only the housekeeping sweep can have taken it first.
    match fs::remove_dir_all(&aside) {
        Ok(()) => Ok(()),
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(err) => Err(err)
            .with_context(|| format!("could not remove {}", aside.display())),
    }
}

/// Removes result directories that no version in use writes to any more.
///
/// A directory is kept when it holds the marker, which every current slot
/// carries, and when it is a build tree, shared or local. Anything else was
/// written by an older layout and would otherwise sit on disk forever.
fn prune_stale(base: &Path, layout: &Layout) {
    let Ok(entries) = fs::read_dir(base) else {
        return;
    };
    for entry in entries.filter_map(Result::ok) {
        let path = entry.path();
        if !path.is_dir()
            || path == layout.out
            || path == layout.target
            || path.file_name().is_some_and(|name| name == "build")
        {
            continue;
        }
        if path.join(SLOT_MARKER).exists() {
            continue;
        }
        if fs::remove_dir_all(&path).is_ok() {
            // Housekeeping, not a result. It goes to the error stream so it
            // cannot land in front of a report something is parsing.
            eprintln!("removed stale results in {}", path.display());
        }
    }
}

/// The tree the analysis build for these settings compiles into.
///
/// Rebuilding the standard library costs one full build and depends only
/// on the toolchain, so that tree is shared across projects rather than
/// paid for once per target directory. The artifacts stay local: they
/// describe one crate.
fn analysis_target(root: &Path, args: &Args) -> Result<(PathBuf, bool)> {
    let base = root.join("target").join("panicgraph");
    let local = base.join(format!("build{}", mir_opt_suffix(args)));
    Ok(match args.std_mode {
        StdMode::Full => shared_build_dir(args)?
            .map_or_else(|| (local.clone(), false), |tree| (tree, true)),
        StdMode::Shipped => (local, false),
    })
}

/// What a build with a chosen set of features is named apart by.
///
/// The features change which code exists, so results built with one set
/// are never read as another's. The name is written with the characters
/// a path is safe to hold; the default set names nothing.
fn feature_suffix(args: &Args) -> String {
    if args.features.is_default() {
        return String::new();
    }
    let safe: String = args
        .features
        .describe()
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '-' })
        .collect();
    format!("-f-{safe}")
}

/// What a build at a chosen MIR optimization level is named apart by.
///
/// The level changes every body the analysis reads, so a tree built at one
/// level is never read as another's; the default level names nothing, so
/// a run that asks for nothing lands where it always did.
fn mir_opt_suffix(args: &Args) -> String {
    args.mir_opt_level
        .map(|level| format!("-mir{level}"))
        .unwrap_or_default()
}

/// The shared tree a rebuilt standard library is compiled into.
///
/// One tree per compiler build, under the user's cache directory, so the
/// cost of `--std full` is paid once per toolchain rather than once per
/// project. `PANICGRAPH_CACHE` overrides the location; a system with no
/// resolvable cache directory falls back to the project's own target tree.
///
/// # Errors
///
/// Returns an error when the compiler's version cannot be read at all.
fn shared_build_dir(args: &Args) -> Result<Option<PathBuf>> {
    let base = env::var_os("PANICGRAPH_CACHE")
        .map(PathBuf::from)
        .or_else(|| {
            env::var_os("XDG_CACHE_HOME")
                .map(|dir| PathBuf::from(dir).join("panicgraph"))
        })
        .or_else(|| {
            env::var_os("HOME").map(|home| {
                PathBuf::from(home).join(".cache").join("panicgraph")
            })
        });
    let Some(base) = base else {
        return Ok(None);
    };
    let version = match BUILT_AGAINST {
        Some(version) => version.to_owned(),
        None => match rustc_version()? {
            Some(version) => version,
            None => return Ok(None),
        },
    };
    let fingerprint: String = version
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '-' })
        .collect();
    Ok(Some(base.join(format!(
        "build-{fingerprint}{}",
        mir_opt_suffix(args)
    ))))
}

/// Reads every artifact in a directory.
///
/// The names are read in sorted order rather than the order the filesystem
/// hands them out. The merge order decides which instantiation of a generic
/// function names the location a report prints, so leaving it to the
/// filesystem would let two machines describe the same build differently.
fn load(dir: &Path) -> Result<Vec<Artifact>> {
    let mut paths: Vec<PathBuf> = Vec::new();
    for entry in fs::read_dir(dir)
        .with_context(|| format!("could not read {}", dir.display()))?
    {
        let path = entry?.path();
        if path.extension().is_some_and(|e| e == "json") {
            paths.push(path);
        }
    }
    paths.sort();

    let mut out = Vec::with_capacity(paths.len());
    for path in paths {
        let text = fs::read(&path)
            .with_context(|| format!("could not read {}", path.display()))?;
        let artifact: Artifact = serde_json::from_slice(&text)
            .with_context(|| format!("could not parse {}", path.display()))?;
        out.push(artifact);
    }
    Ok(out)
}

/// Locates the compiler driver next to this executable.
fn driver_path() -> Result<PathBuf> {
    let exe = env::current_exe().context("could not locate this program")?;
    let dir = exe
        .parent()
        .context("this program has no containing directory")?;
    let driver = dir.join("panicgraph-driver");
    if !driver.exists() {
        bail!(
            "the analysis driver is missing from {}; it is installed \
             alongside this program, so reinstall with `cargo install \
             --path .`",
            dir.display()
        );
    }
    Ok(driver)
}

/// The directory holding the compiler's shared libraries.
///
/// The driver links against the compiler, so this must be on the loader path
/// for it to start at all.
fn library_path() -> Result<Option<OsString>> {
    let Some(sysroot) = sysroot()? else {
        return Ok(None);
    };
    let lib = PathBuf::from(sysroot).join("lib");
    let mut value = lib.into_os_string();
    if let Some(existing) = env::var_os("LD_LIBRARY_PATH") {
        value.push(":");
        value.push(existing);
    }
    Ok(Some(value))
}

/// The compiler's sysroot.
pub(crate) fn sysroot() -> Result<Option<String>> {
    let text = rustc_output(&["--print", "sysroot"])?;
    let text = text.trim();
    Ok((!text.is_empty()).then(|| text.to_owned()))
}

/// The compiler's host target triple.
pub(crate) fn host_triple() -> Result<String> {
    rustc_field("host: ")?.context("rustc did not report a host triple")
}

/// Reads one labelled field from `rustc --version --verbose`.
fn rustc_field(label: &str) -> Result<Option<String>> {
    Ok(rustc_output(&["--version", "--verbose"])?
        .lines()
        .find_map(|l| l.strip_prefix(label))
        .map(str::trim)
        .map(str::to_owned))
}

/// A cargo command in a directory, pinned to this tool's toolchain.
fn cargo(dir: &Path) -> Command {
    let mut cmd = Command::new("cargo");
    cmd.current_dir(dir);
    if let Some(toolchain) = TOOLCHAIN {
        cmd.env("RUSTUP_TOOLCHAIN", toolchain);
    }
    cmd
}

/// Runs the compiler pinned to this tool's toolchain and returns its output.
fn rustc_output(args: &[&str]) -> Result<String> {
    let mut cmd = Command::new("rustc");
    if let Some(toolchain) = TOOLCHAIN {
        cmd.env("RUSTUP_TOOLCHAIN", toolchain);
    }
    let out = cmd.args(args).output().context("could not run rustc")?;
    ensure!(
        out.status.success(),
        "rustc {} failed: {}",
        args.join(" "),
        String::from_utf8_lossy(&out.stderr).trim()
    );
    String::from_utf8(out.stdout).context("rustc printed invalid utf-8")
}

/// The directory cargo writes a profile's output to.
///
/// Cargo names the `dev` profile's directory `debug` and every other
/// profile's directory after the profile itself.
pub(crate) fn profile_dir(profile: &str) -> &str {
    if profile == "dev" { "debug" } else { profile }
}

/// Maps a profile name onto the one cargo expects.
fn cargo_profile(profile: &str) -> &str {
    if profile == "debug" { "dev" } else { profile }
}
