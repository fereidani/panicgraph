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
    let root = crate_root(args)?;
    let layout = prepare(&root, &driver, args)?;

    build(args, &driver, &root, &layout)?;
    let mut artifacts = load(&layout.out)?;

    if artifacts.is_empty() {
        // Cargo recompiles nothing when the build is already current, so the
        // wrapper never runs and records nothing. Discarding the analysis
        // build is the only way to observe a crate that is already cached.
        clear(&layout.target)?;
        build(args, &driver, &root, &layout)?;
        artifacts = load(&layout.out)?;
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

/// Runs one analysis build.
fn build(
    args: &Args,
    driver: &Path,
    root: &Path,
    layout: &Layout,
) -> Result<()> {
    let mut cmd = Command::new("cargo");
    cmd.current_dir(root)
        .arg("build")
        .arg("--profile")
        .arg(cargo_profile(&args.profile))
        .arg("--target-dir")
        .arg(&layout.target);

    if let Some(pkg) = &args.package {
        cmd.arg("--package").arg(pkg);
    }
    if args.std_mode == StdMode::Full {
        cmd.arg("-Z")
            .arg("build-std=core,alloc,std")
            .arg("--target")
            .arg(host_triple()?);
    }

    cmd.env("RUSTC_WRAPPER", driver)
        .env("PANICGRAPH_OUT", &layout.out)
        .env("PANICGRAPH_PROFILE", &args.profile)
        .env("PANICGRAPH_STD_MODE", args.std_mode.name());
    if let Some(toolchain) = TOOLCHAIN {
        cmd.env("RUSTUP_TOOLCHAIN", toolchain);
    }
    if let Some(path) = library_path()? {
        cmd.env("LD_LIBRARY_PATH", path);
    }

    let status = cmd
        .status()
        .context("could not run cargo; is it on the PATH?")?;
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
        "{}-{}-{}",
        args.profile,
        args.std_mode.name(),
        args.package.as_deref().unwrap_or("all"),
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
    Ok(match args.std_mode {
        StdMode::Full => shared_build_dir()?
            .map_or_else(|| (base.join("build"), false), |tree| (tree, true)),
        StdMode::Shipped => (base.join("build"), false),
    })
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
fn shared_build_dir() -> Result<Option<PathBuf>> {
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
    Ok(Some(base.join(format!("build-{fingerprint}"))))
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
