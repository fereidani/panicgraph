# panicgraph

Reports which functions in a Rust crate can panic, why, and through what call
path. It reads the compiler's own view of the program, so the answer covers
the code you wrote and everything it calls, down into the standard library.

The problem with asking that question honestly is that the answer is "nearly
everything": every `Vec::push` can fail to allocate, so every function that
touches a growable collection is a panicking function. panicgraph's central
idea is that you can assume a category of panic impossible and have the whole
analysis re-run under that assumption, rather than filtering it out of a
finished report.

## Requirements

The analysis is a compiler driver, so it needs a nightly toolchain and the
compiler's own libraries:

```
rustup toolchain install nightly
rustup component add rustc-dev llvm-tools --toolchain nightly
```

A `rust-toolchain.toml` in this repository pins that for you. If you install
from elsewhere, use `cargo +nightly install`. The build stops with an
explanation rather than a linker error when either piece is missing.

## Install

```
cargo install --path .
```

That installs two binaries, `panicgraph` and `panicgraph-driver`. They live
next to each other and both are needed.

### A smaller build for continuous integration

The interactive view and the drawing exist for a person looking at a result.
A build that only needs a verdict can leave them out:

```
cargo install --path . --no-default-features            # report and check only
cargo install --path . --no-default-features -F svg     # keep the drawing
cargo install --path . --no-default-features -F serve   # keep the view
```

Dropping both removes the compression dependency and the scripts the view is
built from, which is most of a megabyte of binary. `-l` and `--format svg`
are then rejected as unknown arguments rather than silently doing nothing.

## Getting started

Run it in a crate:

```
$ panicgraph
Analysis
    rustc              1.100.0-nightly (f7d782a3b 2026-08-19)
    profile            release (debug assertions off, overflow checks off)
    standard library   shipped
    suppressed         capacity-overflow, alloc-failure, ub-check
    functions          56 analysed, 10 can panic

divz
    defined at src/lib.rs:5:1
    divide-by-zero attempt to divide by zero at src/lib.rs:5:38

expect_res
    defined at src/lib.rs:3:1
    unwrap reached through a call
```

The header is part of the answer. Overflow checks do not exist in a build
that has them turned off, so a report that does not name its profile is not
saying anything definite.

## Assuming panics impossible

By default, allocation failure, capacity overflow, and standard library
precondition checks are assumed impossible. Turn that off and the picture
changes:

```
$ panicgraph --suppress ''
    suppressed         nothing
    functions          56 analysed, 12 can panic

push_vec
    defined at src/lib.rs:7:1
    capacity-overflow reached through a call
```

`push_vec` is a one line wrapper around `Vec::push`. With the default policy
it does not appear at all, because the only panic it reaches is one you asked
to assume away.

This is not a display filter. The assumption is applied before the analysis
propagates, so a function that panics only through a suppressed category is
genuinely clean, and so is everything above it. It also reaches into control
flow: a `Drop` that runs only while an allocation failure unwinds becomes
unreachable along with the failure itself.

Select categories by name or by group:

```
panicgraph --suppress foreign           # calls into C
panicgraph --suppress oom               # allocation only
panicgraph --suppress ''                # assume nothing
panicgraph --suppress all               # assume everything, which reports nothing
panicgraph --only unwrap,index          # report just these
panicgraph kinds                        # list the categories
```

## Explaining one function

```
$ panicgraph why unwrap_opt
unwrap_opt can panic with `unwrap`:

  unwrap_opt
      calls std::option::unwrap_failed at .../core/src/option.rs:1014:21
```

For a deeper path this prints each call in turn, marking the ones that run
only while an earlier panic is unwinding.

## Gating a build

`check` fails when a function that must not panic can. With no gate named, no
function in the crate may panic, which is the question an allocation free or
embedded crate asks:

```
$ panicgraph check --forbid '^(idx|divz)$'
2 functions must not panic and can:

divz
    at src/lib.rs:5:1
    divide-by-zero (must not panic)
idx
    at src/lib.rs:1:1
    index (must not panic)

Run `panicgraph why <function>` to see how one of them gets there.
$ echo $?
1
```

Patterns are regular expressions and may be repeated. `--allow` carves known
exceptions out of a broad rule, so the rule can stay broad:

```
panicgraph check --forbid '^api::' --allow '^api::legacy_'
```

Other gates. Naming any of them replaces the default rule rather than
stacking with it, so a ceiling means a ceiling:

```
panicgraph check --max 20               # fail above a ceiling
panicgraph check --fail-on-unknown      # refuse panics the analysis could not classify
```

### Ratcheting an existing crate

Most crates cannot go to zero today. Record what panics now, then fail only
on what is new:

```
panicgraph baseline panicgraph.json
panicgraph check --baseline panicgraph.json
```

A function absent from the record fails. So does one already recorded that
has gained a panic it did not have before, which a record of names alone
would miss. Functions that stop panicking are reported so the file can be
refreshed rather than drifting.

### In a workflow

```yaml
- uses: dtolnay/rust-toolchain@nightly
  with:
    components: rustc-dev, llvm-tools
- run: cargo install --git https://github.com/fereidani/panicgraph
- run: panicgraph check --baseline panicgraph.json --format github
```

`--format github` writes workflow commands, so a failure lands on the line of
the function it is about instead of at the bottom of a log:

```
::error file=src/lib.rs,line=16,col=1,title=Function can panic::newly_added can panic with index (not in the baseline)
```

Exit codes are `0` for nothing to report, `1` for findings or a failed check,
and `2` when the tool could not complete.

## Looking at it

```
panicgraph -l 8080
```

Serves an interactive flame graph: assume categories impossible and watch what
survives, lock the view to a single category, search frames with `ctrl f` and
step through the matches, click a frame for the call path. A bare port binds
the loopback interface only; opening it more widely has to be asked for with
`-l 0.0.0.0:8080`, because it serves the source of the crate being analysed.

For something to attach to a report, write a standalone flame graph instead:

```
panicgraph --format svg > panics.svg
```

The file carries its own styling and behaviour, so it opens from disk with
nothing else present, and every frame keeps a title so it still explains
itself when scripting is off.

Machine readable output is available everywhere with `--format json`.

## Checking findings against the compiled artifact

This is a may-panic analysis over MIR, and the optimizer sees further than
the folder does. `--verify` disassembles the libraries the analysis build
produced and follows each finding into the machine code:

```
verify_absent_loop
    index reached through a call (absent from the compiled artifact)
must_index
    index index out of bounds at src/lib.rs:10:5 (confirmed in the compiled artifact)
```

A confirmed finding still calls a panic entry point in the artifact. An
absent one was removed by the optimizer: every call the compiled function
makes was accounted for and none reaches a panic. Everything else is
unverified, which includes calls through registers, code the sweep cannot
see into, and categories that leave no symbol behind, such as a reference
count overflow's inlined trap. The verdict annotates the finding and never
removes it: absence from one artifact is a fact about that build, not a
proof about the source.

## How it works

The analysis runs as a compiler driver invoked through `RUSTC_WRAPPER`, over
monomorphized MIR. Panic reasons come from the compiler's own `Assert`
terminators and from calls to panic entry points resolved by identity, not by
matching symbol names, which drift between releases.

Reachability is a fixpoint over the call graph: each function gets the set of
panic categories it can raise, unioned from everything it calls. Drop glue is
followed. Suppression removes categories before that propagation runs, and
cleanup paths are gated on the panic that unwinds into them.

Checks that are not in the build are not reported. The standard library ships
one copy of its MIR for every crate that uses it, so a body can carry an
overflow check or a precondition check that the crate being analysed compiles
away, and a check written against `size_of::<T>()` is still a branch there
even though it settles to a constant for every real `T`. Each body is folded
against the arguments it was reached with and the settings of the build in
front of it, the way codegen resolves them, so a branch neither can take is
not walked. A test carries into the arm it guards, so a division below
`if divisor != 0` raises nothing.

The driver injects `-Zalways-encode-mir`. Without it, a dependency keeps MIR
only for generic and small items, so its concrete functions are opaque and
the panics inside them cannot be seen.

## Limitations

Read these before trusting a clean result.

- **The default standard library is partly opaque.** Concrete functions in
  `std` ship without MIR, so panics inside them are reported as `unknown`
  rather than proven absent. `--std full` rebuilds it from source with its
  bodies kept, which costs one build per toolchain: the tree is cached
  under the user's cache directory (`PANICGRAPH_CACHE` overrides where)
  and shared by every project on the machine. `check` and
  `baseline` do this by default, because a gate is read by its category
  names: with the shipped library a reachable `unwrap` reports as `unknown`.
  It does not remove `unknown`, it names it, so expect the same functions
  reported with sharper reasons.
- **`unknown` is not `clean`.** It means the analysis could not see inside
  something. `check --fail-on-unknown` refuses to treat the two alike.
- **Dynamic dispatch is not resolved, only named.** A `dyn Trait` call
  reports `dyn-call` and a function pointer call reports `fn-pointer`.
  `--candidates` expands both: every concrete implementation of the trait,
  and every reachable function reified to a pointer of a matching
  signature, joins the graph as a candidate edge, so the report shows what
  the call could actually do. The category stays either way, because
  candidates narrow the unknown rather than close it, and `--static-only`
  still drops the edges entirely. A call a generic function makes through
  one of its bounds reports `generic-bound`, since which implementation
  runs is the caller's choice. Each of these names where visibility ended;
  `--suppress assumed` assumes them all, and `check --fail-on-unknown`
  refuses them all.
- **This is a may-panic analysis.** A panic that is unreachable for reasons
  the compiler cannot see is still reported. It answers "could this panic",
  not "will it". Folding settles a check against constants and against what a
  branch above it proves, and nothing more: an invariant that holds for
  reasons spread across several functions is still reported.
- **The toolchain is pinned.** The driver links against compiler internals,
  which have no stable interface, so it is built for one nightly at a time.
  Updating the toolchain means reinstalling; the tool says so rather than
  leaving the loader to report a missing library.

## License

Copyright 2026 Khashayar Fereidani.

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or
[MIT license](LICENSE-MIT) at your option.

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in this crate by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
