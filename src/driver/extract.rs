//! Walks MIR and records what each function can panic with, and who it calls.

use panicgraph::{
    Body, CallSite, EdgeKind, FuncKey, Guard, Loc, OPEN_PREFIX, PanicSite,
    Reified, UnwindOrigin,
    util::{Map, Set},
};
use rustc_hir::def_id::DefId;
use rustc_middle::{
    middle::codegen_fn_attrs::CodegenFnAttrFlags,
    mir::{self, AssertKind, BasicBlock, TerminatorKind, UnwindAction},
    ty::{
        self, Instance, TyCtxt, TypeVisitableExt, TypingEnv,
        print::with_no_trimmed_paths,
    },
};
use rustc_span::Spanned;

use self::{
    flow::{resuming, unavoidable},
    sites::classify_assert,
};
use crate::{fold, read::instantiate, sinks::SinkTable, summary::Cache};

mod candidates;
mod flow;
mod sites;

/// One function to analyse, together with the environment its generic
/// arguments belong to.
///
/// A callee resolved from a generic caller carries that caller's parameters,
/// so the two travel together: normalizing the callee's types demands the
/// environment those parameters were declared in.
#[derive(Clone, Copy)]
struct Work<'tcx> {
    inst: Instance<'tcx>,
    env: TypingEnv<'tcx>,
}

/// Where a terminator sits, and where unwinding out of it lands.
///
/// The three travel together from the moment a terminator is read until the
/// entry it produces is recorded, so they are carried as one value.
#[derive(Clone, Copy)]
struct At {
    bb: BasicBlock,
    unwind: UnwindAction,
    span: rustc_span::Span,
    scope: mir::SourceScope,
}

impl At {
    const fn new(
        bb: BasicBlock,
        unwind: UnwindAction,
        info: mir::SourceInfo,
    ) -> Self {
        Self {
            bb,
            unwind,
            span: info.span,
            scope: info.scope,
        }
    }
}

/// Entries collected from one body before reachability guards are attached.
#[derive(Default)]
struct Raw<'tcx> {
    sites: Vec<PanicSite>,
    site_blocks: Vec<BasicBlock>,
    /// Whether each site raises whenever its block runs, rather than only
    /// when a check in the block fails.
    site_fires: Vec<bool>,
    calls: Vec<CallSite>,
    call_blocks: Vec<BasicBlock>,
    unwind_edges: Vec<(UnwindOrigin, BasicBlock)>,
    successors: Vec<Work<'tcx>>,
    /// Which blocks can unwind out of the body, by block index.
    resuming: Vec<bool>,
}

impl Raw<'_> {
    /// Appends a panic site and the cleanup path unwinding out of it
    /// reaches.
    ///
    /// The origin names the entry by its position, so the index has to be
    /// read before the push, and every caller has to go through here for
    /// the two vectors to stay in step.
    fn add_site(&mut self, at: At, mut site: PanicSite, fires: bool) {
        let index = u32::try_from(self.sites.len()).unwrap_or(u32::MAX);
        site.terminates = !self.leaves(at.unwind);
        self.sites.push(site);
        self.site_blocks.push(at.bb);
        self.site_fires.push(fires);
        self.record_unwind(UnwindOrigin::Site(index), at.unwind);
    }

    /// Appends a call edge and the cleanup path unwinding out of it reaches.
    fn add_call(&mut self, at: At, mut call: CallSite) {
        let index = u32::try_from(self.calls.len()).unwrap_or(u32::MAX);
        call.terminates = !self.leaves(at.unwind);
        self.calls.push(call);
        self.call_blocks.push(at.bb);
        self.record_unwind(UnwindOrigin::Call(index), at.unwind);
    }

    /// Whether unwinding out of a terminator can leave the function.
    ///
    /// The compiler aborts instead in a function that must not unwind, in a
    /// cleanup block, and on a cleanup path that never resumes.
    fn leaves(&self, unwind: UnwindAction) -> bool {
        match unwind {
            UnwindAction::Continue => true,
            UnwindAction::Cleanup(target) => self
                .resuming
                .get(target.as_usize())
                .copied()
                .unwrap_or(true),
            UnwindAction::Unreachable | UnwindAction::Terminate(_) => false,
        }
    }

    /// Notes that unwinding from `origin` transfers control to a cleanup
    /// block.
    fn record_unwind(&mut self, origin: UnwindOrigin, unwind: UnwindAction) {
        if let UnwindAction::Cleanup(target) = unwind {
            self.unwind_edges.push((origin, target));
        }
    }
}

/// Collects panic facts for every function reachable from a crate's roots.
pub struct Extractor<'tcx> {
    tcx: TyCtxt<'tcx>,
    sinks: SinkTable,
    /// What folding each callee against each set of claims found, shared
    /// by every body so a chain of calls is read once rather than at every
    /// site that reaches it.
    cache: Cache<'tcx>,
    /// The name of the library the package under analysis builds, which
    /// is what a test crate's instantiations of its generic functions are
    /// recognised by.
    package_lib: Option<String>,
    /// Whether the crate being compiled is an integration test or a bench,
    /// which links the library rather than being it.
    integration: bool,
    /// Whether panics unwind in this build. Under `panic = "abort"` no
    /// cleanup runs and no catch contains anything.
    unwinds: bool,
    bodies: Vec<Body>,
    seen: Set<String>,
    reified: Vec<Reified>,
    reified_seen: Set<(FuncKey, String)>,
    /// The types reachable code makes into trait objects.
    coerced: Set<String>,
}

/// What the extractor found in one crate.
pub struct Extraction {
    /// Every function body observed.
    pub bodies: Vec<Body>,
    /// Every function observed being reified to a pointer.
    pub reified: Vec<Reified>,
    /// Every type observed being made into a trait object.
    pub coerced: Vec<String>,
}

impl<'tcx> Extractor<'tcx> {
    /// Prepares an extractor for one compilation.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            sinks: SinkTable::default(),
            cache: Cache::default(),
            package_lib: std::env::var("CARGO_PKG_NAME")
                .ok()
                .map(|name| name.replace('-', "_")),
            // Cargo sets this for integration tests and benches alone.
            integration: std::env::var_os("CARGO_TARGET_TMPDIR").is_some(),
            unwinds: tcx.sess.panic_strategy().unwinds(),
            bodies: Vec::new(),
            seen: Set::default(),
            reified: Vec::new(),
            reified_seen: Set::default(),
            coerced: Set::default(),
        }
    }

    /// Walks the whole reachable call graph and returns what it found.
    pub fn run(mut self) -> Extraction {
        let mut queue: Vec<Work<'tcx>> = self.roots();
        // Every instance is recorded in `seen` before its callees are
        // queued, so each function is expanded at most once and the walk
        // terminates once the reachable set is exhausted.
        while let Some(work) = queue.pop() {
            let Some(key) = self.symbol_of(work.inst) else {
                continue;
            };
            if !self.seen.insert(key.clone()) {
                continue;
            }
            queue.extend(self.build(work, FuncKey(key)));
        }
        let mut coerced: Vec<String> = self.coerced.into_iter().collect();
        // Sorted so two runs describe one build the same way.
        coerced.sort();
        Extraction {
            bodies: self.bodies,
            reified: self.reified,
            coerced,
        }
    }

    /// Every function defined in the crate under compilation.
    fn roots(&self) -> Vec<Work<'tcx>> {
        let mut out = Vec::new();
        for local in self.tcx.mir_keys(()) {
            let did = local.to_def_id();
            if !self.tcx.is_mir_available(did) {
                continue;
            }
            if !matches!(
                self.tcx.def_kind(did),
                rustc_hir::def::DefKind::Fn
                    | rustc_hir::def::DefKind::AssocFn
                    | rustc_hir::def::DefKind::Closure
            ) {
                continue;
            }
            // Generic items are analysed as written. Their callees often
            // cannot be resolved without concrete arguments, which is
            // recorded honestly as an unresolved edge rather than silently
            // dropping the function from the report.
            let args = ty::GenericArgs::identity_for_item(self.tcx, did);
            out.push(Work {
                inst: Instance::new_raw(did, args),
                env: TypingEnv::post_analysis(self.tcx, did),
            });
        }
        out
    }

    /// Records one function and returns the callees worth expanding.
    fn build(&mut self, work: Work<'tcx>, key: FuncKey) -> Vec<Work<'tcx>> {
        let inst = work.inst;
        let did = inst.def_id();
        let display = self.display_of(did);
        let krate = self.tcx.crate_name(did.krate).to_string();
        if !Self::has_mir_body(self.tcx, inst) {
            let mut body = Body::opaque(key, display, krate);
            // Foreign code has no Rust body to read and never will, so it is
            // reported apart from a Rust function a fuller standard library
            // would have shown.
            body.foreign = self.tcx.is_foreign_item(did);
            // A body the compiler could not produce is still recorded
            // against the crate that declares it, so the two facts have to
            // agree: a foreign item declared here reports the local crate
            // name, and saying it is not local contradicts that.
            body.local = self.reported(inst);
            body.from_tests = self.tcx.sess.opts.test;
            // A function the compiler guarantees does not unwind raises no
            // panic even though its body is unavailable. Allocator shims are
            // the common case.
            body.opaque = !self.never_unwinds(did);
            self.bodies.push(body);
            return Vec::new();
        }

        let mir = self.tcx.instance_mir(inst.def);
        let raw = self.scan(work, mir);
        let origins = Self::propagate_origins(mir, &raw.unwind_edges);

        let mut sites = raw.sites;
        for (site, bb) in sites.iter_mut().zip(&raw.site_blocks) {
            site.guard = Self::guard_for(mir, &origins, *bb);
        }
        let mut calls = raw.calls;
        for (call, bb) in calls.iter_mut().zip(&raw.call_blocks) {
            call.guard = Self::guard_for(mir, &origins, *bb);
        }

        self.bodies.push(Body {
            key,
            display,
            krate,
            loc: self.loc_of(self.tcx.def_span(did)),
            sites,
            calls,
            opaque: false,
            foreign: false,
            local: self.reported(inst),
            from_tests: self.tcx.sess.opts.test,
        });
        raw.successors
    }

    /// Whether a function is reported as the crate under analysis's own.
    ///
    /// In a test crate the functions defined locally are the tests and the
    /// crate's own code compiled again for them, and neither is what was
    /// asked about: the second is already reported from the build that is.
    /// What such a crate adds is the instantiations it makes of the
    /// library's generic functions, which the library's own build could
    /// only read as written. Those belong to the library, whether it is
    /// compiled again for its unit tests or linked by an integration test,
    /// and are reported as its own. A closure is judged by the function it
    /// is written in, so one inside a test stays out. An integration test
    /// may be named after the package it tests, so there the library is
    /// only ever the crate linked in, never the test crate itself. A generic
    /// body as written is the library build's to report.
    fn reported(&self, inst: Instance<'tcx>) -> bool {
        let did = inst.def_id();
        if !self.tcx.sess.opts.test {
            return did.is_local();
        }
        if (self.integration && did.is_local()) || inst.args.has_param() {
            return false;
        }
        let root = self.tcx.typeck_root_def_id(did);
        self.of_package(did)
            && self
                .tcx
                .generics_of(root)
                .requires_monomorphization(self.tcx)
    }

    /// Whether a function belongs to the library the package builds.
    fn of_package(&self, did: DefId) -> bool {
        self.package_lib.as_deref()
            == Some(self.tcx.crate_name(did.krate).as_str())
    }

    /// The path a function reports under.
    ///
    /// A function of the library reached from one of its test crates is
    /// named the way the library's own build names it, without the crate
    /// in front of its paths, so the two reports of one function fall
    /// under one name.
    fn display_of(&self, did: DefId) -> String {
        let path = self.tcx.def_path_str(did);
        if did.is_local() || !self.of_package(did) {
            return path;
        }
        match &self.package_lib {
            Some(lib) => path.replace(&format!("{lib}::"), ""),
            None => path,
        }
    }

    /// The environment types in this body must be normalized against.
    ///
    /// A body still carrying generic parameters has to be read in the
    /// environment those parameters were declared in, which is the caller's,
    /// not the callee's: a trait method resolved from a generic caller knows
    /// only its own `Self`, so normalizing the caller's parameters there asks
    /// the compiler about parameters it has never heard of.
    fn env_for(work: Work<'tcx>) -> TypingEnv<'tcx> {
        if work.inst.args.has_param() {
            work.env
        } else {
            TypingEnv::fully_monomorphized()
        }
    }

    /// Reads every terminator of a body into raw entries.
    fn scan(&mut self, work: Work<'tcx>, mir: &mir::Body<'tcx>) -> Raw<'tcx> {
        let cx = Work {
            inst: work.inst,
            env: Self::env_for(work),
        };
        let reach =
            fold::reachable(self.tcx, cx.inst, cx.env, mir, &mut self.cache);
        let mut raw = Raw {
            resuming: resuming(mir),
            ..Raw::default()
        };
        for (bb, data) in mir.basic_blocks.iter_enumerated() {
            if !reach.is_live(bb) {
                continue;
            }
            for stmt in &data.statements {
                self.note_reified(&mut raw, cx, stmt, mir);
                self.note_coerced(cx, stmt, mir);
            }
            let Some(term) = &data.terminator else {
                continue;
            };
            let info = term.source_info;
            match &term.kind {
                TerminatorKind::Assert { msg, unwind, .. } => {
                    if reach.is_settled(bb) {
                        // The condition holds for these generic arguments,
                        // so the compiler emits no check at all.
                        continue;
                    }
                    let at = At::new(bb, self.unwind_of(*unwind), info);
                    self.push_assert(&mut raw, at, msg, reach.is_failing(bb));
                }
                TerminatorKind::Call {
                    func,
                    args,
                    unwind,
                    fn_span,
                    ..
                } => {
                    if reach.is_quiet(bb) {
                        // The callee was walked with the arguments this
                        // call makes and found unable to raise. It runs no
                        // other body under them either, so nothing below it
                        // is reachable through this edge.
                        continue;
                    }
                    let mut info = info;
                    info.span = *fn_span;
                    let at = At::new(bb, self.unwind_of(*unwind), info);
                    let ty = func.ty(&mir.local_decls, self.tcx);
                    self.push_call(&mut raw, cx, at, ty, args, mir);
                }
                TerminatorKind::Drop { place, unwind, .. } => {
                    let at = At::new(bb, self.unwind_of(*unwind), info);
                    let ty = place.ty(&mir.local_decls, self.tcx).ty;
                    self.push_drop(&mut raw, cx, at, ty);
                }
                _ => {}
            }
        }
        Self::settle_certain(&mut raw, mir, &reach);
        raw
    }

    /// Where unwinding out of a terminator goes in this build.
    ///
    /// A standard library body is built to unwind even when this build
    /// aborts, and then its cleanup never runs.
    const fn unwind_of(&self, unwind: UnwindAction) -> UnwindAction {
        if self.unwinds {
            unwind
        } else {
            UnwindAction::Unreachable
        }
    }

    /// Marks the sites every execution of the body raises at.
    ///
    /// A site is certain when it raises whenever its block runs and no
    /// execution gets round the block: no path from the entry reaches a
    /// way out of the body without passing through it, and no path can go
    /// round in a loop instead, which is as far as a walk that does not
    /// prove loops terminate can go.
    fn settle_certain(
        raw: &mut Raw<'tcx>,
        mir: &mir::Body<'tcx>,
        reach: &fold::Reach,
    ) {
        let mut raises = vec![false; mir.basic_blocks.len()];
        for bb in &raw.site_blocks {
            if let Some(slot) = raises.get_mut(bb.as_usize()) {
                *slot = true;
            }
        }
        for (index, site) in raw.sites.iter_mut().enumerate() {
            let fires = raw.site_fires.get(index).copied().unwrap_or(false);
            let Some(&bb) = raw.site_blocks.get(index) else {
                continue;
            };
            // A cleanup block runs only while another panic unwinds, so a
            // site in one is never the whole story of a call.
            site.certain = fires
                && !mir.basic_blocks[bb].is_cleanup
                && unavoidable(mir, reach, bb, &raises);
        }
    }

    /// Records a compiler inserted check as a panic site.
    fn push_assert<O>(
        &self,
        raw: &mut Raw<'tcx>,
        at: At,
        msg: &AssertKind<O>,
        fails: bool,
    ) {
        if !self.tcx.sess.overflow_checks() && msg.is_optional_overflow_check()
        {
            // Codegen drops these outright in a build without overflow
            // checks: the arithmetic wraps instead. They survive in the MIR
            // only because a function marked to inherit the setting is built
            // once and used by crates that disagree about it.
            return;
        }
        let (category, termination, reason) = classify_assert(msg);
        let site = PanicSite {
            category,
            termination,
            reason: reason.to_owned(),
            sink: None,
            loc: self.loc_of(at.span),
            guard: Guard::default(),
            certain: false,
            terminates: false,
        };
        raw.add_site(at, site, fails);
    }

    /// Records a call, either as a panic site or as a graph edge.
    fn push_call(
        &mut self,
        raw: &mut Raw<'tcx>,
        cx: Work<'tcx>,
        at: At,
        ty: ty::Ty<'tcx>,
        operands: &[Spanned<mir::Operand<'tcx>>],
        mir: &mir::Body<'tcx>,
    ) {
        let Some(ty) = self.normalize(cx, ty) else {
            self.unresolved(raw, at, "<unresolved>".to_owned());
            return;
        };
        let ty::FnDef(did, args) = *ty.kind() else {
            // A call through a function pointer. The target set is unknown,
            // but the signature narrows which reified functions could be
            // behind it.
            let site = CallSite {
                callee: None,
                callee_display: "<fn pointer>".to_owned(),
                kind: EdgeKind::FnPtr,
                loc: self.loc_of(at.span),
                guard: Guard::default(),
                barrier: false,
                terminates: false,
                candidate: false,
                sig: Some(format!("{ty}")),
                self_ty: None,
            };
            raw.add_call(at, site);
            return;
        };
        let Some(args) = args.no_bound_vars() else {
            self.generic(raw, at, self.tcx.def_path_str(did));
            return;
        };
        let callee = match Instance::try_resolve(self.tcx, cx.env, did, args) {
            // Not enough is known yet: the target exists only once a caller
            // supplies concrete arguments, which is that caller's choice.
            Ok(None) => {
                self.generic(raw, at, self.tcx.def_path_str(did));
                return;
            }
            Err(_) => {
                self.unresolved(raw, at, self.tcx.def_path_str(did));
                return;
            }
            Ok(Some(callee)) => callee,
        };

        if let Some(sink) = self.sinks.get(self.tcx, callee.def_id()) {
            let sink = SinkTable::refine_unwrap(self.tcx, cx.inst.args, sink);
            self.push_sink(raw, cx, at, callee, operands, sink);
            return;
        }

        if matches!(
            callee.def,
            ty::InstanceKind::Intrinsic(..)
                | ty::InstanceKind::LlvmIntrinsic(..)
        ) {
            self.push_intrinsic(raw, cx, at, callee, operands, mir);
            return;
        }
        let kind = match callee.def {
            ty::InstanceKind::Virtual(..) => EdgeKind::Vtable,
            _ => EdgeKind::Static,
        };
        let display = self.tcx.def_path_str(callee.def_id());
        let key = self.symbol_of(callee).map(FuncKey);
        self.push_edge(raw, at, key, display, kind, false);
        if kind == EdgeKind::Static {
            raw.successors.push(Work {
                inst: callee,
                env: cx.env,
            });
        } else {
            self.push_dyn_candidates(raw, cx, at, callee);
        }
    }

    /// Resolves a type written in a body against the arguments it was
    /// reached with.
    fn normalize(
        &self,
        cx: Work<'tcx>,
        ty: ty::Ty<'tcx>,
    ) -> Option<ty::Ty<'tcx>> {
        instantiate(self.tcx, cx.inst, cx.env, ty)
    }

    /// Appends an edge to a target the analysis could not pin down.
    fn unresolved(&self, raw: &mut Raw<'tcx>, at: At, display: String) {
        self.push_edge(raw, at, None, display, EdgeKind::Unresolved, false);
    }

    /// Appends an edge that resolves only once a caller chooses arguments.
    fn generic(&self, raw: &mut Raw<'tcx>, at: At, display: String) {
        self.push_edge(raw, at, None, display, EdgeKind::Generic, false);
    }

    /// Appends a call edge and its unwind channel.
    fn push_edge(
        &self,
        raw: &mut Raw<'tcx>,
        at: At,
        callee: Option<FuncKey>,
        callee_display: String,
        kind: EdgeKind,
        barrier: bool,
    ) {
        let site = CallSite {
            callee,
            callee_display,
            kind,
            loc: self.loc_of(at.span),
            guard: Guard::default(),
            barrier,
            terminates: false,
            candidate: false,
            sig: None,
            self_ty: None,
        };
        raw.add_call(at, site);
    }

    /// Marks every cleanup block reachable from each unwind edge.
    fn propagate_origins(
        mir: &mir::Body<'_>,
        edges: &[(UnwindOrigin, BasicBlock)],
    ) -> Map<BasicBlock, Vec<UnwindOrigin>> {
        let mut out: Map<BasicBlock, Vec<UnwindOrigin>> = Map::default();
        // Every edge walks the same body, so the two scratch buffers are
        // reused rather than rebuilt once per edge.
        let mut seen: Set<BasicBlock> = Set::default();
        let mut stack: Vec<BasicBlock> = Vec::new();
        for (origin, start) in edges {
            seen.clear();
            stack.clear();
            stack.push(*start);
            // `seen` admits each block once, so the walk is bounded by the
            // number of basic blocks in the body.
            while let Some(bb) = stack.pop() {
                if !seen.insert(bb) {
                    continue;
                }
                let list = out.entry(bb).or_default();
                if !list.contains(origin) {
                    list.push(*origin);
                }
                let Some(term) = &mir.basic_blocks[bb].terminator else {
                    continue;
                };
                stack.extend(term.successors());
            }
        }
        out
    }

    /// Builds the reachability guard for one basic block.
    fn guard_for(
        mir: &mir::Body<'_>,
        origins: &Map<BasicBlock, Vec<UnwindOrigin>>,
        bb: BasicBlock,
    ) -> Guard {
        Guard {
            normal: !mir.basic_blocks[bb].is_cleanup,
            origins: origins.get(&bb).cloned().unwrap_or_default(),
        }
    }

    /// Whether the compiler guarantees a function cannot unwind.
    fn never_unwinds(&self, did: rustc_hir::def_id::DefId) -> bool {
        self.tcx
            .codegen_fn_attrs(did)
            .flags
            .contains(CodegenFnAttrFlags::NEVER_UNWIND)
    }

    /// Whether the compiler can produce a body for this instance.
    fn has_mir_body(tcx: TyCtxt<'tcx>, inst: Instance<'tcx>) -> bool {
        match inst.def {
            ty::InstanceKind::Item(def) => tcx.is_mir_available(def),
            ty::InstanceKind::Intrinsic(..)
            | ty::InstanceKind::LlvmIntrinsic(..)
            | ty::InstanceKind::Virtual(..) => false,
            ty::InstanceKind::Shim(_) => true,
        }
    }

    /// The globally unique key for an instance.
    fn symbol_of(&self, inst: Instance<'tcx>) -> Option<String> {
        if matches!(inst.def, ty::InstanceKind::Virtual(..)) {
            return None;
        }
        if inst.args.has_param() {
            // A symbol name only exists once the generic arguments are
            // concrete, so a generic body is keyed by its crate, its
            // disambiguated path, and its arguments instead. Two crates may
            // each define `parse<T>`, and `f::<U>` and `f::<Wrapper<T>>`
            // resolve their calls differently.
            let did = inst.def_id();
            let rendered = with_no_trimmed_paths!(inst.to_string());
            return Some(format!(
                "{OPEN_PREFIX}{}[{:016x}]{} {rendered}",
                self.tcx.crate_name(did.krate),
                self.tcx.stable_crate_id(did.krate).as_u64(),
                self.tcx.def_path(did).to_string_no_crate_verbose(),
            ));
        }
        Some(self.tcx.symbol_name(inst).name.to_owned())
    }

    /// Converts a span into a source location.
    fn loc_of(&self, span: rustc_span::Span) -> Option<Loc> {
        if span.is_dummy() {
            return None;
        }
        let map = self.tcx.sess.source_map();
        let pos = map.lookup_char_pos(span.lo());
        Some(Loc {
            file: map.filename_for_diagnostics(&pos.file.name).to_string(),
            line: u32::try_from(pos.line).unwrap_or(0),
            col: pos.col.0.saturating_add(1).try_into().unwrap_or(0),
        })
    }
}
