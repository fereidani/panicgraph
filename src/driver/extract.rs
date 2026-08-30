//! Walks MIR and records what each function can panic with, and who it calls.

use panicgraph::{
    Body, CallSite, Category, EdgeKind, FuncKey, Guard, Loc, PanicSite,
    Termination, UnwindOrigin,
    util::{Map, Set},
};
use rustc_middle::{
    middle::codegen_fn_attrs::CodegenFnAttrFlags,
    mir::{self, AssertKind, BasicBlock, TerminatorKind, UnwindAction},
    ty::{self, Instance, TyCtxt, TypeVisitableExt, TypingEnv},
};

use crate::{fold, sinks::SinkTable};

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
}

impl At {
    const fn new(
        bb: BasicBlock,
        unwind: UnwindAction,
        span: rustc_span::Span,
    ) -> Self {
        Self { bb, unwind, span }
    }
}

/// Entries collected from one body before reachability guards are attached.
struct Raw<'tcx> {
    sites: Vec<PanicSite>,
    site_blocks: Vec<BasicBlock>,
    calls: Vec<CallSite>,
    call_blocks: Vec<BasicBlock>,
    unwind_edges: Vec<(UnwindOrigin, BasicBlock)>,
    successors: Vec<Work<'tcx>>,
}

impl Raw<'_> {
    const fn new() -> Self {
        Self {
            sites: Vec::new(),
            site_blocks: Vec::new(),
            calls: Vec::new(),
            call_blocks: Vec::new(),
            unwind_edges: Vec::new(),
            successors: Vec::new(),
        }
    }
}

/// Collects panic facts for every function reachable from a crate's roots.
pub struct Extractor<'tcx> {
    tcx: TyCtxt<'tcx>,
    sinks: SinkTable,
    bodies: Vec<Body>,
    seen: Set<String>,
}

impl<'tcx> Extractor<'tcx> {
    /// Prepares an extractor for one compilation.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            sinks: SinkTable::new(),
            bodies: Vec::new(),
            seen: Set::default(),
        }
    }

    /// Walks the whole reachable call graph and returns the bodies found.
    pub fn run(mut self) -> Vec<Body> {
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
        self.bodies
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
        if !Self::has_mir_body(self.tcx, inst) {
            let did = inst.def_id();
            let display = self.tcx.def_path_str(did);
            let krate = self.tcx.crate_name(did.krate).to_string();
            let mut body = Body::opaque(key, display, krate);
            // Foreign code has no Rust body to read and never will, so it is
            // reported apart from a Rust function a fuller standard library
            // would have shown.
            body.foreign = self.tcx.is_foreign_item(did);
            // A body the compiler could not produce is still recorded
            // against the crate that declares it, so the two facts have to
            // agree: a foreign item declared here reports the local crate
            // name, and saying it is not local contradicts that.
            body.local = did.is_local();
            if self.never_unwinds(did) {
                // The compiler guarantees this function does not unwind, so
                // it raises no panic even though its body is unavailable.
                // Allocator shims are the common case.
                body.opaque = false;
            }
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

        let did = inst.def_id();
        self.bodies.push(Body {
            key,
            display: self.tcx.def_path_str(did),
            krate: self.tcx.crate_name(did.krate).to_string(),
            loc: self.loc_of(self.tcx.def_span(did)),
            sites,
            calls,
            opaque: false,
            foreign: false,
            local: did.is_local(),
        });
        raw.successors
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
        let reach = fold::reachable(self.tcx, cx.inst, cx.env, mir);
        let mut raw = Raw::new();
        for (bb, data) in mir.basic_blocks.iter_enumerated() {
            let Some(term) = &data.terminator else {
                continue;
            };
            if !reach.is_live(bb) {
                continue;
            }
            let span = term.source_info.span;
            match &term.kind {
                TerminatorKind::Assert { msg, unwind, .. } => {
                    if reach.is_settled(bb) {
                        // The condition holds for these generic arguments,
                        // so the compiler emits no check at all.
                        continue;
                    }
                    let at = At::new(bb, *unwind, span);
                    self.push_assert(&mut raw, at, msg);
                }
                TerminatorKind::Call {
                    func,
                    unwind,
                    fn_span,
                    ..
                } => {
                    let at = At::new(bb, *unwind, *fn_span);
                    let ty = func.ty(&mir.local_decls, self.tcx);
                    self.push_call(&mut raw, cx, at, ty);
                }
                TerminatorKind::Drop { place, unwind, .. } => {
                    let at = At::new(bb, *unwind, span);
                    let ty = place.ty(&mir.local_decls, self.tcx).ty;
                    self.push_drop(&mut raw, cx, at, ty);
                }
                _ => {}
            }
        }
        raw
    }

    /// Records a compiler inserted check as a panic site.
    fn push_assert<O>(&self, raw: &mut Raw<'tcx>, at: At, msg: &AssertKind<O>) {
        if !self.tcx.sess.overflow_checks() && msg.is_optional_overflow_check()
        {
            // Codegen drops these outright in a build without overflow
            // checks: the arithmetic wraps instead. They survive in the MIR
            // only because a function marked to inherit the setting is built
            // once and used by crates that disagree about it.
            return;
        }
        let (category, termination, reason) = classify_assert(msg);
        let index = u32::try_from(raw.sites.len()).unwrap_or(u32::MAX);
        raw.sites.push(PanicSite {
            category,
            termination,
            reason: reason.to_owned(),
            sink: None,
            loc: self.loc_of(at.span),
            guard: Guard::default(),
        });
        raw.site_blocks.push(at.bb);
        Self::record_unwind(raw, UnwindOrigin::Site(index), at.unwind);
    }

    /// Records a call, either as a panic site or as a graph edge.
    fn push_call(
        &mut self,
        raw: &mut Raw<'tcx>,
        cx: Work<'tcx>,
        at: At,
        ty: ty::Ty<'tcx>,
    ) {
        let Some(ty) = self.normalize(cx, ty) else {
            self.unresolved(raw, at, "<unresolved>".to_owned());
            return;
        };
        let ty::FnDef(did, args) = *ty.kind() else {
            // A call through a function pointer. The target set is unknown.
            let name = "<fn pointer>".to_owned();
            self.push_edge(raw, at, None, name, EdgeKind::FnPtr);
            return;
        };
        let Some(args) = args.no_bound_vars() else {
            self.unresolved(raw, at, self.tcx.def_path_str(did));
            return;
        };
        let resolved = Instance::try_resolve(self.tcx, cx.env, did, args);
        let Ok(Some(callee)) = resolved else {
            self.unresolved(raw, at, self.tcx.def_path_str(did));
            return;
        };

        if let Some(sink) = self.sinks.get(self.tcx, callee.def_id()) {
            let path = self.tcx.def_path_str(callee.def_id());
            for (category, termination) in sink.raises() {
                let index = u32::try_from(raw.sites.len()).unwrap_or(u32::MAX);
                raw.sites.push(PanicSite {
                    category,
                    termination,
                    reason: format!("calls {path}"),
                    sink: Some(path.clone()),
                    loc: self.loc_of(at.span),
                    guard: Guard::default(),
                });
                raw.site_blocks.push(at.bb);
                Self::record_unwind(raw, UnwindOrigin::Site(index), at.unwind);
            }
            return;
        }

        if matches!(
            callee.def,
            ty::InstanceKind::Intrinsic(..)
                | ty::InstanceKind::LlvmIntrinsic(..)
        ) {
            // Intrinsics are compiler defined operations. They cannot call
            // back into the program, so they add nothing to the graph, and
            // recording them as bodies without MIR would report every use of
            // a hint like `cold_path` as an unknown panic.
            return;
        }
        let kind = match callee.def {
            ty::InstanceKind::Virtual(..) => EdgeKind::Vtable,
            _ => EdgeKind::Static,
        };
        let display = self.tcx.def_path_str(callee.def_id());
        let key = self.symbol_of(callee).map(FuncKey);
        self.push_edge(raw, at, key, display, kind);
        if kind == EdgeKind::Static {
            raw.successors.push(Work {
                inst: callee,
                env: cx.env,
            });
        }
    }

    /// Records the drop glue reached by a `Drop` terminator.
    fn push_drop(
        &self,
        raw: &mut Raw<'tcx>,
        cx: Work<'tcx>,
        at: At,
        ty: ty::Ty<'tcx>,
    ) {
        let Some(ty) = self.normalize(cx, ty) else {
            self.unresolved(raw, at, "<unresolved drop>".to_owned());
            return;
        };
        if !ty.needs_drop(self.tcx, cx.env) {
            // Nothing runs here. A reference or a struct of raw pointers has
            // no glue whatever its parameters turn out to be, so treating
            // the terminator as an unknown target would invent a panic that
            // no instantiation can reach.
            return;
        }
        if ty.has_param() {
            // Something has to run, but which glue is only known once the
            // dropped type is concrete.
            self.unresolved(raw, at, format!("drop glue for {ty}"));
            return;
        }
        let glue = Instance::resolve_drop_glue(self.tcx, ty);
        let display = format!("drop glue for {ty}");
        let key = self.symbol_of(glue).map(FuncKey);
        self.push_edge(raw, at, key, display, EdgeKind::Drop);
        raw.successors.push(Work {
            inst: glue,
            env: cx.env,
        });
    }

    /// Resolves a type written in a body against the arguments it was
    /// reached with.
    fn normalize(
        &self,
        cx: Work<'tcx>,
        ty: ty::Ty<'tcx>,
    ) -> Option<ty::Ty<'tcx>> {
        cx.inst
            .try_instantiate_mir_and_normalize_erasing_regions(
                self.tcx,
                cx.env,
                ty::EarlyBinder::bind(self.tcx, ty),
            )
            .ok()
    }

    /// Appends an edge to a target the analysis could not pin down.
    fn unresolved(&self, raw: &mut Raw<'tcx>, at: At, display: String) {
        self.push_edge(raw, at, None, display, EdgeKind::Unresolved);
    }

    /// Appends a call edge and its unwind channel.
    fn push_edge(
        &self,
        raw: &mut Raw<'tcx>,
        at: At,
        callee: Option<FuncKey>,
        callee_display: String,
        kind: EdgeKind,
    ) {
        let index = u32::try_from(raw.calls.len()).unwrap_or(u32::MAX);
        raw.calls.push(CallSite {
            callee,
            callee_display,
            kind,
            loc: self.loc_of(at.span),
            guard: Guard::default(),
        });
        raw.call_blocks.push(at.bb);
        Self::record_unwind(raw, UnwindOrigin::Call(index), at.unwind);
    }

    /// Notes that unwinding from `origin` transfers control to a cleanup
    /// block.
    fn record_unwind(
        raw: &mut Raw<'tcx>,
        origin: UnwindOrigin,
        unwind: UnwindAction,
    ) {
        if let UnwindAction::Cleanup(target) = unwind {
            raw.unwind_edges.push((origin, target));
        }
    }

    /// Marks every cleanup block reachable from each unwind edge.
    fn propagate_origins(
        mir: &mir::Body<'_>,
        edges: &[(UnwindOrigin, BasicBlock)],
    ) -> Map<BasicBlock, Vec<UnwindOrigin>> {
        let mut out: Map<BasicBlock, Vec<UnwindOrigin>> = Map::default();
        for (origin, start) in edges {
            let mut seen: Set<BasicBlock> = Set::default();
            let mut stack = vec![*start];
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
            // concrete, so a generic body is keyed by its path instead.
            return Some(format!(
                "generic:{}",
                self.tcx.def_path_str(inst.def_id())
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

/// Maps a compiler inserted check to a reportable category.
const fn classify_assert<O>(
    msg: &AssertKind<O>,
) -> (Category, Termination, &'static str) {
    use Termination::{Abort, Unwind};
    match msg {
        AssertKind::BoundsCheck { .. } => {
            (Category::Index, Unwind, "index out of bounds")
        }
        AssertKind::Overflow(..) => {
            (Category::Overflow, Unwind, "arithmetic overflow")
        }
        AssertKind::OverflowNeg(_) => {
            (Category::Overflow, Unwind, "negation overflow")
        }
        AssertKind::DivisionByZero(_) => {
            (Category::DivideByZero, Unwind, "attempt to divide by zero")
        }
        AssertKind::RemainderByZero(_) => (
            Category::RemainderByZero,
            Unwind,
            "attempt to take remainder by zero",
        ),
        AssertKind::MisalignedPointerDereference { .. } => (
            Category::MisalignedRef,
            Abort,
            "misaligned pointer dereference",
        ),
        AssertKind::NullPointerDereference
        | AssertKind::NullReferenceConstructed => {
            (Category::NullDeref, Abort, "null pointer dereference")
        }
        AssertKind::InvalidEnumConstruction(_) => {
            (Category::Explicit, Abort, "invalid enum construction")
        }
        AssertKind::ResumedAfterReturn(_)
        | AssertKind::ResumedAfterPanic(_)
        | AssertKind::ResumedAfterDrop(_) => (
            Category::Explicit,
            Unwind,
            "coroutine resumed after completion",
        ),
    }
}
