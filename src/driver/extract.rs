//! Walks MIR and records what each function can panic with, and who it calls.

use panicgraph::{
    Body, CallSite, Category, EdgeKind, FuncKey, Guard, Loc, PanicSite,
    Reified, Termination, UnwindOrigin,
    util::{Map, Set},
};
use rustc_middle::{
    middle::codegen_fn_attrs::CodegenFnAttrFlags,
    mir::{
        self, AssertKind, BasicBlock, TerminatorKind, UnwindAction, interpret,
    },
    ty::{self, Instance, TyCtxt, TypeVisitableExt, TypingEnv},
};
use rustc_span::Spanned;

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
    reified: Vec<Reified>,
    reified_seen: Set<(FuncKey, String)>,
}

/// What the extractor found in one crate.
pub struct Extraction {
    /// Every function body observed.
    pub bodies: Vec<Body>,
    /// Every function observed being reified to a pointer.
    pub reified: Vec<Reified>,
}

impl<'tcx> Extractor<'tcx> {
    /// Prepares an extractor for one compilation.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            sinks: SinkTable::new(),
            bodies: Vec::new(),
            seen: Set::default(),
            reified: Vec::new(),
            reified_seen: Set::default(),
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
        Extraction {
            bodies: self.bodies,
            reified: self.reified,
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
            if !reach.is_live(bb) {
                continue;
            }
            for stmt in &data.statements {
                self.note_reified(&mut raw, cx, stmt);
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
                    let at = At::new(bb, *unwind, info);
                    self.push_assert(&mut raw, at, msg);
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
                    let at = At::new(bb, *unwind, info);
                    let ty = func.ty(&mir.local_decls, self.tcx);
                    self.push_call(&mut raw, cx, at, ty, args, mir);
                }
                TerminatorKind::Drop { place, unwind, .. } => {
                    let at = At::new(bb, *unwind, info);
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
            let index = u32::try_from(raw.calls.len()).unwrap_or(u32::MAX);
            raw.calls.push(CallSite {
                callee: None,
                callee_display: "<fn pointer>".to_owned(),
                kind: EdgeKind::FnPtr,
                loc: self.loc_of(at.span),
                guard: Guard::default(),
                barrier: false,
                candidate: false,
                sig: Some(format!("{ty}")),
            });
            raw.call_blocks.push(at.bb);
            Self::record_unwind(raw, UnwindOrigin::Call(index), at.unwind);
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
            if self.tcx.item_name(callee.def_id()).as_str() == "catch_unwind" {
                self.push_catch(raw, cx, at, operands, mir);
                return;
            }
            if let Some(requirement) =
                ty::layout::ValidityRequirement::from_intrinsic(
                    self.tcx.item_name(callee.def_id()),
                )
            {
                self.push_validity(raw, cx, at, callee, requirement);
                return;
            }
            if self.refcount_abort(cx, at, callee.def_id(), mir) {
                let index = u32::try_from(raw.sites.len()).unwrap_or(u32::MAX);
                raw.sites.push(PanicSite {
                    category: Category::RefCountOverflow,
                    termination: Termination::Abort,
                    reason: "the reference count would overflow".to_owned(),
                    sink: Some("core::intrinsics::abort".to_owned()),
                    loc: self.loc_of(at.span),
                    guard: Guard::default(),
                });
                raw.site_blocks.push(at.bb);
                Self::record_unwind(raw, UnwindOrigin::Site(index), at.unwind);
            }
            // Other intrinsics are compiler defined operations. They cannot
            // call back into the program, so they add nothing to the graph,
            // and recording them as bodies without MIR would report every
            // use of a hint like `cold_path` as an unknown panic.
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
            self.generic(raw, at, format!("drop glue for {ty}"));
            return;
        }
        let glue = Instance::resolve_drop_glue(self.tcx, ty);
        let display = format!("drop glue for {ty}");
        let key = self.symbol_of(glue).map(FuncKey);
        self.push_edge(raw, at, key, display, EdgeKind::Drop, false);
        raw.successors.push(Work {
            inst: glue,
            env: cx.env,
        });
    }

    /// Records the edges of the unwind catching intrinsic.
    ///
    /// The intrinsic runs its first operand and, when that unwinds, its
    /// third. An unwinding panic in the first stops here, which is the whole
    /// point of the catch; an aborting one cannot be caught by anything. The
    /// edge is therefore a barrier rather than a severed subtree, so the
    /// aborts keep flowing to the caller.
    fn push_catch(
        &self,
        raw: &mut Raw<'tcx>,
        cx: Work<'tcx>,
        at: At,
        operands: &[Spanned<mir::Operand<'tcx>>],
        mir: &mir::Body<'tcx>,
    ) {
        for (index, barrier) in [(0usize, true), (2usize, false)] {
            let resolved = operands
                .get(index)
                .and_then(|arg| self.fn_operand(cx, &arg.node, mir));
            match resolved {
                Some(inst) => {
                    let display = self.tcx.def_path_str(inst.def_id());
                    let key = self.symbol_of(inst).map(FuncKey);
                    self.push_edge(
                        raw,
                        at,
                        key,
                        display,
                        EdgeKind::Static,
                        barrier,
                    );
                    raw.successors.push(Work { inst, env: cx.env });
                }
                None => self.push_edge(
                    raw,
                    at,
                    None,
                    "<caught function>".to_owned(),
                    EdgeKind::Unresolved,
                    barrier,
                ),
            }
        }
    }

    /// Records the panics a call into an entry point raises.
    fn push_sink(
        &self,
        raw: &mut Raw<'tcx>,
        cx: Work<'tcx>,
        at: At,
        callee: Instance<'tcx>,
        operands: &[Spanned<mir::Operand<'tcx>>],
        sink: crate::sinks::Sink,
    ) {
        let path = self.tcx.def_path_str(callee.def_id());
        let reason = self.panic_message(cx, operands).map_or_else(
            || format!("calls {path}"),
            |msg| format!("panics with \"{msg}\""),
        );
        for (category, termination) in sink.raises() {
            let index = u32::try_from(raw.sites.len()).unwrap_or(u32::MAX);
            raw.sites.push(PanicSite {
                category,
                termination,
                reason: reason.clone(),
                sink: Some(path.clone()),
                loc: self.loc_of(at.span),
                guard: Guard::default(),
            });
            raw.site_blocks.push(at.bb);
            Self::record_unwind(raw, UnwindOrigin::Site(index), at.unwind);
        }
    }

    /// The static message a panic entry point is handed, when it has one.
    ///
    /// Formatted panics carry their template inside an arguments value and
    /// are left alone; a plain string argument is the message itself, which
    /// is what a bare panic, an unwrap, and an expect pass down.
    fn panic_message(
        &self,
        cx: Work<'tcx>,
        operands: &[Spanned<mir::Operand<'tcx>>],
    ) -> Option<String> {
        let mir::Operand::Constant(konst) = &operands.first()?.node else {
            return None;
        };
        let konst = cx
            .inst
            .try_instantiate_mir_and_normalize_erasing_regions(
                self.tcx,
                cx.env,
                ty::EarlyBinder::bind(self.tcx, konst.const_),
            )
            .ok()?;
        let ty::Ref(_, inner, _) = konst.ty().kind() else {
            return None;
        };
        if !matches!(inner.kind(), ty::Str) {
            return None;
        }
        let value = konst.eval(self.tcx, cx.env, rustc_span::DUMMY_SP).ok()?;
        let bytes = value.try_get_slice_bytes_for_diagnostics(self.tcx)?;
        let text = std::str::from_utf8(bytes).ok()?;
        let mut out: String = text.chars().take(72).collect();
        if out.len() < text.len() {
            out.push_str("...");
        }
        Some(out)
    }

    /// Resolves an operand holding a function to the instance it names.
    ///
    /// The reified pointer handed to the catch intrinsic is either a
    /// constant already or a local a single cast wrote, and both name the
    /// function outright. Anything else is given up on rather than guessed.
    fn fn_operand(
        &self,
        cx: Work<'tcx>,
        operand: &mir::Operand<'tcx>,
        mir: &mir::Body<'tcx>,
    ) -> Option<Instance<'tcx>> {
        if let mir::Operand::Constant(konst) = operand {
            return self.fn_constant(cx, konst);
        }
        let (mir::Operand::Copy(place) | mir::Operand::Move(place)) = operand
        else {
            return None;
        };
        let local = place.as_local()?;
        let mut written: Option<&mir::Rvalue<'tcx>> = None;
        for block in mir.basic_blocks.iter() {
            for stmt in &block.statements {
                let mir::StatementKind::Assign(pair) = &stmt.kind else {
                    continue;
                };
                if pair.0.local != local {
                    continue;
                }
                if written.is_some() {
                    // Written twice, so which function the pointer names
                    // depends on the path taken.
                    return None;
                }
                written = Some(&pair.1);
            }
        }
        match written? {
            mir::Rvalue::Cast(
                mir::CastKind::PointerCoercion(
                    ty::adjustment::PointerCoercion::ReifyFnPointer(_),
                    _,
                ),
                mir::Operand::Constant(konst),
                _,
            )
            | mir::Rvalue::Use(mir::Operand::Constant(konst), _) => {
                self.fn_constant(cx, konst)
            }
            _ => None,
        }
    }

    /// Resolves a constant naming a function, written either as the zero
    /// sized function item or as an already reified pointer.
    fn fn_constant(
        &self,
        cx: Work<'tcx>,
        konst: &mir::ConstOperand<'tcx>,
    ) -> Option<Instance<'tcx>> {
        let konst = cx
            .inst
            .try_instantiate_mir_and_normalize_erasing_regions(
                self.tcx,
                cx.env,
                ty::EarlyBinder::bind(self.tcx, konst.const_),
            )
            .ok()?;
        if let ty::FnDef(did, args) = *konst.ty().kind() {
            let args = args.no_bound_vars()?;
            return Instance::try_resolve(self.tcx, cx.env, did, args)
                .ok()
                .flatten();
        }
        let scalar = konst.try_eval_scalar(self.tcx, cx.env)?;
        let interpret::Scalar::Ptr(ptr, _) = scalar else {
            return None;
        };
        let alloc = self.tcx.global_alloc(ptr.provenance.alloc_id());
        match alloc {
            interpret::GlobalAlloc::Function { instance } => Some(instance),
            _ => None,
        }
    }

    /// Records the check inside an instantiation the type system cannot
    /// see.
    ///
    /// `mem::zeroed`, `mem::uninitialized`, and `assume_init` guard their
    /// instantiation with an intrinsic that aborts when the type forbids
    /// the value, in every build. The guard is resolved here the way
    /// codegen resolves it: a type that satisfies the requirement raises
    /// nothing, and one that cannot aborts every time it is reached.
    fn push_validity(
        &self,
        raw: &mut Raw<'tcx>,
        cx: Work<'tcx>,
        at: At,
        callee: Instance<'tcx>,
        requirement: ty::layout::ValidityRequirement,
    ) {
        // The argument is read off the resolved instance, so it is already
        // in its final form; running it through the enclosing frame again
        // would instantiate a type that belongs to whichever caller the
        // chain started from, whose parameters this frame does not have.
        let Some(ty) = callee.args.first().and_then(|arg| arg.as_type()) else {
            self.unresolved(raw, at, "<validity of an unknown type>".into());
            return;
        };
        if ty.has_param() {
            self.generic(raw, at, format!("validity of {ty}"));
            return;
        }
        match self.tcx.check_validity_requirement((
            requirement,
            cx.env.as_query_input(ty),
        )) {
            // The type allows the value, so the compiler emits no check.
            Ok(true) => {}
            Ok(false) => {
                let index = u32::try_from(raw.sites.len()).unwrap_or(u32::MAX);
                raw.sites.push(PanicSite {
                    category: Category::Explicit,
                    termination: Termination::Abort,
                    reason: format!(
                        "instantiating {ty} this way is invalid, so the \
                         check aborts"
                    ),
                    sink: None,
                    loc: self.loc_of(at.span),
                    guard: Guard::default(),
                });
                raw.site_blocks.push(at.bb);
                Self::record_unwind(raw, UnwindOrigin::Site(index), at.unwind);
            }
            // The layout could not be computed, so neither answer is safe
            // to claim.
            Err(_) => {
                self.unresolved(raw, at, format!("validity of {ty}"));
            }
        }
    }

    /// Whether a call to the abort intrinsic reports a reference count
    /// overflow.
    ///
    /// `Rc` and `Arc` abort when a count would wrap, and the abort intrinsic
    /// is the whole report: there is no entry point to name. The rule is
    /// scoped to the reference counting modules so that `process::abort`, a
    /// deliberate termination rather than a panic, stays unreported. The
    /// machinery is usually inlined into its caller, so the enclosing
    /// instance is not enough: the scope chain keeps the compiler's own
    /// record of where each inlined call was written.
    fn refcount_abort(
        &self,
        cx: Work<'tcx>,
        at: At,
        callee: rustc_hir::def_id::DefId,
        mir: &mir::Body<'tcx>,
    ) -> bool {
        if self.tcx.item_name(callee).as_str() != "abort" {
            return false;
        }
        if self.in_refcounting(cx.inst.def_id()) {
            return true;
        }
        let mut scope = at.scope;
        // Parent links form a tree toward the root scope, so the walk takes
        // at most one step per scope in the body.
        for _ in 0..=mir.source_scopes.len() {
            let data = &mir.source_scopes[scope];
            if let Some((inst, _)) = data.inlined
                && self.in_refcounting(inst.def_id())
            {
                return true;
            }
            let Some(parent) = data.parent_scope else {
                return false;
            };
            scope = parent;
        }
        false
    }

    /// Whether a function belongs to the reference counting modules.
    fn in_refcounting(&self, did: rustc_hir::def_id::DefId) -> bool {
        if self.tcx.crate_name(did.krate).as_str() != "alloc" {
            return false;
        }
        let path = SinkTable::def_path(self.tcx, did);
        path.starts_with("rc::") || path.starts_with("sync::")
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
        let index = u32::try_from(raw.calls.len()).unwrap_or(u32::MAX);
        raw.calls.push(CallSite {
            callee,
            callee_display,
            kind,
            loc: self.loc_of(at.span),
            guard: Guard::default(),
            barrier,
            candidate: false,
            sig: None,
        });
        raw.call_blocks.push(at.bb);
        Self::record_unwind(raw, UnwindOrigin::Call(index), at.unwind);
    }

    /// Records a function being turned into a pointer, so indirect calls
    /// can name it as a candidate.
    ///
    /// Only reachable code is scanned, so a pointer that no execution can
    /// create never becomes a candidate.
    fn note_reified(
        &mut self,
        raw: &mut Raw<'tcx>,
        cx: Work<'tcx>,
        stmt: &mir::Statement<'tcx>,
    ) {
        let mir::StatementKind::Assign(pair) = &stmt.kind else {
            return;
        };
        let mir::Rvalue::Cast(
            mir::CastKind::PointerCoercion(
                ty::adjustment::PointerCoercion::ReifyFnPointer(_),
                _,
            ),
            mir::Operand::Constant(konst),
            cast_ty,
        ) = &pair.1
        else {
            return;
        };
        let Some(inst) = self.fn_constant(cx, konst) else {
            return;
        };
        let Some(sig) = self.normalize(cx, *cast_ty).map(|ty| ty.to_string())
        else {
            return;
        };
        let Some(key) = self.symbol_of(inst).map(FuncKey) else {
            return;
        };
        if !self.reified_seen.insert((key.clone(), sig.clone())) {
            return;
        }
        // The candidate's own panics have to be in the artifact for the
        // edge to mean anything, so its body is walked as well.
        raw.successors.push(Work { inst, env: cx.env });
        self.reified.push(Reified {
            key,
            display: self.tcx.def_path_str(inst.def_id()),
            sig,
        });
    }

    /// Appends every known implementation a dynamic call could reach.
    ///
    /// Candidates are marked as such and followed only when asked for. The
    /// unresolved edge stays regardless: an implementation in a crate the
    /// analysis never loads, or behind a generic impl, is still possible.
    fn push_dyn_candidates(
        &self,
        raw: &mut Raw<'tcx>,
        cx: Work<'tcx>,
        at: At,
        virt: Instance<'tcx>,
    ) {
        let method = virt.def_id();
        let Some(trait_did) = self.tcx.trait_of_assoc(method) else {
            return;
        };
        if self.tcx.is_fn_trait(trait_did) {
            // Every closure in the graph implements these; the candidate
            // set would be noise rather than narrowing.
            return;
        }
        for impl_did in self.tcx.all_impls(trait_did) {
            // Skipping normalization is fine here: a concrete impl's self
            // type and arguments are used only to ask resolution for the
            // instance, and resolution normalizes what it is given.
            let trait_ref = self
                .tcx
                .impl_trait_ref(impl_did)
                .instantiate_identity()
                .skip_normalization();
            if trait_ref.has_param() {
                // A generic impl has no single instance to name. The
                // unresolved edge already covers it.
                continue;
            }
            let args = self.tcx.mk_args_from_iter(
                std::iter::once(ty::GenericArg::from(trait_ref.self_ty()))
                    .chain(virt.args.iter().skip(1)),
            );
            let Ok(Some(target)) =
                Instance::try_resolve(self.tcx, cx.env, method, args)
            else {
                continue;
            };
            let Some(key) = self.symbol_of(target).map(FuncKey) else {
                continue;
            };
            let index = u32::try_from(raw.calls.len()).unwrap_or(u32::MAX);
            raw.calls.push(CallSite {
                callee: Some(key),
                callee_display: self.tcx.def_path_str(target.def_id()),
                kind: EdgeKind::Vtable,
                loc: self.loc_of(at.span),
                guard: Guard::default(),
                barrier: false,
                candidate: true,
                sig: None,
            });
            raw.call_blocks.push(at.bb);
            Self::record_unwind(raw, UnwindOrigin::Call(index), at.unwind);
            raw.successors.push(Work {
                inst: target,
                env: cx.env,
            });
        }
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
