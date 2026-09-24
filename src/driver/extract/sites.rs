//! How a call into a panic entry point, or into an operation the compiler
//! defines, becomes a panic the body raises.

use panicgraph::{Category, EdgeKind, FuncKey, Guard, PanicSite, Termination};
use rustc_middle::{
    mir::{self, AssertKind, interpret},
    ty::{self, Instance, TypeVisitableExt},
};
use rustc_span::Spanned;

use super::{At, Extractor, Raw, Work};
use crate::{
    read::instantiate,
    sinks::{Sink, SinkTable},
};

impl<'tcx> Extractor<'tcx> {
    /// Records what a call to an intrinsic raises.
    pub(super) fn push_intrinsic(
        &self,
        raw: &mut Raw<'tcx>,
        cx: Work<'tcx>,
        at: At,
        callee: Instance<'tcx>,
        operands: &[Spanned<mir::Operand<'tcx>>],
        mir: &mir::Body<'tcx>,
    ) {
        let name = self.tcx.item_name(callee.def_id());
        if name.as_str() == "catch_unwind" {
            self.push_catch(raw, cx, at, operands, mir);
            return;
        }
        if let Some(requirement) =
            ty::layout::ValidityRequirement::from_intrinsic(name)
        {
            self.push_validity(raw, cx, at, callee, requirement);
            return;
        }
        if self.refcount_abort(cx, at, callee.def_id(), mir) {
            let site = PanicSite {
                category: Category::RefCountOverflow,
                termination: Termination::Abort,
                reason: "the reference count would overflow".to_owned(),
                sink: Some("core::intrinsics::abort".to_owned()),
                loc: self.loc_of(at.span),
                guard: Guard::default(),
                certain: false,
                terminates: false,
            };
            raw.add_site(at, site, true);
        }
        // Other intrinsics are compiler defined operations. They cannot
        // call back into the program, so they add nothing to the graph, and
        // recording them as bodies without MIR would report every use of a
        // hint like `cold_path` as an unknown panic.
    }

    /// Records the panics a call into an entry point raises.
    pub(super) fn push_sink(
        &self,
        raw: &mut Raw<'tcx>,
        cx: Work<'tcx>,
        at: At,
        callee: Instance<'tcx>,
        operands: &[Spanned<mir::Operand<'tcx>>],
        sink: Sink,
    ) {
        let path = self.tcx.def_path_str(callee.def_id());
        let reason = self.panic_message(cx, operands).map_or_else(
            || format!("calls {path}"),
            |msg| format!("panics with \"{msg}\""),
        );
        for (category, termination) in sink.raises() {
            let site = PanicSite {
                category,
                termination,
                reason: reason.clone(),
                sink: Some(path.clone()),
                loc: self.loc_of(at.span),
                guard: Guard::default(),
                certain: false,
                terminates: false,
            };
            raw.add_site(at, site, true);
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
        let konst = instantiate(self.tcx, cx.inst, cx.env, konst.const_)?;
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
    pub(super) fn fn_constant(
        &self,
        cx: Work<'tcx>,
        konst: &mir::ConstOperand<'tcx>,
    ) -> Option<Instance<'tcx>> {
        let konst = instantiate(self.tcx, cx.inst, cx.env, konst.const_)?;
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
                let site = PanicSite {
                    category: Category::Explicit,
                    termination: Termination::Abort,
                    reason: format!(
                        "instantiating {ty} this way is invalid, so the \
                         check aborts"
                    ),
                    sink: None,
                    loc: self.loc_of(at.span),
                    guard: Guard::default(),
                    certain: false,
                    terminates: false,
                };
                raw.add_site(at, site, true);
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
}

/// Maps a compiler inserted check to a reportable category.
pub(super) const fn classify_assert<O>(
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
