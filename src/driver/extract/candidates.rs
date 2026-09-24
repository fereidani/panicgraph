//! What a drop, or a call through a trait object or a function pointer,
//! could run.

use panicgraph::{CallSite, EdgeKind, FuncKey, Guard, Reified};
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir,
    ty::{self, Instance, TypeVisitableExt, TypingEnv},
};

use super::{At, Extractor, Raw, Work};

impl<'tcx> Extractor<'tcx> {
    /// Records the drop glue reached by a `Drop` terminator.
    pub(super) fn push_drop(
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
        let display = format!("drop glue for {ty}");
        if let ty::Dynamic(predicates, _) = ty.kind() {
            // The object's own glue only calls through its vtable and would
            // read as clean, so the drop is a call through the object like
            // any of its methods.
            self.push_edge(raw, at, None, display, EdgeKind::Vtable, false);
            if let Some(principal) = predicates.principal_def_id() {
                self.push_drop_candidates(raw, cx, at, principal);
            }
            return;
        }
        let glue = Instance::resolve_drop_glue(self.tcx, ty);
        let key = self.symbol_of(glue).map(FuncKey);
        self.push_edge(raw, at, key, display, EdgeKind::Drop, false);
        raw.successors.push(Work {
            inst: glue,
            env: cx.env,
        });
    }

    /// Appends the drop glue of each type implementing the object's trait,
    /// the candidates a method called through the object would have.
    fn push_drop_candidates(
        &self,
        raw: &mut Raw<'tcx>,
        cx: Work<'tcx>,
        at: At,
        principal: DefId,
    ) {
        for impl_did in self.tcx.all_impls(principal) {
            let self_ty = self
                .tcx
                .impl_trait_ref(impl_did)
                .instantiate_identity()
                .skip_normalization()
                .self_ty();
            if self_ty.has_param()
                || !self_ty
                    .needs_drop(self.tcx, TypingEnv::fully_monomorphized())
            {
                // A generic impl has no single glue to name; the
                // unresolved edge already covers it.
                continue;
            }
            let glue = Instance::resolve_drop_glue(self.tcx, self_ty);
            let Some(key) = self.symbol_of(glue).map(FuncKey) else {
                continue;
            };
            let site = CallSite {
                callee: Some(key),
                callee_display: format!("drop glue for {self_ty}"),
                kind: EdgeKind::Vtable,
                loc: self.loc_of(at.span),
                guard: Guard::default(),
                barrier: false,
                terminates: false,
                candidate: true,
                sig: None,
                self_ty: Some(format!("{self_ty}")),
            };
            raw.add_call(at, site);
            raw.successors.push(Work {
                inst: glue,
                env: cx.env,
            });
        }
    }

    /// Appends every known implementation a dynamic call could reach.
    ///
    /// Candidates are marked as such and followed only when asked for. The
    /// unresolved edge stays regardless: an implementation in a crate the
    /// analysis never loads, or behind a generic impl, is still possible.
    pub(super) fn push_dyn_candidates(
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
            let site = CallSite {
                callee: Some(key),
                callee_display: self.tcx.def_path_str(target.def_id()),
                kind: EdgeKind::Vtable,
                loc: self.loc_of(at.span),
                guard: Guard::default(),
                barrier: false,
                terminates: false,
                candidate: true,
                sig: None,
                self_ty: Some(format!("{}", trait_ref.self_ty())),
            };
            raw.add_call(at, site);
            raw.successors.push(Work {
                inst: target,
                env: cx.env,
            });
        }
    }

    /// Records a type being made into a trait object, so that a call
    /// through one can name the implementations that can be behind it.
    ///
    /// Only reachable code is scanned, so a type no execution turns into an
    /// object is never a candidate, however many implementations the trait
    /// has. The object is made by unsizing a pointer to the type into one
    /// to the trait, and the type is what that pointer points at.
    pub(super) fn note_coerced(
        &mut self,
        cx: Work<'tcx>,
        stmt: &mir::Statement<'tcx>,
        mir: &mir::Body<'tcx>,
    ) {
        let mir::StatementKind::Assign(pair) = &stmt.kind else {
            return;
        };
        let mir::Rvalue::Cast(
            mir::CastKind::PointerCoercion(
                ty::adjustment::PointerCoercion::Unsize,
                _,
            ),
            operand,
            target,
        ) = &pair.1
        else {
            return;
        };
        let Some(target) = self.normalize(cx, *target) else {
            return;
        };
        let source = operand.ty(&mir.local_decls, self.tcx);
        let Some(source) = self.normalize(cx, source) else {
            return;
        };
        if !names_object(target) || names_object(source) {
            return;
        }
        if let Some(pointee) = pointee_of(source) {
            self.coerced.insert(format!("{pointee}"));
        }
    }

    /// Records a function being turned into a pointer, so indirect calls
    /// can name it as a candidate.
    ///
    /// Only reachable code is scanned, so a pointer that no execution can
    /// create never becomes a candidate. A closure coerced to a pointer
    /// names its `FnOnce` shim.
    pub(super) fn note_reified(
        &mut self,
        raw: &mut Raw<'tcx>,
        cx: Work<'tcx>,
        stmt: &mir::Statement<'tcx>,
        mir: &mir::Body<'tcx>,
    ) {
        let mir::StatementKind::Assign(pair) = &stmt.kind else {
            return;
        };
        let mir::Rvalue::Cast(
            mir::CastKind::PointerCoercion(coercion, _),
            operand,
            cast_ty,
        ) = &pair.1
        else {
            return;
        };
        let inst = match (coercion, operand) {
            (
                ty::adjustment::PointerCoercion::ReifyFnPointer(_),
                mir::Operand::Constant(konst),
            ) => self.fn_constant(cx, konst),
            (ty::adjustment::PointerCoercion::ClosureFnPointer(_), _) => self
                .normalize(cx, operand.ty(&mir.local_decls, self.tcx))
                .and_then(|closure| match *closure.kind() {
                    ty::Closure(did, args) => Some(Instance::resolve_closure(
                        self.tcx,
                        did,
                        args,
                        ty::ClosureKind::FnOnce,
                    )),
                    _ => None,
                }),
            _ => None,
        };
        let Some(inst) = inst else {
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
}

/// Whether a type is or holds a trait object.
fn names_object(ty: ty::Ty<'_>) -> bool {
    ty.walk().any(|part| {
        part.as_type()
            .is_some_and(|inner| matches!(inner.kind(), ty::Dynamic(..)))
    })
}

/// The type a pointer or a smart pointer points at.
///
/// A box names it outright, a reference or a raw pointer carries it, and
/// any other pointer wrapper keeps it as its first type argument, wrapped
/// once more where it is pinned.
fn pointee_of(ty: ty::Ty<'_>) -> Option<ty::Ty<'_>> {
    match ty.kind() {
        ty::Ref(_, inner, _) | ty::RawPtr(inner, _) => Some(*inner),
        ty::Adt(def, _) if def.is_box() => Some(ty.expect_boxed_ty()),
        ty::Adt(_, args) => {
            let inner = args.types().next()?;
            match inner.kind() {
                ty::Ref(..) | ty::RawPtr(..) => pointee_of(inner),
                ty::Adt(def, _) if def.is_box() => pointee_of(inner),
                _ => Some(inner),
            }
        }
        _ => None,
    }
}
