mod borrow_check;
mod ctxs;
mod error;
pub mod pre_decl;
mod subty;

use crate::ast::internal::{IdentTyped, Loan, PrvMapping};
use crate::ast::DataTy::Scalar;
use crate::ast::ThreadHierchyTy;
use crate::ast::*;
use crate::error::ErrorReported;
use ctxs::{GlobalCtx, KindCtx, TyCtx};
use error::*;
use std::ops::Deref;

type TyResult<T> = Result<T, TyError>;

// ∀ε ∈ Σ. Σ ⊢ ε
// --------------
//      ⊢ Σ
pub fn ty_check(compil_unit: &mut CompilUnit) -> Result<(), ErrorReported> {
    let compil_unit_clone = compil_unit.clone();
    let ty_checker = TyChecker::new(&compil_unit_clone);
    ty_checker.ty_check(compil_unit).map_err(|err| {
        err.emit(compil_unit.source);
        ErrorReported
    })
}

struct TyChecker {
    gl_ctx: GlobalCtx,
}

impl TyChecker {
    pub fn new(compil_unit: &CompilUnit) -> Self {
        let gl_ctx = GlobalCtx::new()
            .append_from_gl_fun_defs(&compil_unit.fun_defs)
            .append_fun_decls(&pre_decl::fun_decls());
        TyChecker { gl_ctx }
    }

    fn ty_check(&self, compil_unit: &mut CompilUnit) -> TyResult<()> {
        let errs = compil_unit.fun_defs.iter_mut().fold(
            Vec::<TyError>::new(),
            |mut errors, fun| match self.ty_check_global_fun_def(fun) {
                Ok(()) => errors,
                Err(err) => {
                    errors.push(err);
                    errors
                }
            },
        );
        if errs.is_empty() {
            Ok(())
        } else {
            Err(errs.into_iter().collect::<TyError>())
        }
    }

    // Σ ⊢ fn f <List[φ], List[ρ], List[α]> (x1: τ1, ..., xn: τn) → τr where List[ρ1:ρ2] { e }
    fn ty_check_global_fun_def(&self, gf: &mut FunDef) -> TyResult<()> {
        let kind_ctx = KindCtx::from(gf.generic_params.clone(), gf.prv_rels.clone())?;

        // TODO check that every prv_rel only uses provenance variables bound in generic_params

        // Build frame typing for this function
        let glf_frame = internal::append_idents_typed(
            &vec![],
            gf.param_decls
                .iter()
                .map(|ParamDecl { ident, ty, mutbl }| IdentTyped {
                    ident: ident.clone(),
                    ty: ty.clone(),
                    mutbl: *mutbl,
                })
                .collect(),
        );
        let ty_ctx = TyCtx::from(glf_frame);

        self.ty_check_expr(&kind_ctx, ty_ctx, gf.exec, &mut gf.body_expr)?;

        // t <= t_f
        let empty_ty_ctx = subty::check(
            &kind_ctx,
            TyCtx::new(),
            gf.body_expr.ty.as_ref().unwrap().dty(),
            &gf.ret_dty,
        )?;
        //TODO why is this the case?
        assert!(
            empty_ty_ctx.is_empty(),
            "Expected typing context to be empty. But TyCtx:\n {:?}",
            empty_ty_ctx
        );
        Ok(())
    }

    // TODO find out if Gamma is always correct by construction (similarly to Delta), also all 3 combined
    // e has type τ under Σ, Δ, and Γ, producing output context Γ'
    // sideconditions: Global Function Context Σ, Kinding context Δ and typing context are well-formed and
    //   type τ is well-formed under well-formed GlFunCtxt, kinding ctx, output context Γ'.
    // Σ; Δ; Γ ⊢ e :^exec τ ⇒ Γ′, side conditions:  ⊢ Σ;Δ;Γ and Σ;Δ;Γ′ ⊢ τ
    // This never returns a dead type, because typing an expression with a dead type is not possible.
    fn ty_check_expr(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        expr: &mut Expr,
    ) -> TyResult<TyCtx> {
        // TODO input contexts are well-formed
        //   well_formed_ctxs(gl_ctx, kind_ctx, &ty_ctx);
        let (res_ty_ctx, ty) = match &mut expr.expr {
            ExprKind::PlaceExpr(pl_expr) => {
                if pl_expr.is_place() {
                    self.ty_check_pl_expr_without_deref(kind_ctx, ty_ctx, exec, pl_expr)?
                } else {
                    self.ty_check_pl_expr_with_deref(kind_ctx, ty_ctx, exec, pl_expr)?
                }
            }
            ExprKind::LetProv(prvs, body) => {
                self.ty_check_letprov(kind_ctx, ty_ctx, exec, prvs, body)?
            }
            ExprKind::Let(mutbl, ident, ty, e) => {
                self.ty_check_let(kind_ctx, ty_ctx, exec, *mutbl, ident, ty, e)?
            }
            ExprKind::LetUninit(ident, ty) => self.ty_check_let_uninit(ty_ctx, exec, ident, ty)?,
            ExprKind::Seq(es) => self.ty_check_seq(kind_ctx, ty_ctx, exec, es)?,
            ExprKind::Lit(l) => Self::ty_check_literal(ty_ctx, l),
            ExprKind::Array(elems) => self.ty_check_array(kind_ctx, ty_ctx, exec, elems)?,
            ExprKind::Tuple(elems) => self.ty_check_tuple(kind_ctx, ty_ctx, exec, elems)?,
            ExprKind::TupleView(elems) => {
                self.ty_check_tuple_view(kind_ctx, ty_ctx, exec, elems)?
            }
            ExprKind::Proj(e, i) => self.ty_check_proj(kind_ctx, ty_ctx, exec, e, *i)?,
            ExprKind::App(ef, k_args, args) => {
                self.ty_check_app(kind_ctx, ty_ctx, exec, ef, k_args, args)?
            }
            ExprKind::DepApp(ef, k_args) => {
                self.ty_check_dep_app(kind_ctx, ty_ctx, exec, ef, k_args)?
            }
            ExprKind::Ref(prv, own, pl_expr) => {
                self.ty_check_borrow(kind_ctx, ty_ctx, exec, prv, *own, pl_expr)?
            }
            ExprKind::Index(pl_expr, index) => {
                self.ty_check_index_copy(kind_ctx, ty_ctx, exec, pl_expr, index)?
            }
            ExprKind::Assign(pl_expr, e) => {
                if pl_expr.is_place() {
                    self.ty_check_assign_place(kind_ctx, ty_ctx, exec, pl_expr, e)?
                } else {
                    self.ty_check_assign_deref(kind_ctx, ty_ctx, exec, pl_expr, e)?
                }
            }
            ExprKind::IdxAssign(pl_expr, idx, e) => {
                self.ty_check_idx_assign(kind_ctx, ty_ctx, exec, pl_expr, idx, e)?
            }
            ExprKind::ParFor(parall_collec, input, funs) => {
                self.ty_check_par_for(kind_ctx, ty_ctx, exec, parall_collec, input, funs)?
            }
            ExprKind::ForNat(var, range, body) => {
                self.ty_check_for_nat(kind_ctx, ty_ctx, exec, var, range, body)?
            }
            ExprKind::IfElse(cond, case_true, case_false) => {
                self.ty_check_if_else(kind_ctx, ty_ctx, exec, cond, case_true, case_false)?
            }
            ExprKind::For(ident, collec, body) => {
                self.ty_check_for(kind_ctx, ty_ctx, exec, ident, collec, body)?
            }
            ExprKind::While(cond, body) => {
                self.ty_check_while(kind_ctx, ty_ctx, exec, cond, body)?
            }
            ExprKind::Lambda(params, exec, ret_ty, body) => {
                self.ty_check_lambda(kind_ctx, ty_ctx, *exec, params, ret_ty, body)?
            }
            ExprKind::BinOp(bin_op, lhs, rhs) => {
                self.ty_check_binary_op(kind_ctx, ty_ctx, exec, bin_op, lhs, rhs)?
            }
            ExprKind::UnOp(un_op, e) => self.ty_check_unary_op(kind_ctx, ty_ctx, exec, un_op, e)?,
            ExprKind::Split(n, r1, r2, view) => {
                //                self.ty_check_split(kind_ctx, ty_ctx, exec, n, r1, r2, view)?
                unimplemented!()
            }
            ExprKind::BorrowIndex(_, _, _, _) => unimplemented!(),
            ExprKind::Idx(_, _) => {
                unimplemented!("This is helper syntax to index into non-place expressions.")
            }
            ExprKind::Deref(_) => panic!(
                "Dereferencing a non place expression is not a valid Descend \
        program and only exists for codegen."
            ),
        };

        if let Err(err) = self.ty_well_formed(kind_ctx, &res_ty_ctx, exec, &ty) {
            panic!("{:?}", err);
        }
        expr.ty = Some(ty);
        Ok(res_ty_ctx)
    }

    fn ty_check_split(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        n: &Nat,
        r1: &str,
        r2: &str,
        view: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        // let view_ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, view)?;
        // if let TyKind::View(ViewTy::Array(elem_ty, n)) = view.ty.unwrap().ty {
        //     if !(view_ty_ctx.loans_for_prv(r1)?.is_empty()) {
        //         return Err(TyError::PrvValueAlreadyInUse(r1.to_string()));
        //     }
        //     if !(view_ty_ctx.loans_for_prv(r2)?.is_empty()) {
        //         return Err(TyError::PrvValueAlreadyInUse(r2.to_string()));
        //     }
        //
        //     // TODO work on any dimension by using all contained provenances
        //     let TyKind::Data(DataTy::Ref(prv, own, mem, dty)) = elem_ty.ty {
        //         view_ty_ctx.loans_for_prv(prv)
        //     }
        // }
        unimplemented!()
    }

    fn ty_check_for_nat(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        var: &Ident,
        range: &Nat,
        body: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        let scoped_kind_ctx: KindCtx = kind_ctx.clone().append_idents(vec![IdentKinded {
            ident: var.clone(),
            kind: Kind::Nat,
        }]);
        let ty_ctx_1 = self.ty_check_expr(&scoped_kind_ctx, ty_ctx, exec, body)?;
        // let ty_ctx_2 = ty_check_expr(gl_ctx, &scoped_kind_ctx, ty_ctx_1.clone(), exec, body)?;
        // if &ty_ctx_1 != &ty_ctx_2 {
        //    return Err("Using a data type in loop that can only be used once.".to_string());
        // }
        Ok((
            ty_ctx_1,
            Ty::new(TyKind::Data(DataTy::Scalar(ScalarTy::Unit))),
        ))
    }

    fn ty_check_for(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        ident: &Ident,
        collec: &mut Expr,
        body: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        let collec_ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, collec)?;
        let ident_dty = match &collec.ty.as_ref().unwrap().ty {
            // TODO
            TyKind::Data(DataTy::Array(elem_dty, n)) => unimplemented!(),
            TyKind::Data(DataTy::Ref(prv, own, mem, arr_dty)) => {
                if let DataTy::Array(elem_dty, _) = arr_dty.as_ref() {
                    DataTy::Ref(prv.clone(), *own, mem.clone(), elem_dty.clone())
                } else {
                    return Err(TyError::String(format!(
                        "Expected reference to array data type, but found {:?}",
                        *arr_dty
                    )));
                }
            }
            _ => {
                return Err(TyError::String(format!(
                    "Expected array data type or reference to array data type, but found {:?}",
                    collec.ty.as_ref().unwrap()
                )));
            }
        };
        let collec_ty_ctx_with_ident = collec_ty_ctx.clone().append_ident_typed(IdentTyped::new(
            ident.clone(),
            Ty::new(TyKind::Data(ident_dty)),
            Mutability::Const,
        ));
        let final_ctx = self.ty_check_expr(kind_ctx, collec_ty_ctx_with_ident, exec, body)?;
        if !matches!(
            body.ty.as_ref().unwrap().ty,
            TyKind::Data(DataTy::Scalar(ScalarTy::Unit))
        ) {
            return Err(TyError::String(
                "A loop body cannot have a return type.".to_string(),
            ));
        }
        match final_ctx.drop_ident(ident) {
            Some(ctx) if ctx == collec_ty_ctx => {
                Ok((ctx, Ty::new(TyKind::Data(DataTy::Scalar(ScalarTy::Unit)))))
            }
            _ => Err(TyError::String(
                "Trying to use illegal element in for-loop.".to_string(),
            )),
        }
    }

    fn ty_check_while(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        cond: &mut Expr,
        body: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        let cond_ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, cond)?;
        let body_ty_ctx = self.ty_check_expr(kind_ctx, cond_ty_ctx, exec, body)?;

        let cond_temp_ty_ctx = self.ty_check_expr(kind_ctx, body_ty_ctx.clone(), exec, cond)?;
        if body_ty_ctx != cond_temp_ty_ctx {
            return Err(TyError::String(
                "Context should have stayed the same".to_string(),
            ));
        }
        let body_temp_ty_ctx = self.ty_check_expr(kind_ctx, body_ty_ctx.clone(), exec, body)?;
        if body_ty_ctx != body_temp_ty_ctx {
            return Err(TyError::String(
                "Context should have stayed the same".to_string(),
            ));
        }

        let cond_ty = cond.ty.as_ref().unwrap();
        let body_ty = body.ty.as_ref().unwrap();

        if !matches!(&cond_ty.ty, TyKind::Data(DataTy::Scalar(ScalarTy::Bool))) {
            return Err(TyError::String(format!(
                "Expected condition in while loop, instead got {:?}",
                cond_ty
            )));
        }
        if !matches!(&body_ty.ty, TyKind::Data(DataTy::Scalar(ScalarTy::Bool))) {
            return Err(TyError::String(format!(
                "Body of while loop is not of unit type, instead got {:?}",
                body_ty
            )));
        }
        Ok((
            body_ty_ctx,
            Ty::new(TyKind::Data(DataTy::Scalar(ScalarTy::Unit))),
        ))
    }

    fn ty_check_if_else(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        cond: &mut Expr,
        case_true: &mut Expr,
        case_false: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        // TODO deal with provenances in cases
        let cond_ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, cond)?;
        let _case_true_ty_ctx =
            self.ty_check_expr(kind_ctx, cond_ty_ctx.clone(), exec, case_true)?;
        let case_false_ty_ctx = self.ty_check_expr(kind_ctx, cond_ty_ctx, exec, case_false)?;

        let cond_ty = cond.ty.as_ref().unwrap();
        let case_true_ty = case_true.ty.as_ref().unwrap();
        let case_false_ty = case_false.ty.as_ref().unwrap();

        if !matches!(&cond_ty.ty, TyKind::Data(DataTy::Scalar(ScalarTy::Bool))) {
            return Err(TyError::String(format!(
                "Expected condition in if case, instead got {:?}",
                cond_ty
            )));
        }
        if !matches!(
            &case_true_ty.ty,
            TyKind::Data(DataTy::Scalar(ScalarTy::Unit))
        ) {
            return Err(TyError::String(format!(
                "Body of the true case is not of unit type, instead got {:?}",
                case_true_ty
            )));
        }
        if !matches!(
            &case_false_ty.ty,
            TyKind::Data(DataTy::Scalar(ScalarTy::Unit))
        ) {
            return Err(TyError::String(format!(
                "Body of the false case is not of unit type, instead got {:?}",
                case_false_ty
            )));
        }

        Ok((
            case_false_ty_ctx,
            Ty::new(TyKind::Data(DataTy::Scalar(ScalarTy::Unit))),
        ))
    }

    // TODO split up groupings, i.e., deal with TupleViews and require enough functions.
    fn ty_check_par_for(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        parall_collec: &mut Expr,
        input: &mut Expr,
        funs: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        fn to_exec_and_size(parall_collec: &Expr) -> Exec {
            match &parall_collec.ty.as_ref().unwrap().ty {
                TyKind::ThreadHierchy(th_hy) => match th_hy.as_ref() {
                    ThreadHierchyTy::BlockGrp(_, _, _, _, _, _) => Exec::GpuGrid,
                    ThreadHierchyTy::ThreadGrp(_, _, _) => Exec::GpuBlock,
                    ThreadHierchyTy::WarpGrp(_) => Exec::GpuBlock,
                    ThreadHierchyTy::Warp => Exec::GpuWarp,
                },
                _ => panic!("Expected a parallel collection: Grid or Block."),
            }
        }

        let parall_collec_ty_ctx =
            self.ty_check_expr(kind_ctx, ty_ctx.clone(), exec, parall_collec)?;
        let allowed_exec = to_exec_and_size(parall_collec);
        if allowed_exec != exec {
            return Err(TyError::String(format!(
                "Trying to run a parallel for-loop over {:?} inside of {:?}",
                parall_collec, exec
            )));
        }
        let input_ty_ctx = self.ty_check_expr(kind_ctx, parall_collec_ty_ctx, exec, input)?;
        // Dismiss the resulting typing context. A par_for always synchronizes. Therefore everything
        // that is used for the par_for can safely be reused.
        let _funs_ty_ctx = self.ty_check_expr(kind_ctx, input_ty_ctx.clone(), exec, funs)?;
        self.executable_over_parall_collec_and_input(funs, parall_collec, input)?;
        Ok((
            input_ty_ctx,
            Ty::new(TyKind::Data(DataTy::Scalar(ScalarTy::Unit))),
        ))
    }

    fn executable_over_parall_collec_and_input(
        &self,
        fun: &Expr,
        parall_collec: &Expr,
        input: &Expr,
    ) -> TyResult<()> {
        let in_param_tys: Vec<_> = match &input.ty.as_ref().unwrap().ty {
            TyKind::View(ViewTy::Tuple(input_tys)) => input_tys
                .iter()
                .map(|t| match &t.ty {
                    TyKind::View(ViewTy::Array(tty, n)) => tty.as_ref(),
                    _ => t,
                })
                .collect(),
            _ => {
                return Err(TyError::String(
                    "Provided input expression is not a tuple view.".to_string(),
                ));
            }
        };

        match &fun.ty.as_ref().unwrap().ty {
            // FIXME unimplemented
            TyKind::View(ViewTy::Tuple(funs)) => {
                if let TyKind::View(ViewTy::Tuple(pcs)) = &parall_collec.ty.as_ref().unwrap().ty {
                    if pcs.len() != funs.len() {
                        return Err(TyError::String(
                            "Branching in parallel collections is of different amount than \
                            provided functions."
                                .to_string(),
                        ));
                    }
                    for (f, p) in funs.iter().zip(pcs) {
                        //executable_over_parall_collec_and_input(f, p, input)?
                        unimplemented!()
                    }
                }
                Ok(())
            }
            TyKind::Fn(_, param_tys, fun_exec, ret_ty) => {
                let parall_elem_ty = match &parall_collec.ty.as_ref().unwrap().ty {
                    TyKind::ThreadHierchy(th_hy) => match th_hy.as_ref() {
                        ThreadHierchyTy::BlockGrp(_, _, _, m1, m2, m3) => Some(
                            ThreadHierchyTy::ThreadGrp(m1.clone(), m2.clone(), m3.clone()),
                        ),
                        ThreadHierchyTy::ThreadGrp(_, _, _) => None,
                        ThreadHierchyTy::WarpGrp(_) => Some(ThreadHierchyTy::Warp),
                        ThreadHierchyTy::Warp => None,
                    },
                    _ => {
                        return Err(TyError::String(
                            "Provided expression is not a parallel collection.".to_string(),
                        ))
                    }
                };
                let param_offset = match parall_elem_ty {
                    Some(_) => 1,
                    None => 0,
                };
                let num_fun_params = in_param_tys.len() + param_offset;
                if param_tys.len() != num_fun_params {
                    return Err(TyError::String(format!(
                        "Wrong amount of parameters in provided function. Expected {},\
                    one for parallelism expression and one for input.",
                        num_fun_params
                    )));
                }
                let fun_parall_elem_ty = match &param_tys[0].ty {
                    TyKind::ThreadHierchy(th_hierchy) => Some(th_hierchy.as_ref().clone()),
                    _ => None,
                };
                let fun_input_elem_tys: Vec<_> =
                    param_tys[param_offset..].iter().map(|t| t).collect();

                if &fun_parall_elem_ty != &parall_elem_ty {
                    return Err(TyError::String(format!(
                        "Function does not fit the provided parallel collection. \
                        Expected: {:?}, but found: {:?}",
                        parall_elem_ty, fun_parall_elem_ty
                    )));
                }
                if fun_input_elem_tys != in_param_tys {
                    return Err(TyError::String(format!(
                        "Function does not fit the provided input. \
                        Expected: {:?},\n but found: {:?}",
                        in_param_tys, fun_input_elem_tys
                    )));
                }
                let f_exec = match parall_elem_ty {
                    Some(ThreadHierchyTy::ThreadGrp(_, _, _)) => Exec::GpuBlock,
                    Some(ThreadHierchyTy::WarpGrp(_)) => Exec::GpuBlock,
                    Some(ThreadHierchyTy::Warp) => Exec::GpuWarp,
                    None => Exec::GpuThread,
                    Some(ThreadHierchyTy::BlockGrp(_, _, _, _, _, _)) => {
                        return Err(TyError::String(
                            "Cannot parallelize over multiple Grids.".to_string(),
                        ))
                    }
                };
                if fun_exec != &f_exec {
                    return Err(TyError::String(
                        "Execution resource does not fit.".to_string(),
                    ));
                }
                if &ret_ty.as_ref().ty != &TyKind::Data(Scalar(ScalarTy::Unit)) {
                    return Err(TyError::String(
                        "Function has wrong return type. Expected ().".to_string(),
                    ));
                }

                Ok(())
            }
            _ => Err(TyError::String(
                "The provided expression is not a function or tuple view of functions.".to_string(),
            )),
        }
    }

    fn ty_check_lambda(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        params: &mut [ParamDecl],
        ret_dty: &DataTy,
        body: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        // Build frame typing for this function
        let fun_frame = internal::append_idents_typed(
            &vec![],
            params
                .iter()
                .map(|ParamDecl { ident, ty, mutbl }| IdentTyped {
                    ident: ident.clone(),
                    ty: ty.clone(),
                    mutbl: mutbl.clone(),
                })
                .collect(),
        );
        // Copy porvenance mappings into scope and append scope frame.
        // FIXME check that no variables are captured.
        let fun_ty_ctx = ty_ctx.clone().append_frm_ty(fun_frame);

        self.ty_check_expr(kind_ctx, fun_ty_ctx, exec, body)?;

        // t <= t_f
        let empty_ty_ctx = subty::check(
            kind_ctx,
            TyCtx::new(),
            body.ty.as_ref().unwrap().dty(),
            ret_dty,
        )?;

        assert!(
            empty_ty_ctx.is_empty(),
            "Expected typing context to be empty. But TyCtx:\n {:?}",
            empty_ty_ctx
        );

        let fun_ty = Ty::new(TyKind::Fn(
            vec![],
            params.iter().map(|decl| decl.ty.clone()).collect(),
            exec,
            Box::new(Ty::new(TyKind::Data(ret_dty.clone()))),
        ));

        Ok((ty_ctx, fun_ty))
    }

    fn ty_check_letprov(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        prvs: &[String],
        body: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        let mut ty_ctx_with_prvs = ty_ctx;
        for prv in prvs {
            ty_ctx_with_prvs = ty_ctx_with_prvs.append_prv_mapping(PrvMapping {
                prv: prv.clone(),
                loans: std::collections::HashSet::new(),
            })
        }
        // TODO do we have to check that the prvs in res_ty_ctx have loans now?
        let res_ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx_with_prvs, exec, body)?;
        Ok((res_ty_ctx, body.ty.as_ref().unwrap().clone()))
    }

    fn ty_check_assign_place(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        pl_expr: &mut PlaceExpr,
        e: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        let assigned_val_ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, e)?;

        let place = pl_expr.to_place().unwrap();
        let place_ty = assigned_val_ty_ctx.place_ty(&place)?;
        if matches!(&place_ty.ty, TyKind::View(_)) {
            return Err(TyError::String(format!(
                "Assigning views is forbidden. Trying to assign view {:?}",
                e
            )));
        }
        let ident_ty = assigned_val_ty_ctx.ident_ty(&place.ident)?;
        if pl_expr.is_place() && ident_ty.mutbl != Mutability::Mut {
            return Err(TyError::AssignToConst(pl_expr.clone(), Box::new(e.clone())));
        }

        // If the place is not dead, check that it is safe to use, otherwise it is safe to use anyway.
        if !matches!(&place_ty.ty, TyKind::Data(DataTy::Dead(_))) {
            let pl_uniq_loans = borrow_check::ownership_safe(
                self,
                kind_ctx,
                &assigned_val_ty_ctx,
                exec,
                &[],
                Ownership::Uniq,
                pl_expr,
            )
            .map_err(|err| {
                TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Uniq, err)
            })?;
            // TODO remove this is always true if borrow_check::ownership_safe succeeds
            // assert_eq!(pl_uniq_loans.len(), 1);
            // let place_loan = Loan {
            //     place_expr: pl_expr.clone(),
            //     own: Ownership::Uniq,
            // };
            // if !matches!(pl_uniq_loans.get(&place_loan), Some(_)) {
            //     return Err(TyError::)
            // }
        }

        let after_subty_ctx = subty::check(
            kind_ctx,
            assigned_val_ty_ctx,
            e.ty.as_ref().unwrap().dty(),
            place_ty.dty(),
        )?;
        let adjust_place_ty_ctx =
            after_subty_ctx.set_place_ty(&place, e.ty.as_ref().unwrap().clone());
        Ok((
            adjust_place_ty_ctx.without_reborrow_loans(pl_expr),
            Ty::new(TyKind::Data(DataTy::Scalar(ScalarTy::Unit))),
        ))
    }

    fn ty_check_assign_deref(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        deref_expr: &mut PlaceExpr,
        e: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        let assigned_val_ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, e)?;
        let deref_ty = self.place_expr_ty_under_exec_own(
            kind_ctx,
            &assigned_val_ty_ctx,
            exec,
            Ownership::Uniq,
            deref_expr,
        )?;

        if !deref_ty.is_fully_alive() {
            return Err(TyError::String(
                "Trying to assign through reference, to a type which is not fully alive."
                    .to_string(),
            ));
        }

        if let TyKind::Data(deref_dty) = &deref_ty.ty {
            borrow_check::ownership_safe(
                self,
                kind_ctx,
                &assigned_val_ty_ctx,
                exec,
                &[],
                Ownership::Uniq,
                deref_expr,
            )
            .map_err(|err| {
                TyError::ConflictingBorrow(Box::new(deref_expr.clone()), Ownership::Uniq, err)
            })?;

            let after_subty_ctx = subty::check(
                kind_ctx,
                assigned_val_ty_ctx,
                e.ty.as_ref().unwrap().dty(),
                deref_dty,
            )?;
            Ok((
                after_subty_ctx.without_reborrow_loans(deref_expr),
                Ty::new(TyKind::Data(DataTy::Scalar(ScalarTy::Unit))),
            ))
        } else {
            Err(TyError::String(
                "Trying to dereference view type which is not allowed.".to_string(),
            ))
        }
    }

    fn ty_check_idx_assign(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        pl_expr: &mut PlaceExpr,
        idx: &Nat,
        e: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        if exec != Exec::CpuThread && exec != Exec::GpuThread {
            return Err(TyError::String(format!(
                "Trying to assign to memory from {}.",
                exec
            )));
        }

        let assigned_val_ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, e)?;
        let pl_expr_ty = self.place_expr_ty_under_exec_own(
            kind_ctx,
            &assigned_val_ty_ctx,
            exec,
            Ownership::Uniq,
            pl_expr,
        )?;
        let (n, dty, own, mem) = match pl_expr_ty.ty {
            TyKind::Data(DataTy::Array(elem_ty, n)) => unimplemented!(), //(Ty::Data(*elem_ty), n),
            TyKind::Data(DataTy::At(arr_dty, mem)) => {
                if let DataTy::Array(elem_ty, n) = arr_dty.as_ref() {
                    unimplemented!() //(Ty::Data(*elem_ty), n)
                } else {
                    return Err(TyError::String(
                        "Trying to index into non array type.".to_string(),
                    ));
                }
            }
            TyKind::View(ViewTy::Array(elem_ty, n)) => {
                if let TyKind::Data(DataTy::Ref(_, own, mem, dty)) = elem_ty.ty {
                    (n, dty, own, mem)
                } else {
                    return Err(TyError::String(
                        "Expected a reference as element type of array view.".to_string(),
                    ));
                }
            }
            _ => {
                return Err(TyError::String(
                    "Trying to index into non array type.".to_string(),
                ))
            }
        };

        if !dty.is_fully_alive() {
            return Err(TyError::String(
                "Trying to assign through reference, to a type which is not fully alive."
                    .to_string(),
            ));
        }
        Self::accessible_memory(exec, &mem)?;

        if own != Ownership::Uniq {
            return Err(TyError::String(
                "Cannot assigned through shared references.".to_string(),
            ));
        }

        match n.partial_cmp(idx) {
            Some(std::cmp::Ordering::Less) => (),
            Some(std::cmp::Ordering::Equal) | Some(std::cmp::Ordering::Greater) => {
                return Err(TyError::String(
                    "Trying to access array out-of-bounds.".to_string(),
                ))
            }
            None => println!(
            "WARNING: Cannot check out-of-bounds indexing for index `{}` in array with size `{}`",
            idx, n
        ),
        };
        // TODO Only relevant for non array view indexing? (because array views cannot be borrowed?)
        // borrow_check::ownership_safe(
        //     kind_ctx,
        //     &assigned_val_ty_ctx,
        //     &[],
        //     Ownership::Uniq,
        //     deref_expr,
        // )?;

        let after_subty_ctx = subty::check(
            kind_ctx,
            assigned_val_ty_ctx,
            e.ty.as_ref().unwrap().dty(),
            &dty,
        )?;

        Ok((
            after_subty_ctx,
            Ty::new(TyKind::Data(DataTy::Scalar(ScalarTy::Unit))),
        ))
    }

    fn ty_check_index_copy(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        pl_expr: &mut PlaceExpr,
        idx: &mut Nat,
    ) -> TyResult<(TyCtx, Ty)> {
        // TODO refactor
        borrow_check::ownership_safe(self, kind_ctx, &ty_ctx, exec, &[], Ownership::Shrd, pl_expr)
            .map_err(|err| {
                TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Shrd, err)
            })?;
        let pl_expr_ty =
            self.place_expr_ty_under_exec_own(kind_ctx, &ty_ctx, exec, Ownership::Shrd, pl_expr)?;
        pl_expr.ty = Some(pl_expr_ty.clone());
        let (elem_dty, n) = match pl_expr_ty.ty {
            TyKind::Data(DataTy::Array(elem_ty, n)) => (*elem_ty, n),
            TyKind::Data(DataTy::At(arr_ty, _)) => {
                if let DataTy::Array(elem_ty, n) = *arr_ty {
                    (*elem_ty, n)
                } else {
                    return Err(TyError::String(
                        "Trying to index into non array type.".to_string(),
                    ));
                }
            }
            TyKind::View(ViewTy::Array(ref_dty, n)) => {
                if let TyKind::Data(DataTy::Ref(_, own, mem, dty)) = ref_dty.ty {
                    Self::accessible_memory(exec, &mem)?;
                    // TODO is ownership checking necessary here?
                    (*dty, n)
                } else {
                    return Err(TyError::String(
                        "Expected a reference as element type of array view.".to_string(),
                    ));
                }
            }
            TyKind::Data(DataTy::Ref(_, _, _, arr_ty)) => match *arr_ty {
                DataTy::Array(elem_ty, n) => (*elem_ty, n),
                _ => {
                    return Err(TyError::String(
                        "Trying to index into non array type.".to_string(),
                    ))
                }
            },
            _ => {
                return Err(TyError::String(
                    "Trying to index into non array type.".to_string(),
                ))
            }
        };

        match n.partial_cmp(idx) {
            Some(std::cmp::Ordering::Less) => (),
            Some(std::cmp::Ordering::Equal) | Some(std::cmp::Ordering::Greater) => {
                return Err(TyError::String(
                    "Trying to access array out-of-bounds.".to_string(),
                ))
            }
            None => println!(
            "WARNING: Cannot check out-of-bounds indexing for index `{}` in array with size `{}`",
            idx, n
        ),
        };

        if elem_dty.copyable() {
            Ok((ty_ctx, Ty::new(TyKind::Data(elem_dty))))
        } else {
            Err(TyError::String(
                "Cannot move out of array type.".to_string(),
            ))
        }
    }

    // FIXME currently assumes that binary operators exist only for f32 and i32 and that both
    //  arguments have to be of the same type
    fn ty_check_binary_op(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        bin_op: &BinOp,
        lhs: &mut Expr,
        rhs: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        let lhs_ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, lhs)?;
        let rhs_ty_ctx = self.ty_check_expr(kind_ctx, lhs_ty_ctx, exec, rhs)?;

        let lhs_ty = lhs.ty.as_ref().unwrap();
        let rhs_ty = rhs.ty.as_ref().unwrap();
        let ret = match bin_op {
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Mod
            | BinOp::And
            | BinOp::Or => lhs_ty.clone(),
            BinOp::Eq | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Neq => {
                Ty::new(TyKind::Data(DataTy::Scalar(ScalarTy::Bool)))
            }
        };
        match (&lhs_ty.ty, &rhs_ty.ty) {
            (
                TyKind::Data(DataTy::Scalar(ScalarTy::F32)),
                TyKind::Data(DataTy::Scalar(ScalarTy::F32)),
            )
            | (
                TyKind::Data(DataTy::Scalar(ScalarTy::I32)),
                TyKind::Data(DataTy::Scalar(ScalarTy::I32)),
            ) => Ok((rhs_ty_ctx, ret)),
            _ => Err(TyError::String(format!(
            "Expected the same number types for operator {}, instead got\n Lhs: {:?}\n Rhs: {:?}",
            bin_op, lhs, rhs
        ))),
        }
    }

    // FIXME currently assumes that binary operators exist only for f32 and i32
    fn ty_check_unary_op(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        un_op: &UnOp,
        e: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        let res_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, e)?;
        let e_ty = e.ty.as_ref().unwrap();
        match &e_ty.ty {
            TyKind::Data(DataTy::Scalar(ScalarTy::F32))
            | TyKind::Data(DataTy::Scalar(ScalarTy::I32)) => Ok((res_ctx, e_ty.clone())),
            _ => Err(TyError::String(format!(
                "Exected a number type (i.e., f32 or i32), but found {:?}",
                e_ty
            ))),
        }
    }

    // TODO base implementation on ty_check_dep_app
    fn ty_check_app(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        ef: &mut Expr,
        k_args: &mut [ArgKinded],
        args: &mut [Expr],
    ) -> TyResult<(TyCtx, Ty)> {
        // TODO check well-kinded: FrameTyping, Prv, Ty
        let mut res_ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, ef)?;
        if let TyKind::Fn(gen_params, param_tys, exec_f, out_ty) = &ef.ty.as_ref().unwrap().ty {
            if !exec_f.callable_in(exec) {
                return Err(TyError::String(format!(
                    "Trying to apply function for execution resource `{}` \
                under execution resource `{}`",
                    exec_f, exec
                )));
            }
            if gen_params.len() != k_args.len() {
                return Err(TyError::String(format!(
                    "Wrong amount of generic arguments. Expected {}, found {}",
                    gen_params.len(),
                    k_args.len()
                )));
            }
            for (gp, kv) in gen_params.iter().zip(&*k_args) {
                self.check_arg_has_correct_kind(kind_ctx, &gp.kind, kv)?;
            }
            if args.len() != param_tys.len() {
                return Err(TyError::String(format!(
                    "Wrong amount of arguments. Expected {}, found {}",
                    param_tys.len(),
                    args.len()
                )));
            }
            let subst_param_tys: Vec<_> = param_tys
                .iter()
                .map(|ty| {
                    let mut subst_ty = ty.clone();
                    for (gen_param, k_arg) in gen_params.iter().zip(&*k_args) {
                        subst_ty = subst_ty.subst_ident_kinded(gen_param, k_arg)
                    }
                    subst_ty
                })
                .collect();

            for (arg, param_ty) in args.iter_mut().zip(subst_param_tys) {
                res_ty_ctx = self.ty_check_expr(kind_ctx, res_ty_ctx, exec, arg)?;
                if arg.ty.as_ref().unwrap() != &param_ty {
                    return Err(TyError::String(format!(
                        "Argument types do not match.\n Expected {:?}, but found {:?}.",
                        param_ty,
                        arg.ty.as_ref().unwrap()
                    )));
                }
            }
            // TODO check provenance relations
            let subst_out_ty = {
                let mut subst_ty = out_ty.as_ref().clone();
                for (gen_param, k_arg) in gen_params.iter().zip(&*k_args) {
                    subst_ty = subst_ty.subst_ident_kinded(gen_param, k_arg)
                }
                subst_ty
            };
            Ok((res_ty_ctx, subst_out_ty))
        } else {
            Err(TyError::String(format!(
                "The provided function expression\n {:?}\n does not have a function type.",
                ef
            )))
        }
    }

    fn ty_check_dep_app(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        ef: &mut Expr,
        k_args: &mut [ArgKinded],
    ) -> TyResult<(TyCtx, Ty)> {
        let mut res_ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, ef)?;
        if let TyKind::Fn(gen_params, param_tys, exec_f, out_ty) = &ef.ty.as_ref().unwrap().ty {
            if gen_params.len() != k_args.len() {
                return Err(TyError::String(format!(
                    "Wrong amount of generic arguments. Expected {}, found {}",
                    gen_params.len(),
                    k_args.len()
                )));
            }
            for (gp, kv) in gen_params.iter().zip(&*k_args) {
                self.check_arg_has_correct_kind(kind_ctx, &gp.kind, kv)?;
            }
            let subst_param_tys: Vec<_> = param_tys
                .iter()
                .map(|ty| {
                    let mut subst_ty = ty.clone();
                    for (gen_param, k_arg) in gen_params.iter().zip(&*k_args) {
                        subst_ty = subst_ty.subst_ident_kinded(gen_param, k_arg)
                    }
                    subst_ty
                })
                .collect();
            let subst_out_ty = {
                let mut subst_ty = out_ty.as_ref().clone();
                for (gen_param, k_arg) in gen_params.iter().zip(&*k_args) {
                    subst_ty = subst_ty.subst_ident_kinded(gen_param, k_arg)
                }
                subst_ty
            };
            let subst_fun_ty = Ty::new(TyKind::Fn(
                vec![],
                subst_param_tys,
                *exec_f,
                Box::new(subst_out_ty),
            ));
            Ok((res_ty_ctx, subst_fun_ty))
        } else {
            Err(TyError::String(format!(
                "The provided function expression\n {:?}\n does not have a function type.",
                ef
            )))
        }
    }

    fn check_arg_has_correct_kind(
        &self,
        kind_ctx: &KindCtx,
        expected: &Kind,
        kv: &ArgKinded,
    ) -> TyResult<()> {
        match kv {
            ArgKinded::Provenance(_) if expected == &Kind::Provenance => Ok(()),
            ArgKinded::Ty(_) if expected == &Kind::Ty => Ok(()),
            ArgKinded::Nat(_) if expected == &Kind::Nat => Ok(()),
            ArgKinded::Memory(_) if expected == &Kind::Memory => Ok(()),
            // TODO?
            //  KindedArg::Frame(_) if expected == &Kind::Frame => Ok(()),
            ArgKinded::Ident(k_ident) if expected == kind_ctx.get_kind(k_ident)? => Ok(()),
            _ => Err(TyError::String(format!(
                "expected argument of kind {:?}, but the provided argument is {:?}",
                expected, kv
            ))),
        }
    }

    fn ty_check_tuple(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        elems: &mut [Expr],
    ) -> TyResult<(TyCtx, Ty)> {
        let mut tmp_ty_ctx = ty_ctx;
        for elem in elems.iter_mut() {
            tmp_ty_ctx = self.ty_check_expr(kind_ctx, tmp_ty_ctx, exec, elem)?;
        }
        let elem_tys: TyResult<Vec<_>> = elems
            .iter()
            .map(|elem| match &elem.ty.as_ref().unwrap().ty {
                TyKind::Data(dty) => Ok(dty.clone()),
                TyKind::View(_) => Err(TyError::String(
                    "Tuple elements cannot be views.".to_string(),
                )),
                TyKind::ThreadHierchy(_) => Err(TyError::String(
                    "Tuple elements must be data types, but found thread hierarchy.".to_string(),
                )),
                TyKind::Ident(_) => Err(TyError::String(
                    "Tuple elements must be data types, but found general type identifier."
                        .to_string(),
                )),
                TyKind::Fn(_, _, _, _) => Err(TyError::String(
                    "Tuple elements must be data types, but found function type.".to_string(),
                )),
            })
            .collect();
        Ok((tmp_ty_ctx, Ty::new(TyKind::Data(DataTy::Tuple(elem_tys?)))))
    }

    fn ty_check_proj(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        e: &mut Expr,
        i: usize,
    ) -> TyResult<(TyCtx, Ty)> {
        if let ExprKind::PlaceExpr(_) = e.expr {
            panic!("Place expression should have been typechecked by a different rule.")
        }

        let tuple_ty_ctx = self.ty_check_expr(kind_ctx, ty_ctx, exec, e)?;
        let elem_ty = match &e.ty.as_ref().unwrap().ty {
            TyKind::Data(DataTy::Tuple(dtys)) => match dtys.get(i) {
                Some(dty) => Ty::new(TyKind::Data(dty.clone())),
                None => {
                    return Err(TyError::String(format!(
                        "Cannot project element `{}` from tuple with {} elements.",
                        i,
                        dtys.len()
                    )))
                }
            },
            TyKind::View(ViewTy::Tuple(tys)) => match tys.get(i) {
                Some(ty) => ty.clone(),
                None => {
                    return Err(TyError::String(format!(
                        "Cannot project element `{}` from tuple with {} elements.",
                        i,
                        tys.len()
                    )))
                }
            },
            _ => {
                return Err(TyError::String(
                    "Cannot project from non tuple type.".to_string(),
                ))
            }
        };

        Ok((tuple_ty_ctx, elem_ty))
    }

    fn ty_check_tuple_view(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        elems: &mut [Expr],
    ) -> TyResult<(TyCtx, Ty)> {
        let mut tmp_ty_ctx = ty_ctx;
        for elem in elems.iter_mut() {
            tmp_ty_ctx = self.ty_check_expr(kind_ctx, tmp_ty_ctx, exec, elem)?;
        }
        let elem_tys: Vec<_> = elems
            .iter()
            .map(|elem| elem.ty.as_ref().unwrap().clone())
            .collect();
        Ok((tmp_ty_ctx, Ty::new(TyKind::View(ViewTy::Tuple(elem_tys)))))
    }

    fn ty_check_array(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        elems: &mut Vec<Expr>,
    ) -> TyResult<(TyCtx, Ty)> {
        assert!(!elems.is_empty());
        let mut tmp_ty_ctx = ty_ctx;
        for elem in elems.iter_mut() {
            tmp_ty_ctx = self.ty_check_expr(kind_ctx, tmp_ty_ctx, exec, elem)?;
        }
        let ty = elems.first().unwrap().ty.as_ref();
        if !matches!(&ty.unwrap().ty, TyKind::Data(_)) {
            return Err(TyError::String(
                "Array elements cannot be views.".to_string(),
            ));
        }
        if elems.iter().any(|elem| ty != elem.ty.as_ref()) {
            Err(TyError::String(
                "Not all provided elements have the same type.".to_string(),
            ))
        } else {
            Ok((
                tmp_ty_ctx,
                Ty::new(TyKind::Data(DataTy::Array(
                    Box::new(ty.as_ref().unwrap().dty().clone()),
                    Nat::Lit(elems.len()),
                ))),
            ))
        }
    }

    fn ty_check_literal(ty_ctx: TyCtx, l: &mut Lit) -> (TyCtx, Ty) {
        let scalar_data = match l {
            Lit::Unit => ScalarTy::Unit,
            Lit::Bool(_) => ScalarTy::Bool,
            Lit::I32(_) => ScalarTy::I32,
            Lit::U32(_) => ScalarTy::U32,
            Lit::F32(_) => ScalarTy::F32,
        };
        (ty_ctx, Ty::new(TyKind::Data(DataTy::Scalar(scalar_data))))
    }

    fn ty_check_let(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        mutbl: Mutability,
        ident: &mut Ident,
        ty: &Option<Ty>,
        expr: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        let ty_ctx_e = self.ty_check_expr(kind_ctx, ty_ctx, exec, expr)?;
        let e1_ty = expr.ty.as_ref().unwrap();
        let ty = if let Some(tty) = ty { tty } else { e1_ty };

        let ty_ctx_sub = match (&ty.ty, &e1_ty.ty) {
            (TyKind::View(_), TyKind::View(_)) => {
                // TODO use subtyping
                if ty != e1_ty {
                    return Err(TyError::String(format!(
                        "Trying to bind view expression of type {:?} to identifier of type {:?}",
                        e1_ty, ty
                    )));
                }
                ty_ctx_e
            }
            (TyKind::Data(dty), TyKind::Data(e1_dty)) => {
                subty::check(kind_ctx, ty_ctx_e, e1_dty, dty)?
            }
            _ => {
                return Err(TyError::String(format!(
                    "Trying to bind expression of type {:?} to identifier of type {:?}",
                    e1_ty, ty
                )))
            }
        };
        let ident_with_annotated_ty = IdentTyped::new(ident.clone(), ty.clone(), mutbl);
        let ty_ctx_with_ident = ty_ctx_sub.append_ident_typed(ident_with_annotated_ty);
        Ok((
            ty_ctx_with_ident,
            Ty::new(TyKind::Data(DataTy::Scalar(ScalarTy::Unit))),
        ))
    }

    // TODO repsect exec?
    fn ty_check_let_uninit(
        &self,
        ty_ctx: TyCtx,
        exec: Exec,
        ident: &Ident,
        ty: &Ty,
    ) -> TyResult<(TyCtx, Ty)> {
        if let TyKind::Data(dty) = &ty.ty {
            let ident_with_ty = IdentTyped::new(
                ident.clone(),
                Ty::new(TyKind::Data(DataTy::Dead(Box::new(dty.clone())))),
                Mutability::Mut,
            );
            let ty_ctx_with_ident = ty_ctx.append_ident_typed(ident_with_ty);
            Ok((
                ty_ctx_with_ident,
                Ty::new(TyKind::Data(DataTy::Scalar(ScalarTy::Unit))),
            ))
        } else {
            Err(TyError::MutabilityNotAllowed(ty.clone()))
        }
    }

    fn ty_check_seq(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        es: &mut [Expr],
    ) -> TyResult<(TyCtx, Ty)> {
        let mut ty_ctx = ty_ctx;
        for e in &mut *es {
            ty_ctx = self
                .ty_check_expr(kind_ctx, ty_ctx, exec, e)?
                .garbage_collect_loans();
        }
        Ok((ty_ctx, es.last().unwrap().ty.as_ref().unwrap().clone()))
    }

    fn ty_check_pl_expr_with_deref(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        pl_expr: &PlaceExpr,
    ) -> TyResult<(TyCtx, Ty)> {
        // TODO refactor
        borrow_check::ownership_safe(self, kind_ctx, &ty_ctx, exec, &[], Ownership::Shrd, pl_expr)
            .map_err(|err| {
                TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Shrd, err)
            })?;
        let ty =
            self.place_expr_ty_under_exec_own(kind_ctx, &ty_ctx, exec, Ownership::Shrd, pl_expr)?;
        if !ty.is_fully_alive() {
            return Err(TyError::String(format!(
                "Part of Place {:?} was moved before.",
                pl_expr
            )));
        }
        if ty.copyable() {
            Ok((ty_ctx, ty))
        } else {
            Err(TyError::String("Data type is not copyable.".to_string()))
        }
    }

    fn ty_check_pl_expr_without_deref(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        pl_expr: &PlaceExpr,
    ) -> TyResult<(TyCtx, Ty)> {
        let place = pl_expr.to_place().unwrap();
        // If place is an identifier referring to a globally declared function
        let (res_ty_ctx, pl_ty) = if let Ok(fun_ty) = self.gl_ctx.fun_ty_by_ident(&place.ident) {
            (ty_ctx, fun_ty.clone())
        } else {
            // If place is NOT referring to a globally declared function
            let pl_ty = ty_ctx.place_ty(&place)?;
            if !pl_ty.is_fully_alive() {
                return Err(TyError::String(format!(
                    "Part of Place {:?} was moved before.",
                    pl_expr
                )));
            }
            let res_ty_ctx = if pl_ty.copyable() {
                // TODO refactor
                borrow_check::ownership_safe(
                    self,
                    kind_ctx,
                    &ty_ctx,
                    exec,
                    &[],
                    Ownership::Shrd,
                    pl_expr,
                )
                .map_err(|err| {
                    TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Shrd, err)
                })?;
                ty_ctx
            } else {
                borrow_check::ownership_safe(
                    self,
                    kind_ctx,
                    &ty_ctx,
                    exec,
                    &[],
                    Ownership::Uniq,
                    pl_expr,
                )
                .map_err(|err| {
                    TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Uniq, err)
                })?;
                ty_ctx.kill_place(&place)
            };
            (res_ty_ctx, pl_ty)
        };

        Ok((res_ty_ctx, pl_ty))
    }

    fn ty_check_borrow(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        exec: Exec,
        prv: &Provenance,
        own: Ownership,
        pl_expr: &mut PlaceExpr,
    ) -> TyResult<(TyCtx, Ty)> {
        if let Some(place) = pl_expr.to_place() {
            if own == Ownership::Uniq && ty_ctx.ident_ty(&place.ident)?.mutbl == Mutability::Const {
                return Err(TyError::ConstBorrow(pl_expr.clone()));
            }
        }

        let prv_val_name = match prv {
            Provenance::Value(prv_val_name) => prv_val_name,
            Provenance::Ident(_) => {
                return Err(TyError::String(format!(
                    "Cannot borrow using a provenance variable {:?}.",
                    prv
                )));
            }
        };

        if !ty_ctx.loans_for_prv(prv_val_name)?.is_empty() {
            return Err(TyError::PrvValueAlreadyInUse(prv_val_name.clone()));
        }
        let loans = borrow_check::ownership_safe(self, kind_ctx, &ty_ctx, exec, &[], own, pl_expr)
            .map_err(|err| TyError::ConflictingBorrow(Box::new(pl_expr.clone()), own, err))?;
        let (ty, mem) =
            self.place_expr_ty_mem_under_exec_own(kind_ctx, &ty_ctx, exec, own, pl_expr)?;
        if !ty.is_fully_alive() {
            return Err(TyError::String(
                "The place was at least partially moved before.".to_string(),
            ));
        }
        let (reffed_ty, rmem) = match &ty.ty {
            TyKind::Data(DataTy::Dead(_)) => panic!("Cannot happen because of the alive check."),
            TyKind::Data(DataTy::At(inner_ty, m)) => (inner_ty.deref().clone(), m.clone()),
            TyKind::Data(dty) => (
                dty.clone(),
                match mem {
                    Some(m) => m,
                    None => {
                        return Err(TyError::String(
                            "Trying to borrow value that does not exist for the current \
            execution resource."
                                .to_string(),
                        ))
                    }
                },
            ),
            TyKind::View(_) => return Err(TyError::String("Trying to borrow a view.".to_string())),
            TyKind::ThreadHierchy(_) => {
                return Err(TyError::String(
                    "Trying to borrow thread hierarchy.".to_string(),
                ))
            }
            TyKind::Fn(_, _, _, _) => {
                return Err(TyError::String("Trying to borrow a function.".to_string()))
            }
            TyKind::Ident(_) => {
                return Err(TyError::String(
                    "Borrowing from value of unspecified type. This could be a view.\
            Therefore it is not allowed to borrow."
                        .to_string(),
                ))
            }
        };
        let res_ty = DataTy::Ref(
            Provenance::Value(prv_val_name.to_string()),
            own,
            rmem,
            Box::new(reffed_ty),
        );
        let res_ty_ctx = ty_ctx.extend_loans_for_prv(prv_val_name, loans)?;
        Ok((res_ty_ctx, Ty::new(TyKind::Data(res_ty))))
    }

    // Δ; Γ ⊢ω p:τ
    // p in an ω context has type τ under Δ and Γ
    fn place_expr_ty_under_exec_own(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        exec: Exec,
        own: Ownership,
        pl_expr: &PlaceExpr,
    ) -> TyResult<Ty> {
        let (ty, _) =
            self.place_expr_ty_mem_under_exec_own(kind_ctx, ty_ctx, exec, own, pl_expr)?;
        Ok(ty)
    }

    fn place_expr_ty_mem_under_exec_own(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        exec: Exec,
        own: Ownership,
        pl_expr: &PlaceExpr,
    ) -> TyResult<(Ty, Option<Memory>)> {
        let (ty, mem, _) = self
            .place_expr_ty_mem_passed_prvs_under_exec_own(kind_ctx, ty_ctx, exec, own, pl_expr)?;
        Ok((ty, mem))
    }

    // Δ; Γ ⊢ω p:τ,{ρ}
    // p in an ω context has type τ under Δ and Γ, passing through provenances in Vec<ρ>
    fn place_expr_ty_mem_passed_prvs_under_exec_own(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        exec: Exec,
        own: Ownership,
        pl_expr: &PlaceExpr,
    ) -> TyResult<(Ty, Option<Memory>, Vec<Provenance>)> {
        match &pl_expr.pl_expr {
            // TC-Var
            PlaceExprKind::Ident(ident) => {
                self.var_expr_ty_mem_empty_prvs_under_exec_own(ty_ctx, exec, &ident)
            }
            // TC-Proj
            PlaceExprKind::Proj(tuple_expr, n) => self.proj_expr_ty_mem_passed_prvs_under_exec_own(
                kind_ctx, ty_ctx, exec, own, tuple_expr, *n,
            ),
            // TC-Deref
            PlaceExprKind::Deref(borr_expr) => self.deref_expr_ty_mem_passed_prvs_under_exec_own(
                kind_ctx, ty_ctx, exec, own, borr_expr,
            ),
        }
    }

    fn var_expr_ty_mem_empty_prvs_under_exec_own(
        &self,
        ty_ctx: &TyCtx,
        exec: Exec,
        ident: &Ident,
    ) -> TyResult<(Ty, Option<Memory>, Vec<Provenance>)> {
        let ty = if let Ok(tty) = ty_ctx.ty_of_ident(&ident) {
            tty
        } else {
            self.gl_ctx.fun_ty_by_ident(&ident)?
        };

        match &ty.ty {
            TyKind::Data(dty) => {
                if !dty.is_fully_alive() {
                    return Err(TyError::String(format!(
                        "The value in this identifier `{}` has been moved out.",
                        ident
                    )));
                }
                let mem = Self::default_mem_by_exec(exec);
                Ok((ty.clone(), mem, vec![]))
            }
            TyKind::View(vty) => {
                if !vty.is_fully_alive() {
                    return Err(TyError::String(
                        "The value in this identifier has been moved out.".to_string(),
                    ));
                }
                Ok((ty.clone(), None, vec![]))
            }
            TyKind::ThreadHierchy(_) => Ok((ty.clone(), None, vec![])),
            TyKind::Fn(_, _, _, _) => {
                if !ty.is_fully_alive() {
                    panic!("This should never happen.")
                }
                Ok((ty.clone(), None, vec![]))
            }
            // TODO this is probably wrong, should probably succeed instead
            //  but not in all cases. as long as these functions return the accessed memory region,
            //  the type MUST be known to do so.
            TyKind::Ident(ident) => {
                panic!("Identifier {} found. Expected instantiated type.", ident)
            }
        }
    }

    fn default_mem_by_exec(exec: Exec) -> Option<Memory> {
        match exec {
            Exec::CpuThread => Some(Memory::CpuStack),
            Exec::GpuThread => Some(Memory::GpuLocal),
            Exec::GpuGrid | Exec::GpuBlock | Exec::GpuWarp | Exec::View => None,
        }
    }

    fn proj_expr_ty_mem_passed_prvs_under_exec_own(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        exec: Exec,
        own: Ownership,
        tuple_expr: &PlaceExpr,
        n: usize,
    ) -> TyResult<(Ty, Option<Memory>, Vec<Provenance>)> {
        let (pl_expr_ty, mem, passed_prvs) = self.place_expr_ty_mem_passed_prvs_under_exec_own(
            kind_ctx, ty_ctx, exec, own, tuple_expr,
        )?;
        match &pl_expr_ty.ty {
            TyKind::Data(DataTy::Tuple(elem_dtys)) => {
                if let Some(ty) = elem_dtys.get(n) {
                    Ok((Ty::new(TyKind::Data(ty.clone())), mem, passed_prvs))
                } else {
                    Err(TyError::String(
                        "Trying to access non existing tuple element.".to_string(),
                    ))
                }
            }
            TyKind::View(ViewTy::Tuple(elem_tys)) => {
                if let Some(ty) = elem_tys.get(n) {
                    let mem = if let TyKind::Data(_) = &ty.ty {
                        Self::default_mem_by_exec(exec)
                    } else {
                        None
                    };
                    Ok((ty.clone(), mem, passed_prvs))
                } else {
                    Err(TyError::String(
                        "Trying to access non existing tuple element.".to_string(),
                    ))
                }
            }
            TyKind::Ident(_) => Err(TyError::String(
                "Type unspecified. Cannot project from potentially non tuple type.".to_string(),
            )),
            _ => Err(TyError::String(
                "Trying to project from non tuple value.".to_string(),
            )),
        }
    }

    fn deref_expr_ty_mem_passed_prvs_under_exec_own(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        exec: Exec,
        own: Ownership,
        borr_expr: &PlaceExpr,
    ) -> TyResult<(Ty, Option<Memory>, Vec<Provenance>)> {
        let (pl_expr_ty, _, mut passed_prvs) = self
            .place_expr_ty_mem_passed_prvs_under_exec_own(kind_ctx, ty_ctx, exec, own, borr_expr)?;
        if let TyKind::Data(DataTy::Ref(prv, ref_own, mem, dty)) = pl_expr_ty.ty {
            if ref_own < own {
                return Err(TyError::String(
                    "Trying to dereference and mutably use a shrd reference.".to_string(),
                ));
            }
            let outl_rels = passed_prvs.iter().map(|passed_prv| (&prv, passed_prv));
            subty::multiple_outlives(kind_ctx, ty_ctx.clone(), outl_rels)?;
            Self::accessible_memory(exec, &mem)?;
            passed_prvs.push(prv);
            Ok((Ty::new(TyKind::Data(*dty)), Some(mem), passed_prvs))
        } else {
            Err(TyError::String(
                "Trying to dereference non reference type.".to_string(),
            ))
        }
    }

    fn accessible_memory(exec: Exec, mem: &Memory) -> TyResult<()> {
        let gpu_exec_to_mem = vec![
            (Exec::CpuThread, Memory::CpuStack),
            (Exec::CpuThread, Memory::CpuHeap),
            (Exec::GpuThread, Memory::GpuGlobal),
            (Exec::GpuThread, Memory::GpuShared),
        ];

        if gpu_exec_to_mem.contains(&(exec, mem.clone())) {
            Ok(())
        } else {
            Err(TyError::String(format!(
                "Trying to dereference pointer to `{}` from execution resource `{}`",
                mem, exec
            )))
        }
    }

    // TODO respect memory
    fn ty_well_formed(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        exec: Exec,
        ty: &Ty,
    ) -> TyResult<()> {
        match &ty.ty {
            TyKind::Data(dty) => match dty {
                // TODO variables of Dead types can be reassigned. So why do we not have to check
                //  well-formedness of the type in Dead(ty)? (According paper).
                DataTy::Scalar(_) | DataTy::Atomic(_) | DataTy::Dead(_) => {}
                DataTy::Ident(ident) => {
                    if !kind_ctx.ident_of_kind_exists(ident, Kind::Ty) {
                        Err(CtxError::KindedIdentNotFound(ident.clone()))?
                    }
                }
                DataTy::Ref(Provenance::Value(prv), own, mem, dty) => {
                    let elem_ty = Ty::new(TyKind::Data(dty.as_ref().clone()));
                    if !elem_ty.is_fully_alive() {
                        return Err(TyError::ReferenceToDeadTy);
                    }
                    let loans = ty_ctx.loans_for_prv(prv)?;
                    if !loans.is_empty() {
                        let mut exists = false;
                        for loan in loans {
                            let Loan {
                                place_expr,
                                own: l_own,
                            } = loan;
                            if l_own != own {
                                return Err(TyError::ReferenceToWrongOwnership);
                            }
                            if let TyKind::Data(pl_expr_dty) = self
                                .place_expr_ty_under_exec_own(
                                    kind_ctx, ty_ctx, exec, *l_own, place_expr,
                                )?
                                .ty
                            {
                                if !pl_expr_dty.is_fully_alive() {
                                    return Err(TyError::ReferenceToDeadTy);
                                }
                                if dty.occurs_in(&pl_expr_dty) {
                                    exists = true;
                                    break;
                                }
                            }
                        }
                        if !exists {
                            return Err(TyError::ReferenceToIncompatibleType);
                        }
                    }
                    self.ty_well_formed(kind_ctx, ty_ctx, exec, &elem_ty)?;
                }
                DataTy::Ref(Provenance::Ident(ident), _, mem, dty) => {
                    let elem_ty = Ty::new(TyKind::Data(dty.as_ref().clone()));
                    if !kind_ctx.ident_of_kind_exists(ident, Kind::Provenance) {
                        Err(CtxError::KindedIdentNotFound(ident.clone()))?
                    }
                    self.ty_well_formed(kind_ctx, ty_ctx, exec, &elem_ty)?;
                }
                DataTy::Tuple(elem_dtys) => {
                    for elem_dty in elem_dtys {
                        self.ty_well_formed(
                            kind_ctx,
                            ty_ctx,
                            exec,
                            &Ty::new(TyKind::Data(elem_dty.clone())),
                        )?;
                    }
                }
                DataTy::Array(elem_dty, n) => {
                    self.ty_well_formed(
                        kind_ctx,
                        ty_ctx,
                        exec,
                        &Ty::new(TyKind::Data(elem_dty.as_ref().clone())),
                    )?;
                    // TODO well-formed nat
                }
                DataTy::At(elem_dty, Memory::Ident(ident)) => {
                    if !kind_ctx.ident_of_kind_exists(ident, Kind::Memory) {
                        Err(TyError::CtxError(CtxError::KindedIdentNotFound(
                            ident.clone(),
                        )))?;
                    }
                    self.ty_well_formed(
                        kind_ctx,
                        ty_ctx,
                        exec,
                        &Ty::new(TyKind::Data(elem_dty.as_ref().clone())),
                    )?;
                }
                DataTy::At(elem_dty, _) => {
                    self.ty_well_formed(
                        kind_ctx,
                        ty_ctx,
                        exec,
                        &Ty::new(TyKind::Data(elem_dty.as_ref().clone())),
                    )?;
                }
            },
            TyKind::Ident(ident) => {
                if !kind_ctx.ident_of_kind_exists(ident, Kind::Ty) {
                    Err(CtxError::KindedIdentNotFound(ident.clone()))?
                }
            }
            TyKind::ThreadHierchy(th_hierchy) => {} // TODO check well-formedness of Nats
            TyKind::View(view_ty) => match view_ty {
                // TODO check well-formedness of Nats
                ViewTy::Tuple(elem_tys) => {
                    for elem_ty in elem_tys {
                        self.ty_well_formed(kind_ctx, ty_ctx, exec, elem_ty)?;
                    }
                }
                ViewTy::Array(elem_ty, nat) => {
                    self.ty_well_formed(kind_ctx, ty_ctx, exec, elem_ty)?
                }
                ViewTy::Dead(_) => {}
            },
            TyKind::Fn(idents_kinded, param_tys, exec, ret_ty) => {
                let extended_kind_ctx = kind_ctx.clone().append_idents(idents_kinded.clone());
                self.ty_well_formed(&extended_kind_ctx, ty_ctx, *exec, ret_ty)?;
                for param_ty in param_tys {
                    self.ty_well_formed(&extended_kind_ctx, ty_ctx, *exec, param_ty)?;
                }
            }
        }
        Ok(())
    }
}
