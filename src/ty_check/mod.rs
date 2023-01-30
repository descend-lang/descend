mod borrow_check;
mod ctxs;
mod error;
mod infer_kinded_args;
pub mod pre_decl;
mod subty;
mod unify;

use crate::ast::internal::{FrameEntry, IdentTyped, Loan, Place, PrvMapping};
use crate::ast::utils;
use crate::ast::*;
use crate::error::ErrorReported;
use ctxs::{ExecBorrowCtx, GlobalCtx, KindCtx, TyCtx};
use error::*;
use std::collections::HashSet;
use std::ops::Deref;

type TyResult<T> = Result<T, TyError>;

macro_rules! matches_dty {
    ($ty: expr, $dty_pat: pat_param) => {
        if let crate::ast::TyKind::Data(d) = &$ty.ty {
            matches!(d.as_ref(), $dty_pat)
        } else {
            false
        }
    };
}
pub(crate) use matches_dty;

// ∀ε ∈ Σ. Σ ⊢ ε
// --------------
//      ⊢ Σ
pub fn ty_check(compil_unit: &mut CompilUnit) -> Result<(), ErrorReported> {
    let compil_unit_clone = compil_unit.clone();
    let mut ty_checker = TyChecker::new(&compil_unit_clone);
    ty_checker.ty_check(compil_unit).map_err(|err| {
        err.emit(compil_unit.source);
        ErrorReported
    })
}

struct TyChecker {
    gl_ctx: GlobalCtx,
    exec_borrow_ctx: ExecBorrowCtx,
}

impl TyChecker {
    pub fn new(compil_unit: &CompilUnit) -> Self {
        let gl_ctx = GlobalCtx::new()
            .append_from_fun_defs(&compil_unit.fun_defs)
            .append_fun_decls(&pre_decl::fun_decls());
        TyChecker {
            gl_ctx,
            exec_borrow_ctx: ExecBorrowCtx::new(),
        }
    }

    fn ty_check(&mut self, compil_unit: &mut CompilUnit) -> TyResult<()> {
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
    fn ty_check_global_fun_def(&mut self, gf: &mut FunDef) -> TyResult<()> {
        self.exec_borrow_ctx = ExecBorrowCtx::new();
        let kind_ctx = KindCtx::from(gf.generic_params.clone(), gf.prv_rels.clone())?;

        // TODO check that every prv_rel only uses provenance variables bound in generic_params
        // Build frame typing for this function
        let glf_frame = internal::append_idents_typed(
            &vec![],
            gf.param_decls
                .iter()
                .map(|ParamDecl { ident, ty, mutbl }| IdentTyped {
                    ident: ident.clone(),
                    ty: ty.as_ref().unwrap().clone(),
                    mutbl: *mutbl,
                    exec: ExecExpr::new(Exec::new(BaseExec::Ident(gf.exec_decl.ident.clone()))),
                })
                .collect(),
        );
        let mut exec_borrow_ctx = ExecBorrowCtx::new();
        let ty_ctx = TyCtx::from(glf_frame);

        let mut exec = ExecExpr::new(Exec::new(BaseExec::Ident(gf.exec_decl.ident.clone())));
        ty_check_exec(&kind_ctx, &ty_ctx, &gf.exec_decl, &mut exec)?;
        let mut ty_ctx = ty_ctx.append_exec_mapping(gf.exec_decl.ident.clone(), exec.clone());
        for prv in &gf.body.prvs {
            ty_ctx = ty_ctx.append_prv_mapping(PrvMapping::new(prv))
        }
        self.ty_check_expr(
            &kind_ctx,
            &mut exec_borrow_ctx,
            ty_ctx,
            &gf.exec_decl,
            &exec,
            &mut gf.body.body,
        )?;

        // t <= t_f
        // unify::constrain(
        //     gf.body_expr.ty.as_ref().unwrap(),
        //     &Ty::new(TyKind::Data(gf.ret_dty.clone())),
        // )?;

        //coalesce::coalesce_ty(&mut self.term_constr.constr_map, &mut body_ctx, )
        let empty_ty_ctx = subty::check(
            &kind_ctx,
            TyCtx::new(),
            gf.body.body.ty.as_ref().unwrap().dty(),
            &gf.ret_dty,
        )?;

        // TODO there should never exist implicit regions either. They are created during parsing and
        //  never removed. Problem with unification? Problem with region rewriting?! Compare to Oxide.
        #[cfg(debug_assertions)]
        if let Some(hm) = utils::implicit_idents_without_rgns(gf) {
            panic!("Implicit Idents:\n{:?}", hm)
        }

        //TODO why is this the case?
        debug_assert!(
            empty_ty_ctx.is_empty(),
            "Expected typing context to be empty. But TyCtx:\n {:?}",
            empty_ty_ctx
        );

        Ok(())
    }

    // e has type τ under Σ, Δ, and Γ, producing output context Γ'
    // sideconditions: Global Function Context Σ, Kinding context Δ and typing context are well-formed and
    //   type τ is well-formed under well-formed GlFunCtxt, kinding ctx, output context Γ'.
    // Σ; Δ; Γ ⊢ e :^exec τ ⇒ Γ′, side conditions:  ⊢ Σ;Δ;Γ and Σ;Δ;Γ′ ⊢ τ
    // This never returns a dead type, because typing an expression with a dead type is not possible.
    fn ty_check_expr(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        expr: &mut Expr,
    ) -> TyResult<TyCtx> {
        // TODO input contexts are well-formed
        //   well_formed_ctxs(gl_ctx, kind_ctx, &ty_ctx);
        let (res_ty_ctx, ty) = match &mut expr.expr {
            ExprKind::PlaceExpr(pl_expr) => {
                if pl_expr.is_place() {
                    self.ty_check_pl_expr_without_deref(
                        kind_ctx,
                        exec_borrow_ctx,
                        ty_ctx,
                        ident_exec,
                        exec,
                        pl_expr,
                    )?
                } else {
                    self.ty_check_pl_expr_with_deref(
                        kind_ctx,
                        exec_borrow_ctx,
                        ty_ctx,
                        ident_exec,
                        exec,
                        pl_expr,
                    )?
                }
            }
            ExprKind::Block(block) => {
                self.ty_check_block(kind_ctx, exec_borrow_ctx, ty_ctx, ident_exec, exec, block)?
            }
            ExprKind::Let(pattern, ty, e) => self.ty_check_let(
                kind_ctx,
                exec_borrow_ctx,
                ty_ctx,
                ident_exec,
                exec,
                pattern,
                ty,
                e,
            )?,
            ExprKind::LetUninit(ident, ty) => {
                Self::ty_check_let_uninit(ty_ctx, exec_borrow_ctx, ident_exec, exec, ident, ty)?
            }
            ExprKind::Seq(es) => {
                self.ty_check_seq(kind_ctx, exec_borrow_ctx, ty_ctx, ident_exec, exec, es)?
            }
            ExprKind::Lit(l) => Self::ty_check_literal(ty_ctx, l),
            ExprKind::Array(elems) => {
                self.ty_check_array(kind_ctx, exec_borrow_ctx, ty_ctx, ident_exec, exec, elems)?
            }
            ExprKind::Tuple(elems) => {
                self.ty_check_tuple(kind_ctx, exec_borrow_ctx, ty_ctx, ident_exec, exec, elems)?
            }
            ExprKind::Proj(e, i) => {
                self.ty_check_proj(kind_ctx, exec_borrow_ctx, ty_ctx, ident_exec, exec, e, *i)?
            }
            ExprKind::App(ef, k_args, args) => self.ty_check_app(
                kind_ctx,
                exec_borrow_ctx,
                ty_ctx,
                ident_exec,
                exec,
                ef,
                k_args,
                args,
            )?,
            ExprKind::DepApp(ef, k_args) => {
                let (ty_ctx, _, _, _, fun_ty) = self.ty_check_dep_app(
                    kind_ctx,
                    exec_borrow_ctx,
                    ty_ctx,
                    ident_exec,
                    exec,
                    ef,
                    k_args,
                )?;
                (ty_ctx, fun_ty)
            }
            ExprKind::AppKernel(app_kernel) => self.ty_check_app_kernel(
                kind_ctx,
                exec_borrow_ctx,
                ty_ctx,
                ident_exec,
                exec,
                app_kernel,
            )?,
            ExprKind::Ref(prv, own, pl_expr) => self.ty_check_borrow(
                kind_ctx,
                exec_borrow_ctx,
                ty_ctx,
                ident_exec,
                exec,
                prv,
                *own,
                pl_expr,
            )?,
            ExprKind::Index(pl_expr, index) => self.ty_check_index_copy(
                kind_ctx,
                exec_borrow_ctx,
                ty_ctx,
                ident_exec,
                exec,
                pl_expr,
                index,
            )?,
            ExprKind::Assign(pl_expr, e) => {
                if pl_expr.is_place() {
                    self.ty_check_assign_place(
                        kind_ctx,
                        exec_borrow_ctx,
                        ty_ctx,
                        ident_exec,
                        exec,
                        &pl_expr,
                        e,
                    )?
                } else {
                    self.ty_check_assign_deref(
                        kind_ctx,
                        exec_borrow_ctx,
                        ty_ctx,
                        ident_exec,
                        exec,
                        pl_expr,
                        e,
                    )?
                }
            }
            ExprKind::IdxAssign(pl_expr, idx, e) => self.ty_check_idx_assign(
                kind_ctx,
                exec_borrow_ctx,
                ty_ctx,
                ident_exec,
                exec,
                pl_expr,
                idx,
                e,
            )?,
            ExprKind::Indep(indep) => {
                self.ty_check_indep(kind_ctx, exec_borrow_ctx, ty_ctx, ident_exec, exec, indep)?
            }
            ExprKind::Sched(sched) => {
                self.ty_check_sched(kind_ctx, exec_borrow_ctx, ty_ctx, ident_exec, exec, sched)?
            }
            ExprKind::Select(r, p, distrib_exec) => self.ty_check_select(
                kind_ctx,
                exec_borrow_ctx,
                ty_ctx,
                ident_exec,
                exec,
                r,
                p,
                distrib_exec,
            )?,
            ExprKind::ForNat(var, range, body) => self.ty_check_for_nat(
                kind_ctx,
                exec_borrow_ctx,
                ty_ctx,
                ident_exec,
                exec,
                var,
                range,
                body,
            )?,
            ExprKind::For(ident, collec, body) => self.ty_check_for(
                kind_ctx,
                exec_borrow_ctx,
                ty_ctx,
                ident_exec,
                exec,
                ident,
                collec,
                body,
            )?,
            ExprKind::IfElse(cond, case_true, case_false) => self.ty_check_if_else(
                kind_ctx,
                exec_borrow_ctx,
                ty_ctx,
                ident_exec,
                exec,
                cond,
                case_true,
                case_false,
            )?,
            ExprKind::If(cond, case_true) => self.ty_check_if(
                kind_ctx,
                exec_borrow_ctx,
                ty_ctx,
                ident_exec,
                exec,
                cond,
                case_true,
            )?,
            ExprKind::While(cond, body) => self.ty_check_while(
                kind_ctx,
                exec_borrow_ctx,
                ty_ctx,
                ident_exec,
                exec,
                cond,
                body,
            )?,
            ExprKind::Lambda(params, lambda_exec_ident, ret_ty, body) => {
                self.ty_check_lambda(kind_ctx, ty_ctx, params, lambda_exec_ident, ret_ty, body)?
            }
            ExprKind::BinOp(bin_op, lhs, rhs) => self.ty_check_binary_op(
                kind_ctx,
                exec_borrow_ctx,
                ty_ctx,
                ident_exec,
                exec,
                bin_op,
                lhs,
                rhs,
            )?,
            ExprKind::UnOp(un_op, e) => self.ty_check_unary_op(
                kind_ctx,
                exec_borrow_ctx,
                ty_ctx,
                ident_exec,
                exec,
                un_op,
                e,
            )?,
            ExprKind::Split(expr_split) => self.ty_check_split(
                kind_ctx,
                exec_borrow_ctx,
                ty_ctx,
                ident_exec,
                exec,
                &mut expr_split.lrgn,
                &mut expr_split.rrgn,
                expr_split.own,
                &mut expr_split.pos,
                &mut expr_split.view,
            )?,
            ExprKind::Sync => {
                //TODO implement
                (
                    ty_ctx,
                    Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                        ScalarTy::Unit,
                    ))))),
                )
            }
            ExprKind::Range(l, u) => {
                self.ty_check_range(kind_ctx, exec_borrow_ctx, ty_ctx, ident_exec, exec, l, u)?
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

        // TODO reintroduce!!!!
        //if let Err(err) = self.ty_well_formed(kind_ctx, &res_ty_ctx, exec, &ty) {
        //    panic!("{:?}", err);
        //}
        expr.ty = Some(Box::new(ty));
        Ok(res_ty_ctx)
    }

    fn ty_check_range(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        l: &mut Expr,
        u: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        if &ident_exec.ty.ty != &ExecTyKind::CpuThread
            && &ident_exec.ty.ty != &ExecTyKind::GpuThread
        {
            return Err(TyError::IllegalExec);
        }

        let ty_ctx_l =
            self.ty_check_expr(kind_ctx, exec_borrow_ctx, ty_ctx, ident_exec, exec, l)?;
        let ty_ctx_u =
            self.ty_check_expr(kind_ctx, exec_borrow_ctx, ty_ctx_l, ident_exec, exec, u)?;

        if !matches_dty!(
            l.ty.as_ref().unwrap(),
            DataTy {
                dty: DataTyKind::Scalar(ScalarTy::I32),
                ..
            }
        ) {
            panic!("expected i32 for l in range")
        }

        if !matches_dty!(
            &u.ty.as_ref().unwrap(),
            DataTy {
                dty: DataTyKind::Scalar(ScalarTy::I32),
                ..
            }
        ) {
            panic!("expected i32 for u in range")
        }

        Ok((
            ty_ctx_u,
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Range)))),
        ))
    }

    fn ty_check_split(
        &self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        r1: &Option<String>,
        r2: &Option<String>,
        own: Ownership,
        s: &Nat,
        view: &mut PlaceExpr,
    ) -> TyResult<(TyCtx, Ty)> {
        fn tag_loans(loans: &HashSet<Loan>, tag: SplitTag) -> HashSet<Loan> {
            loans
                .iter()
                .cloned()
                .map(|mut l| {
                    l.place_expr.split_tag_path.push(tag);
                    l
                })
                .collect()
        }
        fn split_loans(loans: HashSet<Loan>) -> (HashSet<Loan>, HashSet<Loan>) {
            let fst = tag_loans(&loans, SplitTag::Fst);
            let snd = tag_loans(&loans, SplitTag::Snd);
            (fst, snd)
        }

        let (ty_ctx_prv1, prv1) = TyChecker::infer_prv(ty_ctx.clone(), r1);
        let (ty_ctx_prv1_prv2, prv2) = TyChecker::infer_prv(ty_ctx_prv1, r2);
        if !(ty_ctx_prv1_prv2.loans_in_prv(&prv1)?.is_empty()) {
            return Err(TyError::PrvValueAlreadyInUse(prv1));
        }
        if !(ty_ctx_prv1_prv2.loans_in_prv(&prv2)?.is_empty()) {
            return Err(TyError::PrvValueAlreadyInUse(prv2));
        }

        let mems =
            self.place_expr_ty_mems_under_exec_own(kind_ctx, &ty_ctx_prv1_prv2, exec, own, view)?;

        let split_ty = if let TyKind::Data(dty) = &view.ty.as_ref().unwrap().ty {
            if let DataTyKind::ArrayShape(elem_dty, n) = &dty.dty {
                if s > n {
                    return Err(TyError::String(
                        "Trying to access array out-of-bounds.".to_string(),
                    ));
                }

                let mem = if let Some(mem) = mems.last() {
                    mem
                } else {
                    panic!("An array view must always reside in memory.")
                };

                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Tuple(
                    vec![
                        DataTy::new(DataTyKind::Ref(Box::new(RefDty::new(
                            Provenance::Value(prv1.clone()),
                            own,
                            mem.clone(),
                            DataTy::new(DataTyKind::ArrayShape(elem_dty.clone(), s.clone())),
                        )))),
                        DataTy::new(DataTyKind::Ref(Box::new(RefDty::new(
                            Provenance::Value(prv2.clone()),
                            own,
                            mem.clone(),
                            DataTy::new(DataTyKind::ArrayShape(
                                elem_dty.clone(),
                                Nat::BinOp(BinOpNat::Sub, Box::new(n.clone()), Box::new(s.clone())),
                            )),
                        )))),
                    ],
                )))))
            } else {
                return Err(TyError::UnexpectedType);
            }
        } else {
            return Err(TyError::UnexpectedType);
        };

        let loans = borrow_check::ownership_safe(
            self,
            kind_ctx,
            exec_borrow_ctx,
            &ty_ctx_prv1_prv2,
            exec,
            &[],
            own,
            &view.clone(),
        )
        .map_err(|err| TyError::ConflictingBorrow(Box::new(view.clone()), Ownership::Uniq, err))?;
        let (fst_loans, snd_loans) = split_loans(loans);
        let prv1_to_loans = PrvMapping {
            prv: prv1,
            loans: fst_loans,
        };
        let prv2_to_loans = PrvMapping {
            prv: prv2,
            loans: snd_loans,
        };
        let split_ty_ctx = ty_ctx_prv1_prv2
            .append_prv_mapping(prv1_to_loans)
            .append_prv_mapping(prv2_to_loans);

        Ok((split_ty_ctx, split_ty))
    }

    fn infer_prv(ty_ctx: TyCtx, prv_name: &Option<String>) -> (TyCtx, String) {
        let (ty_ctx_r1, r1) = if let Some(prv) = prv_name.as_ref() {
            (ty_ctx, prv.clone())
        } else {
            let name = utils::fresh_name("r");
            (ty_ctx.append_prv_mapping(PrvMapping::new(&name)), name)
        };
        (ty_ctx_r1, r1)
    }

    fn ty_check_for_nat(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        var: &Ident,
        range: &Nat,
        body: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        let scoped_kind_ctx: KindCtx = kind_ctx.clone().append_idents(vec![IdentKinded {
            ident: var.clone(),
            kind: Kind::Nat,
        }]);
        let ty_ctx_1 = self.ty_check_expr(
            &scoped_kind_ctx,
            exec_borrow_ctx,
            ty_ctx.clone().append_frame(vec![]),
            ident_exec,
            exec,
            body,
        )?;
        let ty_ctx_1_no_body = ty_ctx_1.drop_last_frame();
        if ty_ctx != ty_ctx_1_no_body {
            // let diff: Vec<_> = ty_ctx_1_no_body
            //     .prv_mappings()
            //     .filter(|new| ty_ctx.prv_mappings().any(|old| &old == new))
            //     .collect();
            // eprintln!("{:?}", diff);
            return Err(TyError::String(
                "Using a data type in loop that can only be used once.".to_string(),
            ));
        }
        Ok((
            ty_ctx,
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                ScalarTy::Unit,
            ))))),
        ))
    }

    fn ty_check_for(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        ident: &Ident,
        collec: &mut Expr,
        body: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        let collec_ty_ctx =
            self.ty_check_expr(kind_ctx, exec_borrow_ctx, ty_ctx, ident_exec, exec, collec)?;
        let collec_dty = if let TyKind::Data(collec_dty) = &collec.ty.as_ref().unwrap().ty {
            collec_dty.as_ref()
        } else {
            return Err(TyError::String(format!(
                "Expected array data type or reference to array data type, but found {:?}",
                collec.ty.as_ref().unwrap()
            )));
        };

        let ident_dty = match &collec_dty.dty {
            // TODO
            DataTyKind::Array(elem_dty, n) => unimplemented!(),
            DataTyKind::Ref(reff) => match &reff.dty.as_ref().dty {
                DataTyKind::Array(elem_dty, _) => DataTyKind::Ref(Box::new(RefDty::new(
                    reff.rgn.clone(),
                    reff.own,
                    reff.mem.clone(),
                    elem_dty.as_ref().clone(),
                ))),
                DataTyKind::ArrayShape(elem_dty, _) => DataTyKind::Ref(Box::new(RefDty::new(
                    reff.rgn.clone(),
                    reff.own,
                    reff.mem.clone(),
                    elem_dty.as_ref().clone(),
                ))),
                _ => {
                    return Err(TyError::String(format!(
                        "Expected reference to array data type, but found {:?}",
                        reff.dty.as_ref(),
                    )))
                }
            },
            DataTyKind::Range => DataTyKind::Scalar(ScalarTy::I32),
            _ => {
                return Err(TyError::String(format!(
                    "Expected array data type or reference to array data type, but found {:?}",
                    collec.ty.as_ref().unwrap()
                )));
            }
        };
        let collec_ty_ctx_with_ident =
            collec_ty_ctx
                .clone()
                .append_frame(vec![FrameEntry::Var(IdentTyped::new(
                    ident.clone(),
                    Ty::new(TyKind::Data(Box::new(DataTy::new(ident_dty)))),
                    Mutability::Const,
                    ExecExpr::new(Exec::new(BaseExec::Ident(ident_exec.ident.clone()))),
                ))]);
        let iter_ty_ctx = self.ty_check_expr(
            kind_ctx,
            exec_borrow_ctx,
            collec_ty_ctx_with_ident,
            ident_exec,
            exec,
            body,
        )?;
        let ty_ctx_no_body = iter_ty_ctx.drop_last_frame();
        if collec_ty_ctx != ty_ctx_no_body {
            return Err(TyError::String(
                "Using a data type in loop that can only be used once.".to_string(),
            ));
        }
        Ok((
            collec_ty_ctx,
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                ScalarTy::Unit,
            ))))),
        ))
    }

    fn ty_check_while(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        cond: &mut Expr,
        body: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        let cond_ty_ctx =
            self.ty_check_expr(kind_ctx, exec_borrow_ctx, ty_ctx, ident_exec, exec, cond)?;
        let body_ty_ctx = self.ty_check_expr(
            kind_ctx,
            exec_borrow_ctx,
            cond_ty_ctx.append_frame(vec![]),
            ident_exec,
            exec,
            body,
        )?;

        let body_outer_ty_ctx = body_ty_ctx.drop_last_frame();
        let cond_temp_ty_ctx = self.ty_check_expr(
            kind_ctx,
            exec_borrow_ctx,
            body_outer_ty_ctx.clone(),
            ident_exec,
            exec,
            cond,
        )?;
        if body_outer_ty_ctx != cond_temp_ty_ctx {
            return Err(TyError::String(
                "Context should have stayed the same".to_string(),
            ));
        }
        let body_temp_ty_ctx = self.ty_check_expr(
            kind_ctx,
            exec_borrow_ctx,
            body_outer_ty_ctx.clone().append_frame(vec![]),
            ident_exec,
            exec,
            body,
        )?;
        if body_outer_ty_ctx != body_temp_ty_ctx.drop_last_frame() {
            return Err(TyError::String(
                "Context should have stayed the same".to_string(),
            ));
        }

        let cond_ty = cond.ty.as_ref().unwrap();
        let body_ty = body.ty.as_ref().unwrap();

        if !matches_dty!(
            &cond_ty,
            DataTy {
                dty: DataTyKind::Scalar(ScalarTy::Bool),
                ..
            }
        ) {
            return Err(TyError::String(format!(
                "Expected condition in while loop, instead got {:?}",
                cond_ty
            )));
        }
        if !matches_dty!(
            &body_ty,
            DataTy {
                dty: DataTyKind::Scalar(ScalarTy::Unit),
                ..
            }
        ) {
            return Err(TyError::String(format!(
                "Body of while loop is not of unit type, instead got {:?}",
                body_ty
            )));
        }
        Ok((
            body_outer_ty_ctx,
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                ScalarTy::Unit,
            ))))),
        ))
    }

    fn ty_check_if_else(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        cond: &mut Expr,
        case_true: &mut Expr,
        case_false: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        // TODO deal with provenances in cases
        let cond_ty_ctx =
            self.ty_check_expr(kind_ctx, exec_borrow_ctx, ty_ctx, ident_exec, exec, cond)?;
        let _case_true_ty_ctx = self.ty_check_expr(
            kind_ctx,
            exec_borrow_ctx,
            cond_ty_ctx.clone(),
            ident_exec,
            exec,
            case_true,
        )?;
        let case_false_ty_ctx = self.ty_check_expr(
            kind_ctx,
            exec_borrow_ctx,
            cond_ty_ctx,
            ident_exec,
            exec,
            case_false,
        )?;

        let cond_ty = cond.ty.as_ref().unwrap();
        let case_true_ty = case_true.ty.as_ref().unwrap();
        let case_false_ty = case_false.ty.as_ref().unwrap();

        if !matches_dty!(
            &cond_ty,
            DataTy {
                dty: DataTyKind::Scalar(ScalarTy::Bool),
                ..
            }
        ) {
            return Err(TyError::String(format!(
                "Expected condition in if case, instead got {:?}",
                cond_ty
            )));
        }
        if !matches_dty!(
            &case_true_ty,
            DataTy {
                dty: DataTyKind::Scalar(ScalarTy::Unit),
                ..
            }
        ) {
            return Err(TyError::String(format!(
                "Body of the true case is not of unit type, instead got {:?}",
                case_true_ty
            )));
        }
        if !matches_dty!(
            &case_false_ty,
            DataTy {
                dty: DataTyKind::Scalar(ScalarTy::Unit),
                ..
            }
        ) {
            return Err(TyError::String(format!(
                "Body of the false case is not of unit type, instead got {:?}",
                case_false_ty
            )));
        }

        Ok((
            case_false_ty_ctx,
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                ScalarTy::Unit,
            ))))),
        ))
    }

    fn ty_check_if(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        cond: &mut Expr,
        case_true: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        // TODO deal with provenances in cases
        let cond_ty_ctx =
            self.ty_check_expr(kind_ctx, exec_borrow_ctx, ty_ctx, ident_exec, exec, cond)?;
        let case_true_ty_ctx = self.ty_check_expr(
            kind_ctx,
            exec_borrow_ctx,
            cond_ty_ctx.clone(),
            ident_exec,
            exec,
            case_true,
        )?;

        let cond_ty = cond.ty.as_ref().unwrap();
        let case_true_ty = case_true.ty.as_ref().unwrap();

        if !matches_dty!(
            &cond_ty,
            DataTy {
                dty: DataTyKind::Scalar(ScalarTy::Bool),
                ..
            }
        ) {
            return Err(TyError::String(format!(
                "Expected condition in if case, instead got {:?}",
                cond_ty
            )));
        }
        if !matches_dty!(
            &case_true_ty,
            DataTy {
                dty: DataTyKind::Scalar(ScalarTy::Unit),
                ..
            }
        ) {
            return Err(TyError::String(format!(
                "Body of the true case is not of unit type, instead got {:?}",
                case_true_ty
            )));
        }

        Ok((
            case_true_ty_ctx,
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                ScalarTy::Unit,
            ))))),
        ))
    }

    fn ty_check_indep(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        indep: &mut Indep,
    ) -> TyResult<(TyCtx, Ty)> {
        if exec != ty_ctx.get_exec_expr(&indep.split_exec_ident)? {
            return Err(TyError::String(format!(
                "illegal execution resource: {}",
                &indep.split_exec_ident
            )));
        }
        if indep.branch_idents.len() != indep.branch_bodies.len() {
            panic!(
                "Amount of branch identifiers and amount of branches do not match:\
                            {} and {}",
                indep.branch_idents.len(),
                indep.branch_bodies.len()
            );
        }
        if indep.branch_idents.len() != 2 {
            return Err(TyError::String(format!(
                "Expected 2 parallel branches but found {}",
                indep.branch_idents.len()
            )));
        }

        let mut indep_ctx = ty_ctx;
        for i in 0..indep.branch_bodies.len() {
            let mut branch_exec = ExecExpr::new(exec.exec.clone().split_proj(
                indep.dim_compo,
                indep.pos.clone(),
                i as u8,
            ));
            ty_check_exec(kind_ctx, &indep_ctx, ident_exec, &mut branch_exec)?;
            let branch_ty_ctx = indep_ctx
                .append_frame(vec![])
                .append_exec_mapping(indep.branch_idents[i].clone(), branch_exec.clone());
            let branch_res_ctx = self.ty_check_expr(
                kind_ctx,
                exec_borrow_ctx,
                branch_ty_ctx,
                &ident_exec,
                &branch_exec,
                &mut indep.branch_bodies[i],
            )?;
            if indep.branch_bodies[i].ty.as_ref().unwrap().ty
                != TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::Unit))))
            {
                return Err(TyError::String(
                    "A par_branch branch must not return a value.".to_string(),
                ));
            }
            indep_ctx = branch_res_ctx.drop_last_frame();
        }
        Ok((
            indep_ctx,
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                ScalarTy::Unit,
            ))))),
        ))
    }

    fn ty_check_sched(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        sched: &mut Sched,
    ) -> TyResult<(TyCtx, Ty)> {
        if exec != ty_ctx.get_exec_expr(&sched.sched_exec)? {
            return Err(TyError::String(format!(
                "illegal execution resource: {}",
                &sched.sched_exec
            )));
        }
        let mut body_exec = ExecExpr::new(exec.exec.clone().distrib(sched.dim));
        ty_check_exec(kind_ctx, &ty_ctx, ident_exec, &mut body_exec)?;
        let inner_ty_ctx = ty_ctx.clone().append_frame(vec![]);
        let mut inner_ty_ctx = if let Some(ident) = &sched.inner_exec_ident {
            inner_ty_ctx.append_exec_mapping(ident.clone(), body_exec.clone())
        } else {
            inner_ty_ctx
        };
        for prv in &sched.body.prvs {
            inner_ty_ctx = inner_ty_ctx.append_prv_mapping(PrvMapping::new(prv))
        }
        let body_ty_ctx = self.ty_check_expr(
            kind_ctx,
            exec_borrow_ctx,
            inner_ty_ctx,
            ident_exec,
            &body_exec,
            &mut sched.body.body,
        )?;
        let no_moves_ty_ctx = body_ty_ctx.drop_last_frame();
        if no_moves_ty_ctx != ty_ctx {
            return Err(TyError::String("A place from the outer scope was moved into `sched`. This breaks aliasing and is not allowed.".to_string()));
        }

        Ok((
            no_moves_ty_ctx,
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                ScalarTy::Unit,
            ))))),
        ))
    }

    // pub fn current_distrib_size(exec: &ExecExpr) -> Nat {
    //     match exec.exec.base {
    //         BaseExec::CpuThread => Err(TyError::String("it is impossible to select from view for a single CPU thread".to_string())),
    //         BaseExec::Ident(ident) => Err(TyError::String("cannot select from view; it is not specified how many execution resources {} are working in parallel".to_string())),
    //     }
    //     exec.exec.path.iter().rev().find_map(|&e| match e {
    //         ExecPathElem::Distrib(dim_compo) =>
    //             ExecPathElem::SplitProj(_) => None
    //     })
    // }

    fn ty_check_select(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        prv_val_name: &Option<String>,
        p: &mut PlaceExpr,
        distrib_ident: &Ident,
    ) -> TyResult<(TyCtx, Ty)> {
        let distrib_exec = ty_ctx.get_exec_expr(distrib_ident)?;
        if !exec.is_subexec_of(distrib_exec) {
            return Err(TyError::String(
                "Trying select memory for illegal excution resource.".to_string(),
            ));
        }

        self.place_expr_ty_under_exec_own(kind_ctx, &ty_ctx, exec, Ownership::Shrd, p)?;

        if let DataTyKind::Ref(ref_dty) = &p.ty.as_ref().unwrap().dty().dty {
            match &ref_dty.dty.dty {
                DataTyKind::Array(elem_dty, n) | DataTyKind::ArrayShape(elem_dty, n) => {
                    // TODO
                    // if n != distrib_exec.active_distrib_size() {
                    //     return Err(TyError::String("There must be as many elements in the view
                    //  as there exist execution resources that select from it.".to_string()));
                    // }
                    let (impl_ctx, prv_val_name) =
                        TyChecker::infer_prv(ty_ctx.clone(), prv_val_name);
                    if !impl_ctx.loans_in_prv(&prv_val_name)?.is_empty() {
                        return Err(TyError::PrvValueAlreadyInUse(prv_val_name.to_string()));
                    }
                    let loans = borrow_check::ownership_safe(
                        self,
                        kind_ctx,
                        exec_borrow_ctx,
                        &impl_ctx,
                        exec,
                        &[],
                        ref_dty.own,
                        p,
                    )
                    .map_err(|err| {
                        TyError::ConflictingBorrow(Box::new(p.clone()), ref_dty.own, err)
                    })?;
                    // TODO store_reborrow_for_exec(distrib_exec, p);
                    let res_dty = Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
                        Box::new(RefDty::new(
                            Provenance::Value(prv_val_name.clone()),
                            ref_dty.own,
                            ref_dty.mem.clone(),
                            elem_dty.as_ref().clone(),
                        )),
                    )))));
                    exec_borrow_ctx.insert(distrib_exec, loans.clone());
                    let res_ty_ctx = impl_ctx.extend_loans_for_prv(&prv_val_name, loans)?;
                    Ok((res_ty_ctx, res_dty))
                }
                _ => Err(TyError::String("Expected an array or view.".to_string())),
            }
        } else {
            Err(TyError::String(
                "Expected a reference to an array or view.".to_string(),
            ))
        }
    }

    fn type_input_idents(
        input_idents: &[Ident],
        input_exprs: &[Expr],
        body_exec_ident: &IdentExec,
    ) -> TyResult<Vec<IdentTyped>> {
        if input_idents.len() != input_exprs.len() {
            return Err(TyError::String(
                "Amount of input identifiers and input shapes do not match".to_string(),
            ));
        }

        input_exprs
            .iter()
            .map(|e| {
                if let TyKind::Data(dty) = &e.ty.as_ref().unwrap().ty {
                    if let DataTy {
                        dty: DataTyKind::Ref(reff),
                        ..
                    } = dty.as_ref()
                    {
                        if let DataTy {
                            dty: DataTyKind::ArrayShape(tty, n),
                            ..
                        } = reff.dty.as_ref()
                        {
                            Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
                                DataTyKind::Ref(Box::new(RefDty::new(
                                    reff.rgn.clone(),
                                    reff.own,
                                    reff.mem.clone(),
                                    tty.as_ref().clone(),
                                ))),
                            )))))
                        } else {
                            Err(TyError::UnexpectedType)
                        }
                    } else {
                        Err(TyError::UnexpectedType)
                    }
                } else {
                    Err(TyError::UnexpectedType)
                }
            })
            .zip(input_idents)
            .map(|(ty, i)| {
                Ok(IdentTyped::new(
                    i.clone(),
                    ty?,
                    Mutability::Const,
                    ExecExpr::new(Exec::new(BaseExec::Ident(body_exec_ident.ident.clone()))),
                ))
            })
            .collect::<TyResult<Vec<_>>>()
    }

    fn ty_check_lambda(
        &mut self,
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        params: &mut [ParamDecl],
        lambda_ident_exec: &IdentExec,
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
                    ty: match ty {
                        Some(tty) => tty.clone(),
                        None => Ty::new(TyKind::Data(Box::new(DataTy::new(utils::fresh_ident(
                            "param_ty",
                            DataTyKind::Ident,
                        ))))),
                    },
                    mutbl: *mutbl,
                    exec: ExecExpr::new(Exec::new(BaseExec::Ident(
                        lambda_ident_exec.ident.clone(),
                    ))),
                })
                .collect(),
        );
        // Copy porvenance mappings into scope and append scope frame.
        // FIXME check that no variables are captured.
        let fun_ty_ctx = ty_ctx.clone().append_frame(fun_frame);
        let mut body_exec =
            ExecExpr::new(Exec::new(BaseExec::Ident(lambda_ident_exec.ident.clone())));
        ty_check_exec(kind_ctx, &ty_ctx, lambda_ident_exec, &mut body_exec)?;
        let fun_ty_ctx_with_exec =
            fun_ty_ctx.append_exec_mapping(lambda_ident_exec.ident.clone(), body_exec.clone());
        let capture_ty_ctx = self.ty_check_expr(
            kind_ctx,
            &mut ExecBorrowCtx::new(),
            fun_ty_ctx_with_exec,
            lambda_ident_exec,
            &body_exec,
            body,
        )?;
        // FIXME reintroduce after introducing temporary typing context
        // let no_move_ty_ctx = capture_ty_ctx.clone().drop_last_frame();
        // if no_move_ty_ctx != ty_ctx {
        //     // self.ty_check_expr(
        //     //     kind_ctx,
        //     //     no_move_ty_ctx,
        //     //     lambda_ident_exec,
        //     //     &body_exec,
        //     //     body,
        //     // )?;
        //     panic!(
        //         "{:?}\n\n\n{:?}\n\n\n{:?}",
        //         ty_ctx, capture_ty_ctx, no_move_ty_ctx
        //     );
        //     return Err(TyError::String(
        //         "Cannot move values into Lambda.".to_string(),
        //     ));
        // }

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

        let fun_ty = Ty::new(TyKind::FnTy(Box::new(FnTy::new(
            vec![],
            params
                .iter()
                .map(|decl| decl.ty.as_ref().unwrap().clone())
                .collect(),
            lambda_ident_exec.ty.as_ref().clone(),
            Ty::new(TyKind::Data(Box::new(ret_dty.clone()))),
        ))));

        Ok((ty_ctx, fun_ty))
    }

    fn ty_check_block(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        block: &mut Block,
    ) -> TyResult<(TyCtx, Ty)> {
        let mut ty_ctx_with_prvs = ty_ctx.append_frame(vec![]);
        for prv in &block.prvs {
            ty_ctx_with_prvs = ty_ctx_with_prvs.append_prv_mapping(PrvMapping::new(prv))
        }
        let body_ty_ctx = self.ty_check_expr(
            kind_ctx,
            exec_borrow_ctx,
            ty_ctx_with_prvs,
            ident_exec,
            exec,
            &mut block.body,
        )?;
        let res_ty_ctx = body_ty_ctx.drop_last_frame();
        Ok((res_ty_ctx, block.body.ty.as_ref().unwrap().as_ref().clone()))
    }

    fn check_mutable(ty_ctx: &TyCtx, pl: &Place) -> TyResult<()> {
        let ident_ty = ty_ctx.ident_ty(&pl.ident)?;
        if ident_ty.mutbl != Mutability::Mut {
            return Err(TyError::AssignToConst(pl.to_place_expr()));
        }
        Ok(())
    }

    fn ty_check_assign_place(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        pl_expr: &PlaceExpr,
        e: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        let assigned_val_ty_ctx =
            self.ty_check_expr(kind_ctx, exec_borrow_ctx, ty_ctx, ident_exec, exec, e)?;
        let pl = pl_expr.to_place().unwrap();
        let mut place_ty = assigned_val_ty_ctx.place_dty(&pl)?;
        // FIXME this should be checked for ArrayViews as well
        // fn contains_view_dty(ty: &TyKind) -> bool {
        //     unimplemented!()
        // }
        // if contains_view_dty(&place_ty.ty) {
        //     return Err(TyError::String(format!(
        //         "Reassigning views is forbidden. Trying to assign view {:?}",
        //         e
        //     )));
        // }
        Self::check_mutable(&assigned_val_ty_ctx, &pl)?;

        // If the place is not dead, check that it is safe to use, otherwise it is safe to use anyway.
        if !matches!(&place_ty.dty, DataTyKind::Dead(_),) {
            let pl_uniq_loans = borrow_check::ownership_safe(
                self,
                kind_ctx,
                exec_borrow_ctx,
                &assigned_val_ty_ctx,
                exec,
                &[],
                Ownership::Uniq,
                pl_expr,
            )
            .map_err(|err| {
                TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Uniq, err)
            })?;
        }

        let e_dty = if let TyKind::Data(dty) = &mut e.ty.as_mut().unwrap().as_mut().ty {
            dty.as_mut()
        } else {
            return Err(TyError::UnexpectedType);
        };

        let after_subty_ctx =
            unify::sub_unify(kind_ctx, assigned_val_ty_ctx, e_dty, &mut place_ty)?;
        let adjust_place_ty_ctx = after_subty_ctx.set_place_dty(&pl, e_dty.clone());
        Ok((
            adjust_place_ty_ctx.without_reborrow_loans(pl_expr),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                ScalarTy::Unit,
            ))))),
        ))
    }

    fn ty_check_assign_deref(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        deref_expr: &mut PlaceExpr,
        e: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        let assigned_val_ty_ctx =
            self.ty_check_expr(kind_ctx, exec_borrow_ctx, ty_ctx, ident_exec, exec, e)?;
        self.place_expr_ty_under_exec_own(
            kind_ctx,
            &assigned_val_ty_ctx,
            exec,
            Ownership::Uniq,
            deref_expr,
        )?;

        borrow_check::ownership_safe(
            self,
            kind_ctx,
            exec_borrow_ctx,
            &assigned_val_ty_ctx,
            exec,
            &[],
            Ownership::Uniq,
            &deref_expr,
        )
        .map_err(|err| {
            TyError::ConflictingBorrow(Box::new(deref_expr.clone()), Ownership::Uniq, err)
        })?;

        let deref_ty = &mut deref_expr.ty.as_mut().unwrap();
        let after_subty_ctx = unify::sub_unify(
            kind_ctx,
            assigned_val_ty_ctx,
            e.ty.as_mut().unwrap().as_mut(),
            deref_ty,
        )?;

        if !deref_ty.is_fully_alive() {
            return Err(TyError::String(
                "Trying to assign through reference, to a type which is not fully alive."
                    .to_string(),
            ));
        }

        if let TyKind::Data(_) = &deref_ty.ty {
            Ok((
                after_subty_ctx.without_reborrow_loans(deref_expr),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                    ScalarTy::Unit,
                ))))),
            ))
        } else {
            Err(TyError::String(
                "Trying to dereference view type which is not allowed.".to_string(),
            ))
        }
    }

    fn ty_check_idx_assign(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        pl_expr: &mut PlaceExpr,
        idx: &Nat,
        e: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        if ident_exec.ty.ty != ExecTyKind::CpuThread && ident_exec.ty.ty != ExecTyKind::GpuThread {
            return Err(TyError::String(format!(
                "Trying to assign to memory from {}.",
                &ident_exec.ty.ty
            )));
        }

        let assigned_val_ty_ctx =
            self.ty_check_expr(kind_ctx, exec_borrow_ctx, ty_ctx, ident_exec, exec, e)?;
        self.place_expr_ty_under_exec_own(
            kind_ctx,
            &assigned_val_ty_ctx,
            exec,
            Ownership::Uniq,
            pl_expr,
        )?;
        let pl_expr_dty = if let TyKind::Data(dty) = &pl_expr.ty.as_ref().unwrap().ty {
            dty
        } else {
            return Err(TyError::String(
                "Trying to index into non array type.".to_string(),
            ));
        };

        let (n, own, mem, dty) = match &pl_expr_dty.dty {
            DataTyKind::Array(elem_dty, n) => unimplemented!(), //(Ty::Data(*elem_ty), n),
            DataTyKind::At(arr_dty, mem) => {
                if let DataTy {
                    dty: DataTyKind::Array(elem_dty, n),
                    ..
                } = arr_dty.as_ref()
                {
                    unimplemented!() //(Ty::Data(*elem_ty), n)
                } else {
                    return Err(TyError::String(
                        "Trying to index into non array type.".to_string(),
                    ));
                }
            }
            // FIXME is this allowed? There is no reborrow but this leaks the lifetime and does not
            //  consume the array view.
            DataTyKind::Ref(reff) => match &reff.dty.dty {
                DataTyKind::ArrayShape(sdty, n) if matches!(&sdty.dty, DataTyKind::Scalar(_)) => {
                    (n, reff.own, &reff.mem, sdty.as_ref())
                }
                DataTyKind::ArrayShape(_, _) => return Err(TyError::AssignToView),
                _ => {
                    return Err(TyError::String(
                        "Expected a reference to array view.".to_string(),
                    ))
                }
            },
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
        Self::accessible_memory(exec.ty.as_ref().unwrap().as_ref(), &mem)?;

        if own != Ownership::Uniq {
            return Err(TyError::String(
                "Cannot assign through shared references.".to_string(),
            ));
        }

        if n <= idx {
            return Err(TyError::String(
                "Trying to access array out-of-bounds.".to_string(),
            ));
        }

        borrow_check::ownership_safe(
            self,
            kind_ctx,
            exec_borrow_ctx,
            &assigned_val_ty_ctx,
            exec,
            &[],
            Ownership::Uniq,
            pl_expr,
        )
        .map_err(|err| {
            TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Shrd, err)
        })?;

        let after_subty_ctx = subty::check(
            kind_ctx,
            assigned_val_ty_ctx,
            e.ty.as_ref().unwrap().dty(),
            &dty,
        )?;

        Ok((
            after_subty_ctx,
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                ScalarTy::Unit,
            ))))),
        ))
    }

    fn ty_check_index_copy(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        pl_expr: &mut PlaceExpr,
        idx: &mut Nat,
    ) -> TyResult<(TyCtx, Ty)> {
        // TODO refactor
        borrow_check::ownership_safe(
            self,
            kind_ctx,
            exec_borrow_ctx,
            &ty_ctx,
            exec,
            &[],
            Ownership::Shrd,
            pl_expr,
        )
        .map_err(|err| {
            TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Shrd, err)
        })?;
        self.place_expr_ty_under_exec_own(kind_ctx, &ty_ctx, exec, Ownership::Shrd, pl_expr)?;

        let pl_expr_dty = if let TyKind::Data(dty) = &pl_expr.ty.as_ref().unwrap().ty {
            dty
        } else {
            return Err(TyError::String(
                "Trying to index into non array type.".to_string(),
            ));
        };

        let (elem_dty, n) = match pl_expr_dty.dty.clone() {
            DataTyKind::Array(elem_dty, n) => (*elem_dty, n),
            DataTyKind::At(arr_dty, _) => {
                if let DataTyKind::Array(elem_ty, n) = &arr_dty.dty {
                    (elem_ty.as_ref().clone(), n.clone())
                } else {
                    return Err(TyError::String(
                        "Trying to index into non array type.".to_string(),
                    ));
                }
            }
            DataTyKind::Ref(reff) => {
                match &reff.dty.dty {
                    DataTyKind::ArrayShape(sty, n) if matches!(&sty.dty, DataTyKind::Scalar(_)) => {
                        (sty.as_ref().clone(), n.clone())
                    }
                    DataTyKind::ArrayShape(view_ty, n) => {
                        Self::accessible_memory(exec.ty.as_ref().unwrap().as_ref(), &reff.mem)?;
                        // TODO is ownership checking necessary here?
                        (
                            DataTy::new(DataTyKind::Ref(Box::new(RefDty::new(
                                reff.rgn,
                                reff.own,
                                reff.mem,
                                view_ty.as_ref().clone(),
                            )))),
                            n.clone(),
                        )
                    }
                    DataTyKind::Array(elem_ty, n) => (elem_ty.as_ref().clone(), n.clone()),
                    _ => {
                        return Err(TyError::String(
                            "Expected a reference as element type of array view.".to_string(),
                        ))
                    }
                }
            }
            _ => {
                return Err(TyError::String(
                    "Trying to index into non array type.".to_string(),
                ))
            }
        };

        if &n < idx {
            return Err(TyError::String(
                "Trying to access array out-of-bounds.".to_string(),
            ));
        }

        if elem_dty.copyable() {
            Ok((ty_ctx, Ty::new(TyKind::Data(Box::new(elem_dty)))))
        } else {
            Err(TyError::String(format!(
                "Cannot move out of array type: {:?}",
                elem_dty
            )))
        }
    }

    // FIXME currently assumes that binary operators exist only for f32 and i32 and that both
    //  arguments have to be of the same type
    fn ty_check_binary_op(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        bin_op: &BinOp,
        lhs: &mut Expr,
        rhs: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        // FIXME certain operations should only be allowed for certain data types
        //      true > false is currently valid
        let lhs_ty_ctx =
            self.ty_check_expr(kind_ctx, exec_borrow_ctx, ty_ctx, ident_exec, exec, lhs)?;
        let rhs_ty_ctx =
            self.ty_check_expr(kind_ctx, exec_borrow_ctx, lhs_ty_ctx, ident_exec, exec, rhs)?;

        let lhs_ty = lhs.ty.as_ref().unwrap();
        let rhs_ty = rhs.ty.as_ref().unwrap();
        let ret = match bin_op {
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Mod
            | BinOp::And
            | BinOp::Or => lhs_ty.as_ref().clone(),
            BinOp::Eq | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Neq => Ty::new(
                TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::Bool)))),
            ),
        };
        // let fresh_id = constrain::fresh_ident("p_bin_op", DataTyKind::Ident);
        // let operand_ty = Ty::new(TyKind::Data(DataTy::new(fresh_id)));
        // self.term_constr
        //     .constrain(&mut rhs_ty_ctx, lhs_ty, &operand_ty)?;
        // self.term_constr
        //     .constrain(&mut rhs_ty_ctx, rhs_ty, &operand_ty)?;
        match (&lhs_ty.ty, &rhs_ty.ty) {
            (TyKind::Data(dty1), TyKind::Data(dty2)) => match (&dty1.dty, &dty2.dty) {
                (
                    DataTyKind::Scalar(ScalarTy::F32),
                    DataTyKind::Scalar(ScalarTy::F32),
                ) |
                ( DataTyKind::Scalar(ScalarTy::F64), DataTyKind::Scalar(ScalarTy::F64)) |
                (   DataTyKind::Scalar(ScalarTy::I32),
                    DataTyKind::Scalar(ScalarTy::I32),
                ) |
                (    DataTyKind::Scalar(ScalarTy::Bool),
                    DataTyKind::Scalar(ScalarTy::Bool),
                ) => Ok((rhs_ty_ctx, ret)),
                _ =>  Err(TyError::String(format!(
                    "Expected the same number types for operator {}, instead got\n Lhs: {:?}\n Rhs: {:?}",
                    bin_op, lhs, rhs
                )))
            }
            _ => Err(TyError::String(format!(
            "Expected the same number types for operator {}, instead got\n Lhs: {:?}\n Rhs: {:?}",
            bin_op, lhs, rhs
        ))),
        }
        // Ok((rhs_ty_ctx, operand_ty))
    }

    // FIXME currently assumes that binary operators exist only for f32 and i32
    fn ty_check_unary_op(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        un_op: &UnOp,
        e: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        let res_ctx = self.ty_check_expr(kind_ctx, exec_borrow_ctx, ty_ctx, ident_exec, exec, e)?;
        let e_ty = e.ty.as_ref().unwrap();
        let e_dty = if let TyKind::Data(dty) = &e_ty.ty {
            dty.as_ref()
        } else {
            return Err(TyError::String("expected data type, but found".to_string()));
        };
        match &e_dty {
            DataTy {
                dty: DataTyKind::Scalar(ScalarTy::F32),
                ..
            }
            | DataTy {
                dty: DataTyKind::Scalar(ScalarTy::I32),
                ..
            } => Ok((res_ctx, e_ty.as_ref().clone())),
            _ => Err(TyError::String(format!(
                "Exected a number type (i.e., f32 or i32), but found {:?}",
                e_ty
            ))),
        }
    }

    fn ty_check_app(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        ef: &mut Expr,
        k_args: &mut Vec<ArgKinded>,
        args: &mut [Expr],
    ) -> TyResult<(TyCtx, Ty)> {
        // TODO check well-kinded: FrameTyping, Prv, Ty
        let (mut res_ty_ctx, f_remain_gen_args, f_subst_param_tys, f_subst_ret_ty, mut f_mono_ty) =
            self.ty_check_dep_app(
                kind_ctx,
                exec_borrow_ctx,
                ty_ctx,
                ident_exec,
                exec,
                ef,
                k_args,
            )?;
        let exec_f = if let TyKind::FnTy(fn_ty) = &ef.ty.as_ref().unwrap().ty {
            if !callable_in(&fn_ty.exec_ty, exec.ty.as_ref().unwrap()) {
                return Err(TyError::String(format!(
                    "Trying to apply function for execution resource `{}` \
                under execution resource `{}`",
                    &fn_ty.exec_ty,
                    &exec.ty.as_ref().unwrap()
                )));
            }
            fn_ty.exec_ty.clone()
        } else {
            return Err(TyError::String(format!(
                "The provided function expression\n {:?}\n does not have a function type.",
                ef
            )));
        };

        for arg in args.iter_mut() {
            res_ty_ctx =
                self.ty_check_expr(kind_ctx, exec_borrow_ctx, res_ty_ctx, ident_exec, exec, arg)?;
        }
        let ret_dty = Ty::new(TyKind::Data(Box::new(DataTy::new(utils::fresh_ident(
            "ret_ty",
            DataTyKind::Ident,
        )))));
        unify::unify(
            &mut f_mono_ty,
            &mut Ty::new(TyKind::FnTy(Box::new(FnTy::new(
                vec![],
                args.iter()
                    .map(|arg| arg.ty.as_ref().unwrap().as_ref().clone())
                    .collect(),
                exec_f,
                ret_dty,
            )))),
        )?;
        let mut inferred_k_args = infer_kinded_args::infer_kinded_args_from_mono_ty(
            f_remain_gen_args,
            f_subst_param_tys,
            &f_subst_ret_ty,
            &f_mono_ty,
        );
        k_args.append(&mut inferred_k_args);

        if let TyKind::FnTy(fn_ty) = &f_mono_ty.ty {
            // TODO check provenance relations
            return Ok((res_ty_ctx, fn_ty.ret_ty.as_ref().clone()));
        }

        panic!("Expected function type but found something else.")
    }

    fn ty_check_dep_app(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        ef: &mut Expr,
        k_args: &mut [ArgKinded],
    ) -> TyResult<(TyCtx, Vec<IdentKinded>, Vec<Ty>, Ty, Ty)> {
        let res_ty_ctx =
            self.ty_check_expr(kind_ctx, exec_borrow_ctx, ty_ctx, ident_exec, exec, ef)?;
        if let TyKind::FnTy(fn_ty) = &ef.ty.as_ref().unwrap().ty {
            if fn_ty.generics.len() < k_args.len() {
                return Err(TyError::String(format!(
                    "Wrong amount of generic arguments. Expected {}, found {}",
                    fn_ty.generics.len(),
                    k_args.len()
                )));
            }
            for (gp, kv) in fn_ty.generics.iter().zip(&*k_args) {
                Self::check_arg_has_correct_kind(kind_ctx, &gp.kind, kv)?;
            }
            let subst_param_tys: Vec<_> = fn_ty
                .param_tys
                .iter()
                .map(|ty| TyChecker::subst_ident_kinded(&fn_ty.generics, k_args, ty))
                .collect();
            let subst_out_ty =
                TyChecker::subst_ident_kinded(&fn_ty.generics, k_args, &fn_ty.ret_ty);
            let mono_fun_ty = unify::inst_fn_ty_scheme(
                &fn_ty.generics[k_args.len()..],
                &subst_param_tys,
                &fn_ty.exec_ty,
                &subst_out_ty,
            )?;
            Ok((
                res_ty_ctx,
                fn_ty.generics[k_args.len()..].to_vec(),
                subst_param_tys,
                subst_out_ty,
                mono_fun_ty,
            ))
        } else {
            Err(TyError::String(format!(
                "The provided function expression\n {:?}\n does not have a function type.",
                ef
            )))
        }
    }

    pub(super) fn subst_ident_kinded(
        gen_params: &[IdentKinded],
        k_args: &[ArgKinded],
        ty: &Ty,
    ) -> Ty {
        let mut subst_ty = ty.clone();
        for (gen_param, k_arg) in gen_params.iter().zip(k_args) {
            subst_ty = subst_ty.subst_ident_kinded(gen_param, k_arg)
        }
        subst_ty
    }

    fn check_arg_has_correct_kind(
        kind_ctx: &KindCtx,
        expected: &Kind,
        kv: &ArgKinded,
    ) -> TyResult<()> {
        if expected == &kv.kind() {
            Ok(())
        } else {
            Err(TyError::String(format!(
                "expected argument of kind {:?}, but the provided argument is {:?}",
                expected, kv
            )))
        }
    }

    fn ty_check_app_kernel(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        app_kernel: &mut AppKernel,
    ) -> TyResult<(TyCtx, Ty)> {
        // current exec = cpu.thread
        if !matches!(exec.ty.as_ref().unwrap().ty, ExecTyKind::CpuThread) {
            return Err(TyError::String(
                "A kernel must be called from a CPU thread.".to_string(),
            ));
        }
        // new scope with gpu.grid<DIM, DIM> execution resource
        let mut kernel_ty_ctx = ty_ctx.append_frame(vec![]);
        let mut kernel_exec = ExecExpr::new(Exec::new(BaseExec::GpuGrid(
            app_kernel.grid_dim.clone(),
            app_kernel.block_dim.clone(),
        )));
        ty_check_exec(kind_ctx, &kernel_ty_ctx, ident_exec, &mut kernel_exec)?;
        // add explicit provenances to typing context (see block)
        for prv in &app_kernel.shared_mem_prvs {
            kernel_ty_ctx = kernel_ty_ctx.append_prv_mapping(PrvMapping::new(prv))
        }
        // generate internal shared memory identifier with provided dtys @ shared
        let shared_mem_idents_ty = app_kernel
            .shared_mem_dtys
            .iter()
            .map(|dty| {
                IdentTyped::new(
                    Ident::new_impli("shared_mem"),
                    Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::At(
                        Box::new(dty.clone()),
                        Memory::GpuShared,
                    ))))),
                    Mutability::Mut,
                    kernel_exec.clone(),
                )
            })
            .collect::<Vec<_>>();
        // and add shared mem idents to scope
        for it in &shared_mem_idents_ty {
            kernel_ty_ctx = kernel_ty_ctx.append_ident_typed(it.clone());
        }
        // references to shared memory identifiers
        let refs_to_shrd = shared_mem_idents_ty.iter().enumerate().map(|(i, idt)| {
            let prv = if i < app_kernel.shared_mem_prvs.len() {
                Some(app_kernel.shared_mem_prvs[i].clone())
            } else {
                None
            };
            Expr::new(ExprKind::Ref(
                prv,
                Ownership::Uniq,
                Box::new(PlaceExpr::new(PlaceExprKind::Ident(idt.ident.clone()))),
            ))
        });
        // type check argument list
        for arg in app_kernel.args.iter_mut() {
            kernel_ty_ctx = self.ty_check_expr(
                kind_ctx,
                exec_borrow_ctx,
                kernel_ty_ctx,
                ident_exec,
                exec,
                arg,
            )?;
        }
        // create extended argument list with references to shared memory
        let mut extended_args = app_kernel
            .args
            .iter()
            .cloned()
            .chain(refs_to_shrd)
            .collect::<Vec<_>>();
        // type check function application for generic args and extended argument list
        self.ty_check_app(
            kind_ctx,
            exec_borrow_ctx,
            kernel_ty_ctx.clone(),
            ident_exec,
            &kernel_exec,
            &mut app_kernel.fun,
            &mut app_kernel.gen_args,
            &mut extended_args,
        )?;
        kernel_ty_ctx = kernel_ty_ctx.drop_last_frame();
        Ok((
            kernel_ty_ctx,
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                ScalarTy::Unit,
            ))))),
        ))
    }

    fn ty_check_tuple(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        elems: &mut [Expr],
    ) -> TyResult<(TyCtx, Ty)> {
        let mut tmp_ty_ctx = ty_ctx;
        for elem in elems.iter_mut() {
            tmp_ty_ctx = self.ty_check_expr(
                kind_ctx,
                exec_borrow_ctx,
                tmp_ty_ctx,
                ident_exec,
                exec,
                elem,
            )?;
        }
        let elem_tys: TyResult<Vec<_>> = elems
            .iter()
            .map(|elem| match &elem.ty.as_ref().unwrap().ty {
                TyKind::Data(dty) => Ok(dty.as_ref().clone()),
                TyKind::FnTy(_) => Err(TyError::String(
                    "Tuple elements must be data types, but found function type.".to_string(),
                )),
            })
            .collect();
        Ok((
            tmp_ty_ctx,
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Tuple(
                elem_tys?,
            ))))),
        ))
    }

    fn ty_check_proj(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        e: &mut Expr,
        i: usize,
    ) -> TyResult<(TyCtx, Ty)> {
        if let ExprKind::PlaceExpr(_) = e.expr {
            panic!("Place expression should have been typechecked by a different rule.")
        }

        let tuple_ty_ctx =
            self.ty_check_expr(kind_ctx, exec_borrow_ctx, ty_ctx, ident_exec, exec, e)?;
        let e_dty = if let TyKind::Data(dty) = &e.ty.as_ref().unwrap().ty {
            dty.as_ref()
        } else {
            return Err(TyError::UnexpectedType);
        };

        let elem_ty = proj_elem_dty(e_dty, i);

        Ok((tuple_ty_ctx, Ty::new(TyKind::Data(Box::new(elem_ty?)))))
    }

    fn ty_check_array(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        mut ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        elems: &mut Vec<Expr>,
    ) -> TyResult<(TyCtx, Ty)> {
        assert!(!elems.is_empty());
        for elem in elems.iter_mut() {
            ty_ctx =
                self.ty_check_expr(kind_ctx, exec_borrow_ctx, ty_ctx, ident_exec, exec, elem)?;
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
                ty_ctx,
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Array(
                    Box::new(ty.as_ref().unwrap().dty().clone()),
                    Nat::Lit(elems.len()),
                ))))),
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
            Lit::F64(_) => ScalarTy::F64,
        };
        (
            ty_ctx,
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                scalar_data,
            ))))),
        )
    }

    fn infer_pattern_ident_tys(
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        pattern: &Pattern,
        pattern_ty: &Ty,
    ) -> TyResult<TyCtx> {
        let pattern_dty = if let TyKind::Data(dty) = &pattern_ty.ty {
            dty.as_ref()
        } else {
            return Err(TyError::UnexpectedType);
        };

        match (pattern, &pattern_dty.dty) {
            (Pattern::Ident(mutbl, ident), _) => {
                let ident_with_annotated_ty = IdentTyped::new(
                    ident.clone(),
                    Ty::new(TyKind::Data(Box::new(pattern_dty.clone()))),
                    *mutbl,
                    ExecExpr::new(Exec::new(BaseExec::Ident(ident_exec.ident.clone()))),
                );
                Ok(ty_ctx.append_ident_typed(ident_with_annotated_ty))
            }
            (Pattern::Wildcard, _) => Ok(ty_ctx),
            (Pattern::Tuple(patterns), DataTyKind::Tuple(elem_tys)) => Ok(patterns
                .iter()
                .zip(elem_tys)
                .try_fold(ty_ctx, |ctx, (p, tty)| {
                    TyChecker::infer_pattern_ident_tys(
                        ctx,
                        ident_exec,
                        p,
                        &Ty::new(TyKind::Data(Box::new(tty.clone()))),
                    )
                })?),
            _ => Err(TyError::PatternAndTypeDoNotMatch),
        }
    }

    fn infer_pattern_ty(
        kind_ctx: &KindCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        pattern: &Pattern,
        pattern_ty: &mut Option<Box<Ty>>,
        assign_ty: &mut Ty,
    ) -> TyResult<TyCtx> {
        let (ty_ctx_sub, pattern_ty) = if let Some(pty) = pattern_ty {
            (
                unify::sub_unify(kind_ctx, ty_ctx, assign_ty, pty)?,
                pty.as_ref().clone(),
            )
        } else {
            (ty_ctx, assign_ty.clone())
        };
        TyChecker::infer_pattern_ident_tys(ty_ctx_sub, ident_exec, pattern, &pattern_ty)
    }

    fn ty_check_let(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        pattern: &Pattern,
        pattern_ty: &mut Option<Box<Ty>>,
        expr: &mut Expr,
    ) -> TyResult<(TyCtx, Ty)> {
        let ty_ctx_e =
            self.ty_check_expr(kind_ctx, exec_borrow_ctx, ty_ctx, ident_exec, exec, expr)?;
        let e_ty = expr.ty.as_mut().unwrap();
        let ty_ctx_with_idents =
            TyChecker::infer_pattern_ty(kind_ctx, ty_ctx_e, ident_exec, pattern, pattern_ty, e_ty)?;
        Ok((
            ty_ctx_with_idents,
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                ScalarTy::Unit,
            ))))),
        ))
    }

    // TODO respect exec?
    fn ty_check_let_uninit(
        ty_ctx: TyCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        ident: &Ident,
        ty: &Ty,
    ) -> TyResult<(TyCtx, Ty)> {
        if let TyKind::Data(dty) = &ty.ty {
            let ident_with_ty = IdentTyped::new(
                ident.clone(),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Dead(
                    dty.clone(),
                ))))),
                Mutability::Mut,
                ExecExpr::new(Exec::new(BaseExec::Ident(ident_exec.ident.clone()))),
            );
            let ty_ctx_with_ident = ty_ctx.append_ident_typed(ident_with_ty);
            Ok((
                ty_ctx_with_ident,
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                    ScalarTy::Unit,
                ))))),
            ))
        } else {
            Err(TyError::MutabilityNotAllowed(ty.clone()))
        }
    }

    fn ty_check_seq(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        es: &mut [Expr],
    ) -> TyResult<(TyCtx, Ty)> {
        let mut ty_ctx = ty_ctx;
        for e in &mut *es {
            ty_ctx = self
                .ty_check_expr(kind_ctx, exec_borrow_ctx, ty_ctx, ident_exec, exec, e)?
                .garbage_collect_loans();
        }
        Ok((
            ty_ctx,
            es.last().unwrap().ty.as_ref().unwrap().as_ref().clone(),
        ))
    }

    fn ty_check_pl_expr_with_deref(
        &mut self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        mut ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        pl_expr: &mut PlaceExpr,
    ) -> TyResult<(TyCtx, Ty)> {
        // TODO refactor
        let exec = ty_ctx.get_exec_expr(&ident_exec.ident)?;
        borrow_check::ownership_safe(
            self,
            kind_ctx,
            exec_borrow_ctx,
            &ty_ctx,
            exec,
            &[],
            Ownership::Shrd,
            pl_expr,
        )
        .map_err(|err| {
            TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Shrd, err)
        })?;
        self.place_expr_ty_under_exec_own(kind_ctx, &ty_ctx, exec, Ownership::Shrd, pl_expr)?;
        if !pl_expr.ty.as_ref().unwrap().is_fully_alive() {
            return Err(TyError::String(format!(
                "Part of Place {:?} was moved before.",
                pl_expr
            )));
        }
        unify::unify(
            pl_expr.ty.as_mut().unwrap().as_mut(),
            &mut Ty::new(TyKind::Data(Box::new(DataTy::with_constr(
                utils::fresh_ident("pl_deref", DataTyKind::Ident),
                vec![Constraint::Copyable],
            )))),
        )?;
        if pl_expr.ty.as_ref().unwrap().copyable() {
            Ok((ty_ctx, pl_expr.ty.as_ref().unwrap().as_ref().clone()))
        } else {
            Err(TyError::String("Data type is not copyable.".to_string()))
        }
    }

    fn ty_check_pl_expr_without_deref(
        &self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        pl_expr: &PlaceExpr,
    ) -> TyResult<(TyCtx, Ty)> {
        let place = pl_expr.to_place().unwrap();
        // If place is an identifier referring to a globally declared function
        let (res_ty_ctx, pl_ty) = if let Ok(fun_ty) = self.gl_ctx.fn_ty_by_ident(&place.ident) {
            (ty_ctx, Ty::new(TyKind::FnTy(Box::new(fun_ty.clone()))))
        } else {
            // If place is NOT referring to a globally declared function
            let pl_ty = ty_ctx.place_dty(&place)?;
            if !pl_ty.is_fully_alive() {
                return Err(TyError::String(format!(
                    "Part of Place {:?} was moved before.",
                    pl_expr
                )));
            }
            let res_ty_ctx = if pl_ty.copyable() {
                // TODO refactor

                let exec = ty_ctx.get_exec_expr(&ident_exec.ident)?;
                borrow_check::ownership_safe(
                    self,
                    kind_ctx,
                    exec_borrow_ctx,
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
                    exec_borrow_ctx,
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
            (res_ty_ctx, Ty::new(TyKind::Data(Box::new(pl_ty))))
        };

        Ok((res_ty_ctx, pl_ty))
    }

    fn ty_check_borrow(
        &self,
        kind_ctx: &KindCtx,
        exec_borrow_ctx: &mut ExecBorrowCtx,
        ty_ctx: TyCtx,
        ident_exec: &IdentExec,
        exec: &ExecExpr,
        prv_val_name: &Option<String>,
        own: Ownership,
        pl_expr: &mut PlaceExpr,
    ) -> TyResult<(TyCtx, Ty)> {
        // If borrowing a place uniquely, is it mutable?
        if let Some(place) = pl_expr.to_place() {
            if own == Ownership::Uniq && ty_ctx.ident_ty(&place.ident)?.mutbl == Mutability::Const {
                return Err(TyError::ConstBorrow(pl_expr.clone()));
            }
        }
        let (impl_ctx, prv_val_name) = TyChecker::infer_prv(ty_ctx, prv_val_name);

        if !impl_ctx.loans_in_prv(&prv_val_name)?.is_empty() {
            return Err(TyError::PrvValueAlreadyInUse(prv_val_name.to_string()));
        }

        let loans = borrow_check::ownership_safe(
            self,
            kind_ctx,
            exec_borrow_ctx,
            &impl_ctx,
            exec,
            &[],
            own,
            pl_expr,
        )
        .map_err(|err| TyError::ConflictingBorrow(Box::new(pl_expr.clone()), own, err))?;

        let mems =
            self.place_expr_ty_mems_under_exec_own(kind_ctx, &impl_ctx, exec, own, pl_expr)?;
        mems.iter()
            .try_for_each(|mem| Self::accessible_memory(exec.ty.as_ref().unwrap().as_ref(), mem))?;

        let pl_expr_ty = pl_expr.ty.as_ref().unwrap();
        if !pl_expr_ty.is_fully_alive() {
            return Err(TyError::String(
                "The place was at least partially moved before.".to_string(),
            ));
        }

        let (reffed_ty, rmem) = match &pl_expr_ty.ty {
            TyKind::Data(dty) => match &dty.dty {
                DataTyKind::Dead(_) => panic!("Cannot happen because of the alive check."),
                DataTyKind::At(inner_ty, m) => (inner_ty.deref().clone(), m.clone()),
                _ => (
                    dty.as_ref().clone(),
                    if !mems.is_empty() {
                        let m = mems.last().unwrap();
                        m.clone()
                    } else {
                        return Err(TyError::String(
                            "Trying to borrow value that does not exist for the current \
            execution resource."
                                .to_string(),
                        ));
                    },
                ),
            },
            TyKind::FnTy(_) => {
                return Err(TyError::String("Trying to borrow a function.".to_string()))
            }
        };
        if rmem == Memory::GpuLocal {
            return Err(TyError::String(
                "Trying to take reference of unaddressable gpu.local memory.".to_string(),
            ));
        }
        let res_dty = DataTy::new(DataTyKind::Ref(Box::new(RefDty::new(
            Provenance::Value(prv_val_name.to_string()),
            own,
            rmem,
            reffed_ty,
        ))));
        exec_borrow_ctx.insert(exec, loans.clone());
        let res_ty_ctx = impl_ctx.extend_loans_for_prv(&prv_val_name, loans)?;
        Ok((res_ty_ctx, Ty::new(TyKind::Data(Box::new(res_dty)))))
    }

    // Δ; Γ ⊢ω p:τ
    // p in an ω context has type τ under Δ and Γ
    fn place_expr_ty_under_exec_own(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        exec: &ExecExpr,
        own: Ownership,
        pl_expr: &mut PlaceExpr,
    ) -> TyResult<()> {
        let _mem = self.place_expr_ty_mems_under_exec_own(kind_ctx, ty_ctx, exec, own, pl_expr)?;
        Ok(())
    }

    fn place_expr_ty_mems_under_exec_own(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        exec: &ExecExpr,
        own: Ownership,
        pl_expr: &mut PlaceExpr,
    ) -> TyResult<Vec<Memory>> {
        let (mem, _) = self
            .place_expr_ty_mem_passed_prvs_under_exec_own(kind_ctx, ty_ctx, exec, own, pl_expr)?;
        Ok(mem)
    }

    // Δ; Γ ⊢ω p:τ,{ρ}
    // p in an ω context has type τ under Δ and Γ, passing through provenances in Vec<ρ>
    fn place_expr_ty_mem_passed_prvs_under_exec_own(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        exec: &ExecExpr,
        own: Ownership,
        pl_expr: &mut PlaceExpr,
    ) -> TyResult<(Vec<Memory>, Vec<Provenance>)> {
        let (ty, mem, prvs) = match &mut pl_expr.pl_expr {
            // TC-Var
            PlaceExprKind::Ident(ident) => {
                self.var_expr_ty_mem_empty_prvs_under_exec_own(ty_ctx, exec, ident)?
            }
            // TC-Proj
            PlaceExprKind::Proj(tuple_expr, n) => self
                .proj_expr_ty_mem_passed_prvs_under_exec_own(
                    kind_ctx, ty_ctx, exec, own, tuple_expr, *n,
                )?,
            // TC-Deref
            PlaceExprKind::Deref(borr_expr) => self.deref_expr_ty_mem_passed_prvs_under_exec_own(
                kind_ctx, ty_ctx, exec, own, borr_expr,
            )?,
        };
        pl_expr.ty = Some(Box::new(ty));
        Ok((mem, prvs))
    }

    fn var_expr_ty_mem_empty_prvs_under_exec_own(
        &self,
        ty_ctx: &TyCtx,
        exec: &ExecExpr,
        ident: &Ident,
    ) -> TyResult<(Ty, Vec<Memory>, Vec<Provenance>)> {
        if let Ok(tty) = ty_ctx.ty_of_ident(ident) {
            // let ident_dty = if let TyKind::Data(dty) = &tty.ty {
            //     dty.as_ref()
            // } else {
            //     return Err(TyError::UnexpectedType);
            // };

            if !&tty.is_fully_alive() {
                return Err(TyError::String(format!(
                    "The value in this identifier `{}` has been moved out.",
                    ident
                )));
            }
            // FIXME Should throw an error if thread local memory is accessed by a block
            //  for example.
            let mem = Self::default_mem_by_exec(&exec.ty.as_ref().unwrap().ty);
            Ok((
                tty.clone(),
                if mem.is_some() {
                    vec![mem.unwrap()]
                } else {
                    vec![]
                },
                vec![],
            ))
        } else {
            let fn_ty = self.gl_ctx.fn_ty_by_ident(ident)?;
            Ok((
                Ty::new(TyKind::FnTy(Box::new(fn_ty.clone()))),
                vec![],
                vec![],
            ))
        }
    }

    fn default_mem_by_exec(exec_ty: &ExecTyKind) -> Option<Memory> {
        match exec_ty {
            ExecTyKind::CpuThread => Some(Memory::CpuMem),
            ExecTyKind::GpuThread => Some(Memory::GpuLocal),
            ExecTyKind::GpuGrid(_, _) => Some(Memory::GpuLocal),
            ExecTyKind::GpuGlobalThreads(_) => Some(Memory::GpuLocal),
            ExecTyKind::GpuBlockGrp(_, _) => Some(Memory::GpuLocal),
            ExecTyKind::GpuThreadGrp(_) => Some(Memory::GpuLocal),
            ExecTyKind::GpuBlock(_) => Some(Memory::GpuLocal),
            ExecTyKind::View => None,
        }
    }

    fn proj_expr_ty_mem_passed_prvs_under_exec_own(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        exec: &ExecExpr,
        own: Ownership,
        tuple_expr: &mut PlaceExpr,
        n: usize,
    ) -> TyResult<(Ty, Vec<Memory>, Vec<Provenance>)> {
        let (mem, passed_prvs) = self.place_expr_ty_mem_passed_prvs_under_exec_own(
            kind_ctx, ty_ctx, exec, own, tuple_expr,
        )?;
        let tuple_dty = match &tuple_expr.ty.as_ref().unwrap().ty {
            TyKind::Data(dty) => dty,
            ty_kind => {
                return Err(TyError::ExpectedTupleType(
                    ty_kind.clone(),
                    tuple_expr.clone(),
                ));
            }
        };
        match &tuple_dty.dty {
            DataTyKind::Tuple(elem_dtys) => {
                if let Some(dty) = elem_dtys.get(n) {
                    Ok((
                        Ty::new(TyKind::Data(Box::new(dty.clone()))),
                        mem,
                        passed_prvs,
                    ))
                } else {
                    Err(TyError::String(
                        "Trying to access non existing tuple element.".to_string(),
                    ))
                }
            }
            dty_kind => {
                return Err(TyError::ExpectedTupleType(
                    TyKind::Data(Box::new(DataTy::new(dty_kind.clone()))),
                    tuple_expr.clone(),
                ))
            }
        }
    }

    fn deref_expr_ty_mem_passed_prvs_under_exec_own(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        exec: &ExecExpr,
        own: Ownership,
        borr_expr: &mut PlaceExpr,
    ) -> TyResult<(Ty, Vec<Memory>, Vec<Provenance>)> {
        let (mut inner_mem, mut passed_prvs) = self
            .place_expr_ty_mem_passed_prvs_under_exec_own(kind_ctx, ty_ctx, exec, own, borr_expr)?;
        let borr_dty = if let TyKind::Data(dty) = &borr_expr.ty.as_ref().unwrap().ty {
            dty
        } else {
            return Err(TyError::String(
                "Trying to dereference non reference type.".to_string(),
            ));
        };
        match &borr_dty.dty {
            DataTyKind::Ref(reff) => {
                if &reff.own < &own {
                    return Err(TyError::String(
                        "Trying to dereference and mutably use a shrd reference.".to_string(),
                    ));
                }
                let outl_rels = passed_prvs.iter().map(|passed_prv| (&reff.rgn, passed_prv));
                subty::multiple_outlives(kind_ctx, ty_ctx.clone(), outl_rels)?;
                passed_prvs.push(reff.rgn.clone());
                inner_mem.push(reff.mem.clone());
                Ok((
                    Ty::new(TyKind::Data(Box::new(reff.dty.as_ref().clone()))),
                    inner_mem,
                    passed_prvs,
                ))
            }
            DataTyKind::RawPtr(dty) => {
                // TODO is anything of this correct?
                Ok((
                    Ty::new(TyKind::Data(Box::new(dty.as_ref().clone()))),
                    inner_mem,
                    passed_prvs,
                ))
            }
            _ => Err(TyError::String(
                "Trying to dereference non reference type.".to_string(),
            )),
        }
    }

    fn allowed_mem_for_exec(exec_ty: &ExecTyKind) -> Vec<Memory> {
        match exec_ty {
            ExecTyKind::CpuThread => vec![Memory::CpuMem],
            ExecTyKind::GpuThread
            | ExecTyKind::GpuGrid(_, _)
            | ExecTyKind::GpuBlock(_)
            | ExecTyKind::GpuBlockGrp(_, _)
            | ExecTyKind::GpuThreadGrp(_) => {
                vec![Memory::GpuGlobal, Memory::GpuShared, Memory::GpuLocal]
            }
            ExecTyKind::GpuGlobalThreads(_) => vec![Memory::GpuGlobal, Memory::GpuLocal],
            ExecTyKind::View => vec![],
        }
    }

    fn accessible_memory(exec_ty: &ExecTy, mem: &Memory) -> TyResult<()> {
        if Self::allowed_mem_for_exec(&exec_ty.ty).contains(mem) {
            Ok(())
        } else {
            Err(TyError::String(format!(
                "Trying to dereference pointer to `{}` from execution resource `{}`",
                mem, &exec_ty.ty
            )))
        }
    }

    // TODO respect memory
    fn ty_well_formed(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        exec_ty: &ExecTy,
        ty: &Ty,
    ) -> TyResult<()> {
        match &ty.ty {
            TyKind::Data(dty) => match &dty.dty {
                // TODO variables of Dead types can be reassigned. So why do we not have to check
                //  well-formedness of the type in Dead(ty)? (According paper).
                DataTyKind::Scalar(_)
                | DataTyKind::Atomic(_)
                | DataTyKind::Range
                | DataTyKind::RawPtr(_)
                | DataTyKind::Dead(_) => {}
                DataTyKind::Ident(ident) => {
                    if !kind_ctx.ident_of_kind_exists(ident, Kind::DataTy) {
                        Err(CtxError::KindedIdentNotFound(ident.clone()))?
                    }
                }
                DataTyKind::Ref(reff) => {
                    match &reff.rgn {
                        Provenance::Value(prv) => {
                            let elem_ty = Ty::new(TyKind::Data(reff.dty.clone()));
                            if !elem_ty.is_fully_alive() {
                                return Err(TyError::ReferenceToDeadTy);
                            }
                            let loans = ty_ctx.loans_in_prv(prv)?;
                            if !loans.is_empty() {
                                let mut exists = false;
                                for loan in loans {
                                    let Loan {
                                        place_expr,
                                        own: l_own,
                                    } = loan;
                                    if l_own != &reff.own {
                                        return Err(TyError::ReferenceToWrongOwnership);
                                    }
                                    let mut borrowed_pl_expr = place_expr.clone();
                                    // self.place_expr_ty_under_exec_own(
                                    //     kind_ctx,
                                    //     ty_ctx,
                                    //     exec_ty,
                                    //     *l_own,
                                    //     &mut borrowed_pl_expr,
                                    // )?;
                                    if let TyKind::Data(pl_expr_dty) =
                                        borrowed_pl_expr.ty.unwrap().ty
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
                                    if let DataTyKind::ArrayShape(_, _) = &dty.dty {
                                        eprintln!(
                                            "WARNING: Did not check well-formedness of\
                                            view type reference."
                                        )
                                    } else {
                                        return Err(TyError::ReferenceToIncompatibleType);
                                    }
                                }
                            }
                            self.ty_well_formed(kind_ctx, ty_ctx, exec_ty, &elem_ty)?;
                        }
                        Provenance::Ident(ident) => {
                            let elem_ty = Ty::new(TyKind::Data(reff.dty.clone()));
                            if !kind_ctx.ident_of_kind_exists(ident, Kind::Provenance) {
                                Err(CtxError::KindedIdentNotFound(ident.clone()))?
                            }
                            self.ty_well_formed(kind_ctx, ty_ctx, exec_ty, &elem_ty)?;
                        }
                    };
                }
                DataTyKind::Tuple(elem_dtys) => {
                    for elem_dty in elem_dtys {
                        self.ty_well_formed(
                            kind_ctx,
                            ty_ctx,
                            exec_ty,
                            &Ty::new(TyKind::Data(Box::new(elem_dty.clone()))),
                        )?;
                    }
                }
                DataTyKind::Array(elem_dty, n) => {
                    self.ty_well_formed(
                        kind_ctx,
                        ty_ctx,
                        exec_ty,
                        &Ty::new(TyKind::Data(elem_dty.clone())),
                    )?;
                    // TODO well-formed nat
                }
                DataTyKind::ArrayShape(elem_dty, n) => {
                    self.ty_well_formed(
                        kind_ctx,
                        ty_ctx,
                        exec_ty,
                        &Ty::new(TyKind::Data(elem_dty.clone())),
                    )?
                    // TODO well-formed nat
                }
                DataTyKind::At(elem_dty, Memory::Ident(ident)) => {
                    if !kind_ctx.ident_of_kind_exists(ident, Kind::Memory) {
                        return Err(TyError::CtxError(CtxError::KindedIdentNotFound(
                            ident.clone(),
                        )));
                    }
                    self.ty_well_formed(
                        kind_ctx,
                        ty_ctx,
                        exec_ty,
                        &Ty::new(TyKind::Data(elem_dty.clone())),
                    )?;
                }
                DataTyKind::At(elem_dty, _) => {
                    self.ty_well_formed(
                        kind_ctx,
                        ty_ctx,
                        exec_ty,
                        &Ty::new(TyKind::Data(elem_dty.clone())),
                    )?;
                }
            },
            // TODO check well-formedness of Nats
            TyKind::FnTy(fn_ty) => {
                let extended_kind_ctx = kind_ctx.clone().append_idents(fn_ty.generics.clone());
                self.ty_well_formed(&extended_kind_ctx, ty_ctx, exec_ty, &fn_ty.ret_ty)?;
                for param_ty in &fn_ty.param_tys {
                    self.ty_well_formed(&extended_kind_ctx, ty_ctx, exec_ty, param_ty)?;
                }
            }
        }
        Ok(())
    }
}

// fn exec_ty_size(exec_ty: &ExecTy, dim_compo: DimCompo) -> Nat {
//     match &exec_ty.ty {
//         ExecTyKind::CpuThread | ExecTyKind::GpuThread => Nat::Lit(1),
//         ExecTyKind::GpuGrid(gdim, _) | ExecTyKind::GpuBlockGrp(gdim, _) => {
//             gdim.proj_size(dim_compo)
//         }
//         ExecTyKind::GpuBlock(dim) | ExecTyKind::GpuThreadGrp(dim) => dim.proj_size(dim_compo),
//         ExecTyKind::GpuGlobalThreads(_) => todo!(),
//         ExecTyKind::View => unreachable!(),
//     }
// }

pub fn callable_in(callee_exec_ty: &ExecTy, caller_exec_ty: &ExecTy) -> bool {
    if &callee_exec_ty.ty == &ExecTyKind::View {
        true
    } else {
        let res = unify::unify(&mut callee_exec_ty.clone(), &mut caller_exec_ty.clone());
        res.is_ok()
    }
}

fn ty_check_exec(
    kind_ctx: &KindCtx,
    ty_ctx: &TyCtx,
    ident_exec: &IdentExec,
    exec_expr: &mut ExecExpr,
) -> TyResult<()> {
    let mut exec_ty = match &exec_expr.exec.base {
        BaseExec::Ident(ident) => {
            if ident == &ident_exec.ident {
                ident_exec.ty.ty.clone()
            } else {
                let mut inline_exec = ty_ctx.get_exec_expr(ident)?;
                inline_exec.ty.as_ref().unwrap().ty.clone()
            }
        }
        BaseExec::CpuThread => ExecTyKind::CpuThread,
        BaseExec::GpuGrid(gdim, bdim) => ExecTyKind::GpuGrid(gdim.clone(), bdim.clone()),
    };

    for e in &exec_expr.exec.path {
        match &e {
            ExecPathElem::Distrib(d) => {
                exec_ty = ty_check_exec_distrib(*d, &exec_ty)?;
            }
            ExecPathElem::SplitProj(exec_split) => {
                exec_ty = ty_check_exec_split_proj(
                    exec_split.split_dim,
                    &exec_split.pos,
                    exec_split.proj,
                    &exec_ty,
                )?;
            }
            ExecPathElem::ToThreads(d) => {
                exec_ty = ty_check_exec_to_threads(*d, &exec_ty)?;
            }
        }
    }
    exec_expr.ty = Some(Box::new(ExecTy::new(exec_ty)));
    Ok(())
}

fn ty_check_exec_to_threads(dim: DimCompo, exec_ty: &ExecTyKind) -> TyResult<ExecTyKind> {
    let result_ty = if let ExecTyKind::GpuGrid(gdim, bdim) = exec_ty {
        // match (gdim, bdim) {
        // }
        ()
    };
    todo!()
}

fn ty_check_exec_distrib(d: DimCompo, exec_ty: &ExecTyKind) -> TyResult<ExecTyKind> {
    let res_ty = match exec_ty {
        ExecTyKind::GpuGrid(gdim, bdim) => {
            let inner_dim = remove_dim(gdim, d)?;
            match inner_dim {
                Some(dim) => ExecTyKind::GpuGrid(dim, bdim.clone()),
                None => ExecTyKind::GpuBlock(bdim.clone()),
            }
        }
        ExecTyKind::GpuBlockGrp(gdim, bdim) => {
            let inner_dim = remove_dim(gdim, d)?;
            match inner_dim {
                Some(dim) => ExecTyKind::GpuBlockGrp(dim, bdim.clone()),
                None => ExecTyKind::GpuBlock(bdim.clone()),
            }
        }
        ExecTyKind::GpuBlock(bdim) => {
            let inner_dim = remove_dim(bdim, d)?;
            match inner_dim {
                Some(dim) => ExecTyKind::GpuBlock(dim),
                None => ExecTyKind::GpuThread,
            }
        }
        ExecTyKind::GpuThreadGrp(tdim) => {
            let inner_dim = remove_dim(tdim, d)?;
            match inner_dim {
                Some(dim) => ExecTyKind::GpuThreadGrp(dim),
                None => ExecTyKind::GpuThread,
            }
        }
        ExecTyKind::GpuGlobalThreads(gdim) => {
            let inner_dim = remove_dim(gdim, d)?;
            match inner_dim {
                Some(dim) => ExecTyKind::GpuGlobalThreads(dim),
                None => ExecTyKind::GpuThread,
            }
        }
        ex @ ExecTyKind::CpuThread | ex @ ExecTyKind::GpuThread | ex @ ExecTyKind::View => {
            return Err(TyError::String(format!("Cannot schedule over {}", ex)))
        }
    };
    Ok(res_ty)
}

pub fn remove_dim(dim: &Dim, dim_compo: DimCompo) -> TyResult<Option<Dim>> {
    match (dim, dim_compo) {
        (Dim::XYZ(dim3d), DimCompo::X) => Ok(Some(Dim::YZ(Box::new(Dim2d(
            dim3d.as_ref().1.clone(),
            dim3d.2.clone(),
        ))))),
        (Dim::XYZ(dim3d), DimCompo::Y) => Ok(Some(Dim::XZ(Box::new(Dim2d(
            dim3d.as_ref().0.clone(),
            dim3d.2.clone(),
        ))))),
        (Dim::XYZ(dim3d), DimCompo::Z) => Ok(Some(Dim::XY(Box::new(Dim2d(
            dim3d.as_ref().0.clone(),
            dim3d.as_ref().1.clone(),
        ))))),
        (Dim::XY(dim2d), DimCompo::X) => {
            Ok(Some(Dim::Y(Box::new(Dim1d(dim2d.as_ref().1.clone())))))
        }
        (Dim::XY(dim2d), DimCompo::Y) => {
            Ok(Some(Dim::X(Box::new(Dim1d(dim2d.as_ref().0.clone())))))
        }
        (Dim::XZ(dim2d), DimCompo::X) => {
            Ok(Some(Dim::Z(Box::new(Dim1d(dim2d.as_ref().1.clone())))))
        }
        (Dim::XZ(dim2d), DimCompo::Z) => {
            Ok(Some(Dim::X(Box::new(Dim1d(dim2d.as_ref().0.clone())))))
        }
        (Dim::YZ(dim2d), DimCompo::Y) => {
            Ok(Some(Dim::Z(Box::new(Dim1d(dim2d.as_ref().1.clone())))))
        }
        (Dim::YZ(dim2d), DimCompo::Z) => {
            Ok(Some(Dim::Y(Box::new(Dim1d(dim2d.as_ref().0.clone())))))
        }
        (Dim::X(_), DimCompo::X) | (Dim::Y(_), DimCompo::Y) | (Dim::Z(_), DimCompo::Z) => Ok(None),
        _ => Err(TyError::IllegalDimension),
    }
}

fn ty_check_exec_split_proj(
    d: DimCompo,
    n: &Nat,
    proj: u8,
    exec_ty: &ExecTyKind,
) -> TyResult<ExecTyKind> {
    // TODO check well-formedness of Nats
    let (lexec_ty, rexec_ty) = match exec_ty {
        ExecTyKind::GpuGrid(gdim, bdim) | ExecTyKind::GpuBlockGrp(gdim, bdim) => {
            let (ldim, rdim) = split_dim(d, n.clone(), gdim.clone())?;
            (
                ExecTyKind::GpuBlockGrp(ldim, bdim.clone()),
                ExecTyKind::GpuBlockGrp(rdim, bdim.clone()),
            )
        }
        ExecTyKind::GpuBlock(dim) | ExecTyKind::GpuThreadGrp(dim) => {
            let (ldim, rdim) = split_dim(d, n.clone(), dim.clone())?;
            (
                ExecTyKind::GpuThreadGrp(ldim),
                ExecTyKind::GpuThreadGrp(rdim),
            )
        }
        ExecTyKind::GpuGlobalThreads(dim) => {
            let (ldim, rdim) = split_dim(d, n.clone(), dim.clone())?;
            (
                ExecTyKind::GpuGlobalThreads(ldim),
                ExecTyKind::GpuGlobalThreads(rdim),
            )
        }
        ex => {
            return Err(TyError::String(format!(
                "Trying to split non-splittable execution resource: {}",
                ex
            )))
        }
    };
    Ok(if proj == 0 { lexec_ty } else { rexec_ty })
}

fn split_dim(split_dim: DimCompo, pos: Nat, dim: Dim) -> TyResult<(Dim, Dim)> {
    Ok(match dim {
        Dim::XYZ(d) => match split_dim {
            DimCompo::X => (
                Dim::new_3d(pos.clone(), d.1.clone(), d.2.clone()),
                Dim::new_3d(
                    Nat::BinOp(BinOpNat::Sub, Box::new(d.0), Box::new(pos)),
                    d.1,
                    d.2,
                ),
            ),
            DimCompo::Y => (
                Dim::new_3d(d.0.clone(), pos.clone(), d.2.clone()),
                Dim::new_3d(
                    d.0,
                    Nat::BinOp(BinOpNat::Sub, Box::new(d.1), Box::new(pos)),
                    d.2,
                ),
            ),
            DimCompo::Z => (
                Dim::new_3d(d.0.clone(), d.1.clone(), pos.clone()),
                Dim::new_3d(
                    d.0,
                    d.1,
                    Nat::BinOp(BinOpNat::Sub, Box::new(d.2), Box::new(pos)),
                ),
            ),
        },
        Dim::XY(d) => match split_dim {
            DimCompo::X => (
                Dim::new_2d(Dim::XY, pos.clone(), d.1.clone()),
                Dim::new_2d(
                    Dim::XY,
                    Nat::BinOp(BinOpNat::Sub, Box::new(d.0), Box::new(pos)),
                    d.1,
                ),
            ),
            DimCompo::Y => (
                Dim::new_2d(Dim::XY, d.0.clone(), pos.clone()),
                Dim::new_2d(
                    Dim::XY,
                    d.0,
                    Nat::BinOp(BinOpNat::Sub, Box::new(d.1), Box::new(pos)),
                ),
            ),
            DimCompo::Z => return Err(TyError::IllegalDimension),
        },
        Dim::XZ(d) => match split_dim {
            DimCompo::X => (
                Dim::new_2d(Dim::XZ, pos.clone(), d.1.clone()),
                Dim::new_2d(
                    Dim::XZ,
                    Nat::BinOp(BinOpNat::Sub, Box::new(d.0), Box::new(pos)),
                    d.1,
                ),
            ),
            DimCompo::Y => return Err(TyError::IllegalDimension),
            DimCompo::Z => (
                Dim::new_2d(Dim::XZ, d.0.clone(), pos.clone()),
                Dim::new_2d(
                    Dim::XZ,
                    d.0,
                    Nat::BinOp(BinOpNat::Sub, Box::new(d.1), Box::new(pos)),
                ),
            ),
        },
        Dim::YZ(d) => match split_dim {
            DimCompo::X => return Err(TyError::IllegalDimension),
            DimCompo::Y => (
                Dim::new_2d(Dim::YZ, pos.clone(), d.1.clone()),
                Dim::new_2d(
                    Dim::YZ,
                    Nat::BinOp(BinOpNat::Sub, Box::new(d.0), Box::new(pos)),
                    d.1,
                ),
            ),
            DimCompo::Z => (
                Dim::new_2d(Dim::YZ, d.0.clone(), pos.clone()),
                Dim::new_2d(
                    Dim::YZ,
                    d.0,
                    Nat::BinOp(BinOpNat::Sub, Box::new(d.1), Box::new(pos)),
                ),
            ),
        },
        Dim::X(d) => {
            if let DimCompo::X = split_dim {
                (
                    Dim::new_1d(Dim::X, pos.clone()),
                    Dim::new_1d(
                        Dim::X,
                        Nat::BinOp(BinOpNat::Sub, Box::new(d.0), Box::new(pos)),
                    ),
                )
            } else {
                return Err(TyError::IllegalDimension);
            }
        }
        Dim::Y(d) => {
            if let DimCompo::Y = split_dim {
                (
                    Dim::new_1d(Dim::Y, pos.clone()),
                    Dim::new_1d(
                        Dim::Y,
                        Nat::BinOp(BinOpNat::Sub, Box::new(d.0), Box::new(pos)),
                    ),
                )
            } else {
                return Err(TyError::IllegalDimension);
            }
        }
        Dim::Z(d) => {
            if let DimCompo::Z = split_dim {
                (
                    Dim::new_1d(Dim::Z, pos.clone()),
                    Dim::new_1d(
                        Dim::Z,
                        Nat::BinOp(BinOpNat::Sub, Box::new(d.0), Box::new(pos)),
                    ),
                )
            } else {
                return Err(TyError::IllegalDimension);
            }
        }
    })
}

pub fn proj_elem_dty(dty: &DataTy, i: usize) -> TyResult<DataTy> {
    match &dty.dty {
        DataTyKind::Tuple(dtys) => match dtys.get(i) {
            Some(dty) => Ok(dty.clone()),
            None => Err(TyError::String(format!(
                "Cannot project element `{}` from tuple with {} elements.",
                i,
                dtys.len()
            ))),
        },
        _ => Err(TyError::String(
            "Cannot project from non tuple type.".to_string(),
        )),
    }
}
