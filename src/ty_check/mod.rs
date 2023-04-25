mod borrow_check;
mod ctxs;
mod error;
mod exec;
mod infer_kinded_args;
mod pl_expr;
pub mod pre_decl;
mod subty;
mod unify;

use self::pl_expr::PlExprTyCtx;
use crate::ast::internal::{Frame, IdentTyped, Loan, Place, PrvMapping};
use crate::ast::utils;
use crate::ast::*;
use crate::error::ErrorReported;
use ctxs::{AccessCtx, GlobalCtx, KindCtx, TyCtx};
use error::*;
use std::collections::HashSet;

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
use crate::ty_check::borrow_check::BorrowCheckCtx;
pub(crate) use matches_dty;

// ∀ε ∈ Σ. Σ ⊢ ε
// --------------
//      ⊢ Σ
pub fn ty_check(compil_unit: &mut CompilUnit) -> Result<(), ErrorReported> {
    let gl_ctx = GlobalCtx::from_iter(compil_unit.fun_defs.iter());
    ty_check_compil_unit(&gl_ctx, compil_unit).map_err(|err| {
        err.emit(compil_unit.source);
        ErrorReported
    })
}

fn ty_check_compil_unit(gl_ctx: &GlobalCtx, compil_unit: &mut CompilUnit) -> TyResult<()> {
    let errs = compil_unit
        .fun_defs
        .iter_mut()
        .fold(
            Vec::<TyError>::new(),
            |mut errors, fun| match ty_check_global_fun_def(gl_ctx, fun) {
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

struct ExprTyCtx<'ctxt> {
    gl_ctx: &'ctxt GlobalCtx,
    ident_exec: &'ctxt IdentExec,
    kind_ctx: &'ctxt mut KindCtx,
    exec: ExecExpr,
    ty_ctx: &'ctxt mut TyCtx,
    access_ctx: &'ctxt mut AccessCtx,
}

// Σ ⊢ fn f <List[φ], List[ρ], List[α]> (x1: τ1, ..., xn: τn) → τr where List[ρ1:ρ2] { e }
fn ty_check_global_fun_def(gl_ctx: &GlobalCtx, gf: &mut FunDef) -> TyResult<()> {
    // TODO check that every prv_rel only uses provenance variables bound in generic_params
    let ident_exec = gf.exec_decl.clone();
    let mut kind_ctx = KindCtx::gl_fun_kind_ctx(gf.generic_params.clone(), gf.prv_rels.clone())?;
    let mut ty_ctx = TyCtx::new();
    // Build frame typing for this function
    // TODO give Frame its own type and move this into frame and/or ParamDecl
    let param_idents_ty: Vec<_> = gf
        .param_decls
        .iter()
        .map(|ParamDecl { ident, ty, mutbl }| IdentTyped {
            ident: ident.clone(),
            ty: ty.as_ref().unwrap().clone(),
            mutbl: *mutbl,
            exec: ExecExpr::new(Exec::new(BaseExec::Ident(gf.exec_decl.ident.clone()))),
        })
        .collect();
    for pi in param_idents_ty {
        ty_ctx.append_ident_typed(pi);
    }
    for prv in &gf.body.prvs {
        ty_ctx.append_prv_mapping(PrvMapping::new(prv));
    }

    let mut exec = ExecExpr::new(Exec::new(BaseExec::Ident(gf.exec_decl.ident.clone())));
    exec::ty_check(&kind_ctx, &ty_ctx, &gf.exec_decl, &mut exec)?;
    ty_ctx.append_exec_mapping(gf.exec_decl.ident.clone(), exec.clone());

    let mut access_ctx = AccessCtx::new();
    let mut ctx = ExprTyCtx {
        gl_ctx,
        kind_ctx: &mut kind_ctx,
        ident_exec: &ident_exec,
        exec,
        ty_ctx: &mut ty_ctx,
        access_ctx: &mut access_ctx,
    };

    ty_check_expr(&mut ctx, &mut gf.body.body)?;
    // t <= t_f
    // unify::constrain(
    //     gf.body_expr.ty.as_ref().unwrap(),
    //     &Ty::new(TyKind::Data(gf.ret_dty.clone())),
    // )?;

    //coalesce::coalesce_ty(&mut self.term_constr.constr_map, &mut body_ctx, )
    let mut empty_ty_ctx = TyCtx::new();
    subty::check(
        &kind_ctx,
        &mut empty_ty_ctx,
        gf.body.body.ty.as_ref().unwrap().dty(),
        &gf.ret_dty,
    )?;

    #[cfg(debug_assertions)]
    if let Some(hm) = utils::implicit_idents(gf) {
        panic!("Implicit Idents:\n{:?}", hm)
    }
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
fn ty_check_expr(ctx: &mut ExprTyCtx, expr: &mut Expr) -> TyResult<()> {
    let ty = match &mut expr.expr {
        ExprKind::PlaceExpr(pl_expr) => {
            if pl_expr.is_place() {
                ty_check_pl_expr_without_deref(ctx, pl_expr)?
            } else {
                ty_check_pl_expr_with_deref(ctx, pl_expr)?
            }
        }
        ExprKind::Block(block) => ty_check_block(ctx, block)?,
        ExprKind::Let(pattern, ty, e) => ty_check_let(ctx, pattern, ty, e)?,
        ExprKind::LetUninit(ident, ty) => ty_check_let_uninit(ctx, ident, ty)?,
        ExprKind::Seq(es) => ty_check_seq(ctx, es)?,
        ExprKind::Lit(l) => ty_check_literal(l),
        ExprKind::Array(elems) => ty_check_array(ctx, elems)?,
        ExprKind::Tuple(elems) => ty_check_tuple(ctx, elems)?,
        // ExprKind::Proj(e, i) => ty_check_proj(ctx, e, *i)?,
        ExprKind::App(ef, k_args, args) => ty_check_app(ctx, ef, k_args, args)?,
        ExprKind::DepApp(ef, k_args) => {
            Ty::new(TyKind::FnTy(Box::new(ty_check_dep_app(ctx, ef, k_args)?.4)))
        }
        ExprKind::AppKernel(app_kernel) => ty_check_app_kernel(ctx, app_kernel)?,
        ExprKind::Ref(prv, own, pl_expr) => ty_check_borrow(ctx, prv, *own, pl_expr)?,
        ExprKind::Assign(pl_expr, e) => {
            if pl_expr.is_place() {
                ty_check_assign_place(ctx, &pl_expr, e)?
            } else {
                ty_check_assign_deref(ctx, pl_expr, e)?
            }
        }
        ExprKind::IdxAssign(pl_expr, idx, e) => ty_check_idx_assign(ctx, pl_expr, idx, e)?,
        ExprKind::Indep(indep) => ty_check_indep(ctx, indep)?,
        ExprKind::Sched(sched) => ty_check_sched(ctx, sched)?,
        ExprKind::ForNat(var, range, body) => ty_check_for_nat(ctx, var, range, body)?,
        ExprKind::For(ident, collec, body) => ty_check_for(ctx, ident, collec, body)?,
        ExprKind::IfElse(cond, case_true, case_false) => {
            ty_check_if_else(ctx, cond, case_true, case_false)?
        }
        ExprKind::If(cond, case_true) => ty_check_if(ctx, cond, case_true)?,
        ExprKind::While(cond, body) => ty_check_while(ctx, cond, body)?,
        ExprKind::Lambda(params, lambda_exec_ident, ret_ty, body) => {
            ty_check_lambda(ctx, params, lambda_exec_ident, ret_ty, body)?
        }
        ExprKind::BinOp(bin_op, lhs, rhs) => ty_check_binary_op(ctx, bin_op, lhs, rhs)?,
        ExprKind::UnOp(un_op, e) => ty_check_unary_op(ctx, un_op, e)?,
        ExprKind::Sync(exec) => ty_check_sync(ctx, exec)?,
        ExprKind::Range(l, u) => ty_check_range(ctx, l, u)?,
        // ExprKind::BorrowIndex(_, _, _, _) => unimplemented!(),
    };

    // TODO reintroduce!!!!
    //if let Err(err) = self.ty_well_formed(kind_ctx, &res_ty_ctx, exec, &ty) {
    //    panic!("{:?}", err);
    //}
    expr.ty = Some(Box::new(ty));
    Ok(())
}

fn ty_check_sync(ctx: &mut ExprTyCtx, exec: &mut Option<ExecExpr>) -> TyResult<Ty> {
    let synced = match exec {
        Some(exec) => {
            exec::ty_check(ctx.kind_ctx, ctx.ty_ctx, ctx.ident_exec, exec)?;
            exec
        }
        None => &ctx.exec,
    };
    syncable_under_exec(synced, &ctx.exec)?;
    ctx.access_ctx.clear_for(synced);
    Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
        DataTyKind::Scalar(ScalarTy::Unit),
    )))))
}

// assumes fully typed ExecExpr as input
fn syncable_under_exec(synced: &ExecExpr, under: &ExecExpr) -> TyResult<()> {
    if !syncable_exec_ty(synced.ty.as_ref().unwrap()) {
        return Err(TyError::String(
            "trying to synchronize non-synchronizable execution resource".to_string(),
        ));
    }
    if under.is_sub_exec_of(synced) || under == synced {
        for ep in &under.exec.path[synced.exec.path.len()..] {
            if matches!(ep, ExecPathElem::SplitProj(_)) {
                return Err(TyError::String(
                    "tyring to synchronize on split execution resource".to_string(),
                ));
            }
        }
        Ok(())
    } else {
        Err(TyError::String(
            "cannot call sync from this execution resource".to_string(),
        ))
    }
}

fn syncable_exec_ty(exec_ty: &ExecTy) -> bool {
    match &exec_ty.ty {
        ExecTyKind::GpuBlock(_) => true,
        ExecTyKind::CpuThread
        | ExecTyKind::GpuGrid(_, _)
        | ExecTyKind::GpuGlobalThreads(_)
        | ExecTyKind::GpuBlockGrp(_, _)
        | ExecTyKind::GpuThreadGrp(_)
        | ExecTyKind::GpuThread
        | ExecTyKind::View => false,
    }
}

fn ty_check_range(ctx: &mut ExprTyCtx, l: &mut Expr, u: &mut Expr) -> TyResult<Ty> {
    // FIXME this is wrong and should check that the current exec is legal
    if &ctx.ident_exec.ty.ty != &ExecTyKind::CpuThread
        && &ctx.ident_exec.ty.ty != &ExecTyKind::GpuThread
    {
        return Err(TyError::IllegalExec);
    }

    ty_check_expr(ctx, l)?;
    ty_check_expr(ctx, u)?;
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

    Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
        DataTyKind::Range,
    )))))
}

fn infer_and_append_prv(ty_ctx: &mut TyCtx, prv_name: &Option<String>) -> String {
    if let Some(prv) = prv_name.as_ref() {
        prv.clone()
    } else {
        let name = utils::fresh_name("r");
        ty_ctx.append_prv_mapping(PrvMapping::new(&name));
        name
    }
}

fn ty_check_for_nat(
    ctx: &mut ExprTyCtx,
    var: &Ident,
    range: &Nat,
    body: &mut Expr,
) -> TyResult<Ty> {
    ctx.kind_ctx
        .push_empty_scope()
        .append_idents(vec![IdentKinded {
            ident: var.clone(),
            kind: Kind::Nat,
        }]);
    let compare_ty_ctx = ctx.ty_ctx.clone();
    ctx.ty_ctx.push_empty_frame();
    ty_check_expr(ctx, body)?;
    ctx.ty_ctx.pop_frame();
    if ctx.ty_ctx != &compare_ty_ctx {
        return Err(TyError::String(
            "Using a data type in loop that can only be used once.".to_string(),
        ));
    }
    ctx.kind_ctx.drop_scope();
    Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
        DataTyKind::Scalar(ScalarTy::Unit),
    )))))
}

fn ty_check_for(
    ctx: &mut ExprTyCtx,
    ident: &Ident,
    collec: &mut Expr,
    body: &mut Expr,
) -> TyResult<Ty> {
    ty_check_expr(ctx, collec)?;
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
    let compare_ty_ctx = ctx.ty_ctx.clone();
    let mut frame = Frame::new();
    frame.append_idents_typed(vec![IdentTyped::new(
        ident.clone(),
        Ty::new(TyKind::Data(Box::new(DataTy::new(ident_dty)))),
        Mutability::Const,
        ExecExpr::new(Exec::new(BaseExec::Ident(ctx.ident_exec.ident.clone()))),
    )]);
    ctx.ty_ctx.push_frame(frame);
    ty_check_expr(ctx, body)?;
    ctx.ty_ctx.pop_frame();
    if ctx.ty_ctx != &compare_ty_ctx {
        return Err(TyError::String(
            "Using a data type in loop that can only be used once.".to_string(),
        ));
    }
    Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
        DataTyKind::Scalar(ScalarTy::Unit),
    )))))
}

fn ty_check_while(ctx: &mut ExprTyCtx, cond: &mut Expr, body: &mut Expr) -> TyResult<Ty> {
    ty_check_expr(ctx, cond)?;
    ctx.ty_ctx.push_empty_frame();
    ty_check_expr(ctx, body)?;
    ctx.ty_ctx.pop_frame();
    let compare_ty_ctx = ctx.ty_ctx.clone();
    // Is it better/more correct to push and pop scope around this as well?
    ty_check_expr(ctx, cond)?;
    if ctx.ty_ctx != &compare_ty_ctx {
        return Err(TyError::String(
            "Context should have stayed the same".to_string(),
        ));
    }
    ctx.ty_ctx.push_empty_frame();
    ty_check_expr(ctx, body)?;
    ctx.ty_ctx.pop_frame();
    if ctx.ty_ctx != &compare_ty_ctx {
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
    Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
        DataTyKind::Scalar(ScalarTy::Unit),
    )))))
}

fn ty_check_if_else(
    ctx: &mut ExprTyCtx,
    cond: &mut Expr,
    case_true: &mut Expr,
    case_false: &mut Expr,
) -> TyResult<Ty> {
    // TODO deal with provenances in cases
    ty_check_expr(ctx, cond)?;
    // TODO acccess_ctx clone
    let mut ty_ctx_clone = ctx.ty_ctx.clone();
    let mut ctx_clone = ExprTyCtx {
        gl_ctx: ctx.gl_ctx,
        ident_exec: ctx.ident_exec,
        kind_ctx: &mut *ctx.kind_ctx,
        exec: ctx.exec.clone(),
        ty_ctx: &mut ty_ctx_clone,
        access_ctx: &mut *ctx.access_ctx,
    };
    let _case_true_ty_ctx = ty_check_expr(&mut ctx_clone, case_true)?;
    ctx.ty_ctx.push_empty_frame();
    ty_check_expr(ctx, case_false)?;
    ctx.ty_ctx.pop_frame();

    let cond_ty = cond.ty.as_ref().unwrap();
    let case_true_ty = case_true.ty.as_ref().unwrap();
    let case_false_ty = case_false.ty.as_ref().unwrap();

    if !matches_dty!(
        cond_ty,
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
        case_true_ty,
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
        case_false_ty,
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

    Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
        DataTyKind::Scalar(ScalarTy::Unit),
    )))))
}

fn ty_check_if(ctx: &mut ExprTyCtx, cond: &mut Expr, case_true: &mut Expr) -> TyResult<Ty> {
    // TODO deal with provenances in cases
    ty_check_expr(ctx, cond)?;
    ctx.ty_ctx.push_empty_frame();
    ty_check_expr(ctx, case_true)?;
    ctx.ty_ctx.pop_frame();

    let cond_ty = cond.ty.as_ref().unwrap();
    let case_true_ty = case_true.ty.as_ref().unwrap();

    if !matches_dty!(
        cond_ty,
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
        case_true_ty,
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

    Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
        DataTyKind::Scalar(ScalarTy::Unit),
    )))))
}

fn ty_check_indep(ctx: &mut ExprTyCtx, indep: &mut Indep) -> TyResult<Ty> {
    exec::ty_check(
        ctx.kind_ctx,
        ctx.ty_ctx,
        ctx.ident_exec,
        &mut indep.split_exec,
    )?;
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

    for i in 0..indep.branch_bodies.len() {
        let mut branch_exec = ExecExpr::new(ctx.exec.exec.clone().split_proj(
            indep.dim_compo,
            indep.pos.clone(),
            i as u8,
        ));
        exec::ty_check(
            &ctx.kind_ctx,
            &ctx.ty_ctx,
            &ctx.ident_exec,
            &mut branch_exec,
        )?;
        let mut branch_expr_ty_ctx = ExprTyCtx {
            gl_ctx: ctx.gl_ctx,
            ident_exec: ctx.ident_exec,
            kind_ctx: &mut *ctx.kind_ctx,
            exec: branch_exec.clone(),
            ty_ctx: &mut *ctx.ty_ctx,
            access_ctx: &mut *ctx.access_ctx,
        };
        branch_expr_ty_ctx
            .ty_ctx
            .push_empty_frame()
            .append_exec_mapping(indep.branch_idents[i].clone(), branch_exec.clone());
        ty_check_expr(&mut branch_expr_ty_ctx, &mut indep.branch_bodies[i])?;
        if indep.branch_bodies[i].ty.as_ref().unwrap().ty
            != TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::Unit))))
        {
            return Err(TyError::String(
                "A par_branch branch must not return a value.".to_string(),
            ));
        }
        branch_expr_ty_ctx.ty_ctx.pop_frame();
    }
    Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
        DataTyKind::Scalar(ScalarTy::Unit),
    )))))
}

fn ty_check_sched(ctx: &mut ExprTyCtx, sched: &mut Sched) -> TyResult<Ty> {
    exec::ty_check(
        ctx.kind_ctx,
        ctx.ty_ctx,
        ctx.ident_exec,
        &mut sched.sched_exec,
    )?;
    let mut body_exec = ExecExpr::new(ctx.exec.exec.clone().distrib(sched.dim));
    exec::ty_check(&ctx.kind_ctx, &ctx.ty_ctx, &ctx.ident_exec, &mut body_exec)?;
    let mut schedule_body_ctx = ExprTyCtx {
        gl_ctx: ctx.gl_ctx,
        ident_exec: ctx.ident_exec,
        kind_ctx: &mut *ctx.kind_ctx,
        exec: body_exec.clone(),
        ty_ctx: &mut *ctx.ty_ctx,
        access_ctx: &mut *ctx.access_ctx,
    };
    schedule_body_ctx.ty_ctx.push_empty_frame();
    for prv in &sched.body.prvs {
        schedule_body_ctx
            .ty_ctx
            .append_prv_mapping(PrvMapping::new(prv));
    }
    ty_check_expr(&mut schedule_body_ctx, &mut sched.body.body)?;
    schedule_body_ctx.ty_ctx.pop_frame();
    Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
        DataTyKind::Scalar(ScalarTy::Unit),
    )))))
}

fn ty_check_lambda(
    ctx: &mut ExprTyCtx,
    params: &mut [ParamDecl],
    lambda_ident_exec: &IdentExec,
    ret_dty: &DataTy,
    body: &mut Expr,
) -> TyResult<Ty> {
    // Build frame typing for this function
    let mut fun_frame = Frame::new();
    fun_frame.append_idents_typed(
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
                exec: ExecExpr::new(Exec::new(BaseExec::Ident(lambda_ident_exec.ident.clone()))),
            })
            .collect(),
    );
    // Copy porvenance mappings into scope and append scope frame.
    // FIXME check that no variables are captured.
    // let compare_ctx = ctx.ty_ctx.clone();
    ctx.ty_ctx.push_frame(fun_frame);
    let mut body_exec = ExecExpr::new(Exec::new(BaseExec::Ident(lambda_ident_exec.ident.clone())));
    exec::ty_check(
        &ctx.kind_ctx,
        &ctx.ty_ctx,
        lambda_ident_exec,
        &mut body_exec,
    )?;
    ctx.ty_ctx
        .append_exec_mapping(lambda_ident_exec.ident.clone(), body_exec.clone());
    let mut access_ctx = ExprTyCtx {
        gl_ctx: ctx.gl_ctx,
        ident_exec: ctx.ident_exec,
        kind_ctx: ctx.kind_ctx,
        exec: body_exec,
        ty_ctx: &mut *ctx.ty_ctx,
        access_ctx: &mut AccessCtx::new(),
    };
    ty_check_expr(&mut access_ctx, body)?;
    ctx.ty_ctx.pop_frame();
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
    let mut empty_ty_ctx = TyCtx::new();
    subty::check(
        ctx.kind_ctx,
        &mut empty_ty_ctx,
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

    Ok(fun_ty)
}

fn ty_check_block(ctx: &mut ExprTyCtx, block: &mut Block) -> TyResult<Ty> {
    ctx.ty_ctx.push_empty_frame();
    for prv in &block.prvs {
        ctx.ty_ctx.append_prv_mapping(PrvMapping::new(prv));
    }
    ty_check_expr(ctx, &mut block.body)?;
    ctx.ty_ctx.pop_frame();
    Ok(block.body.ty.as_ref().unwrap().as_ref().clone())
}

fn collect_valid_loans(ty_ctx: &TyCtx, mut loans: HashSet<Loan>) -> HashSet<Loan> {
    // FIXME this implementations assumes unique names which is not the case
    loans.retain(|l| {
        let root_ident = &l.place_expr.to_pl_ctx_and_most_specif_pl().1.ident;
        ty_ctx.contains(root_ident)
    });
    loans
}

fn check_mutable(ty_ctx: &TyCtx, pl: &Place) -> TyResult<()> {
    let ident_ty = ty_ctx.ident_ty(&pl.ident)?;
    if ident_ty.mutbl != Mutability::Mut {
        return Err(TyError::AssignToConst(pl.to_place_expr()));
    }
    Ok(())
}

fn ty_check_assign_place(ctx: &mut ExprTyCtx, pl_expr: &PlaceExpr, e: &mut Expr) -> TyResult<Ty> {
    ty_check_expr(ctx, e)?;
    let pl = pl_expr.to_place().unwrap();
    let mut place_ty = ctx.ty_ctx.place_dty(&pl)?;
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
    check_mutable(&ctx.ty_ctx, &pl)?;

    // If the place is not dead, check that it is safe to use, otherwise it is safe to use anyway.
    if !matches!(&place_ty.dty, DataTyKind::Dead(_),) {
        let potential_accesses = borrow_check::ownership_safe(
            &BorrowCheckCtx::new(ctx, vec![], Ownership::Uniq),
            pl_expr,
        )
        .map_err(|err| {
            TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Uniq, err)
        })?;
        ctx.access_ctx.insert(&ctx.exec, potential_accesses);
    }

    let e_dty = if let TyKind::Data(dty) = &mut e.ty.as_mut().unwrap().as_mut().ty {
        dty.as_mut()
    } else {
        return Err(TyError::UnexpectedType);
    };
    let err = unify::sub_unify(ctx.kind_ctx, ctx.ty_ctx, e_dty, &mut place_ty);
    if let Err(err) = err {
        return Err(match err {
            UnifyError::CannotUnify => {
                TyError::MismatchedDataTypes(place_ty.clone(), e_dty.clone(), e.clone())
            }
            err => TyError::from(err),
        });
    }
    ctx.ty_ctx
        .set_place_dty(&pl, e_dty.clone())
        .without_reborrow_loans(pl_expr);
    Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
        DataTyKind::Scalar(ScalarTy::Unit),
    )))))
}

fn ty_check_assign_deref(
    ctx: &mut ExprTyCtx,
    deref_expr: &mut PlaceExpr,
    e: &mut Expr,
) -> TyResult<Ty> {
    ty_check_expr(ctx, e)?;
    pl_expr::ty_check(&PlExprTyCtx::new(ctx, Ownership::Uniq), deref_expr)?;
    let potential_accesses = borrow_check::ownership_safe(
        &BorrowCheckCtx::new(ctx, vec![], Ownership::Uniq),
        deref_expr,
    )
    .map_err(|err| {
        TyError::ConflictingBorrow(Box::new(deref_expr.clone()), Ownership::Uniq, err)
    })?;
    ctx.access_ctx.insert(&ctx.exec, potential_accesses);
    let deref_ty = deref_expr.ty.as_mut().unwrap();
    unify::sub_unify(
        ctx.kind_ctx,
        ctx.ty_ctx,
        e.ty.as_mut().unwrap().as_mut(),
        deref_ty,
    )?;
    if !deref_ty.is_fully_alive() {
        return Err(TyError::String(
            "Trying to assign through reference, to a type which is not fully alive.".to_string(),
        ));
    }
    // FIXME needs subtyping check on p, e types
    if let TyKind::Data(_) = &deref_ty.ty {
        Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
            DataTyKind::Scalar(ScalarTy::Unit),
        )))))
    } else {
        Err(TyError::String(
            "Trying to dereference view type which is not allowed.".to_string(),
        ))
    }
}

fn ty_check_idx_assign(
    ctx: &mut ExprTyCtx,
    pl_expr: &mut PlaceExpr,
    idx: &Nat,
    e: &mut Expr,
) -> TyResult<Ty> {
    if &ctx.ident_exec.ty.ty != &ExecTyKind::CpuThread
        && &ctx.ident_exec.ty.ty != &ExecTyKind::GpuThread
    {
        return Err(TyError::String(format!(
            "Trying to assign to memory from {:?}.",
            &ctx.ident_exec.ty.ty
        )));
    }
    ty_check_expr(ctx, e)?;
    pl_expr::ty_check(&PlExprTyCtx::new(ctx, Ownership::Uniq), pl_expr)?;
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
            "Trying to assign through reference, to a type which is not fully alive.".to_string(),
        ));
    }
    accessible_memory(ctx.exec.ty.as_ref().unwrap().as_ref(), &mem)?;
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
    let potential_accesses =
        borrow_check::ownership_safe(&BorrowCheckCtx::new(ctx, vec![], Ownership::Uniq), pl_expr)
            .map_err(|err| {
            TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Shrd, err)
        })?;
    ctx.access_ctx.insert(&ctx.exec, potential_accesses);
    subty::check(ctx.kind_ctx, ctx.ty_ctx, e.ty.as_ref().unwrap().dty(), dty)?;
    Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
        DataTyKind::Scalar(ScalarTy::Unit),
    )))))
}

// FIXME currently assumes that binary operators exist only for f32 and i32 and that both
//  arguments have to be of the same type
fn ty_check_binary_op(
    ctx: &mut ExprTyCtx,
    bin_op: &BinOp,
    lhs: &mut Expr,
    rhs: &mut Expr,
) -> TyResult<Ty> {
    // FIXME certain operations should only be allowed for certain data types
    //      true > false is currently valid
    ty_check_expr(ctx, lhs)?;
    ty_check_expr(ctx, rhs)?;
    let lhs_ty = lhs.ty.as_ref().unwrap();
    let rhs_ty = rhs.ty.as_ref().unwrap();
    let ret = match bin_op {
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod | BinOp::And | BinOp::Or => {
            lhs_ty.as_ref().clone()
        }
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
                ) => Ok(ret),
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
fn ty_check_unary_op(ctx: &mut ExprTyCtx, un_op: &UnOp, e: &mut Expr) -> TyResult<Ty> {
    ty_check_expr(ctx, e)?;
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
        } => Ok(e_ty.as_ref().clone()),
        _ => Err(TyError::String(format!(
            "Exected a number type (i.e., f32 or i32), but found {:?}",
            e_ty
        ))),
    }
}

fn ty_check_app(
    ctx: &mut ExprTyCtx,
    ef: &mut Expr,
    k_args: &mut Vec<ArgKinded>,
    args: &mut [Expr],
) -> TyResult<Ty> {
    // TODO check well-kinded: FrameTyping, Prv, Ty
    let (f_remain_gen_args, f_subst_param_tys, f_subst_exec_level, f_subst_ret_ty, mut f_mono_ty) =
        ty_check_dep_app(ctx, ef, k_args)?;
    let exec_f = if let TyKind::FnTy(fn_ty) = &ef.ty.as_ref().unwrap().ty {
        if !callable_in(&fn_ty.exec_ty, ctx.exec.ty.as_ref().unwrap()) {
            return Err(TyError::String(format!(
                "Trying to apply function for execution resource `{:?}` \
                under execution resource `{:?}`",
                &fn_ty.exec_ty,
                &ctx.exec.ty.as_ref().unwrap()
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
        ty_check_expr(ctx, arg)?;
    }
    let ret_dty = Ty::new(TyKind::Data(Box::new(DataTy::new(utils::fresh_ident(
        "ret_ty",
        DataTyKind::Ident,
    )))));
    unify::unify(
        &mut FnTy::new(
            vec![],
            args.iter()
                .map(|arg| arg.ty.as_ref().unwrap().as_ref().clone())
                .collect(),
            exec_f,
            ret_dty,
        ),
        &mut f_mono_ty,
    )?;
    let mut inferred_k_args = infer_kinded_args::infer_kinded_args_from_mono_ty(
        f_remain_gen_args,
        f_subst_param_tys,
        &f_subst_exec_level,
        &f_subst_ret_ty,
        &f_mono_ty,
    );
    k_args.append(&mut inferred_k_args);

    // TODO check provenance relations
    return Ok(f_mono_ty.ret_ty.as_ref().clone());
}

fn ty_check_dep_app(
    ctx: &mut ExprTyCtx,
    ef: &mut Expr,
    k_args: &mut [ArgKinded],
) -> TyResult<(Vec<IdentKinded>, Vec<Ty>, ExecTy, Ty, FnTy)> {
    ty_check_expr(ctx, ef)?;
    if let TyKind::FnTy(fn_ty) = &ef.ty.as_ref().unwrap().ty {
        if fn_ty.generics.len() < k_args.len() {
            return Err(TyError::String(format!(
                "Wrong amount of generic arguments. Expected {}, found {}",
                fn_ty.generics.len(),
                k_args.len()
            )));
        }
        for (gp, kv) in fn_ty.generics.iter().zip(&*k_args) {
            check_arg_has_correct_kind(&ctx.kind_ctx, &gp.kind, kv)?;
        }
        let mut subst_param_tys = fn_ty.param_tys.clone();
        for ty in &mut subst_param_tys {
            utils::subst_idents_kinded(fn_ty.generics.iter(), k_args.iter(), ty);
        }
        let mut subst_exec_level = fn_ty.exec_ty.clone();
        utils::subst_idents_kinded(fn_ty.generics.iter(), k_args.iter(), &mut subst_exec_level);
        let mut subst_out_ty = fn_ty.ret_ty.as_ref().clone();
        utils::subst_idents_kinded(fn_ty.generics.iter(), k_args.iter(), &mut subst_out_ty);
        let mono_fun_ty = unify::inst_fn_ty_scheme(
            &fn_ty.generics[k_args.len()..],
            &subst_param_tys,
            &fn_ty.exec_ty,
            &subst_out_ty,
        )?;
        Ok((
            fn_ty.generics[k_args.len()..].to_vec(),
            subst_param_tys,
            subst_exec_level,
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

fn check_arg_has_correct_kind(kind_ctx: &KindCtx, expected: &Kind, kv: &ArgKinded) -> TyResult<()> {
    if expected == &kv.kind() {
        Ok(())
    } else {
        Err(TyError::String(format!(
            "expected argument of kind {:?}, but the provided argument is {:?}",
            expected, kv
        )))
    }
}

fn ty_check_app_kernel(ctx: &mut ExprTyCtx, app_kernel: &mut AppKernel) -> TyResult<Ty> {
    // current exec = cpu.thread
    if !matches!(ctx.exec.ty.as_ref().unwrap().ty, ExecTyKind::CpuThread) {
        return Err(TyError::String(
            "A kernel must be called from a CPU thread.".to_string(),
        ));
    }
    // type check argument list
    for arg in app_kernel.args.iter_mut() {
        ty_check_expr(ctx, arg)?;
    }
    // new scope with gpu.grid<DIM, DIM> execution resource
    let mut kernel_ctx = ExprTyCtx {
        gl_ctx: ctx.gl_ctx,
        ident_exec: ctx.ident_exec,
        kind_ctx: ctx.kind_ctx,
        exec: ExecExpr::new(Exec::new(BaseExec::GpuGrid(
            app_kernel.grid_dim.clone(),
            app_kernel.block_dim.clone(),
        ))),
        ty_ctx: &mut *ctx.ty_ctx,
        access_ctx: &mut AccessCtx::new(),
    };
    exec::ty_check(
        &kernel_ctx.kind_ctx,
        &kernel_ctx.ty_ctx,
        &kernel_ctx.ident_exec,
        &mut kernel_ctx.exec,
    )?;
    // add explicit provenances to typing context (see ty_check_block)
    for prv in &app_kernel.shared_mem_prvs {
        kernel_ctx.ty_ctx.append_prv_mapping(PrvMapping::new(prv));
    }
    // generate internal shared memory identifier with provided dtys @ shared
    let shared_mem_idents_ty = app_kernel
        .shared_mem_dtys
        .iter()
        .map(|dty| {
            IdentTyped::new(
                Ident::new_impli(&utils::fresh_name("shared_mem")),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::At(
                    Box::new(dty.clone()),
                    Memory::GpuShared,
                ))))),
                Mutability::Mut,
                kernel_ctx.exec.clone(),
            )
        })
        .collect::<Vec<_>>();
    // and add shared mem idents to scope
    for it in &shared_mem_idents_ty {
        kernel_ctx.ty_ctx.append_ident_typed(it.clone());
    }
    // references to shared memory identifiers
    let mut refs_to_shrd = shared_mem_idents_ty
        .iter()
        .enumerate()
        .map(|(i, idt)| {
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
        })
        .collect::<Vec<_>>();
    for shrd_mem_arg in refs_to_shrd.iter_mut() {
        ty_check_expr(&mut kernel_ctx, shrd_mem_arg)?;
    }
    // create extended argument list with references to shared memory
    let extended_arg_tys = app_kernel
        .args
        .iter()
        .map(|a| a.ty.as_ref().unwrap().as_ref())
        .cloned()
        .chain(refs_to_shrd.into_iter().map(|a| *a.ty.unwrap()))
        .collect::<Vec<_>>();
    // type check function application for generic args and extended argument list
    let (f_remain_gen_args, f_subst_param_tys, f_subst_exec_level, f_subst_ret_ty, mut f_mono_ty) =
        ty_check_dep_app(
            &mut kernel_ctx,
            &mut app_kernel.fun,
            &mut app_kernel.gen_args,
        )?;
    // Get functions execution resource and check that it can be applied (i.e, that it must be
    //   exectuted on an appropriate grid).
    if let TyKind::FnTy(fn_ty) = &app_kernel.fun.ty.as_ref().unwrap().ty {
        if !callable_in(&fn_ty.exec_ty, kernel_ctx.exec.ty.as_ref().unwrap()) {
            return Err(TyError::String(format!(
                "Trying to execute function for {:?} as kernel.",
                &fn_ty.exec_ty,
            )));
        }
    } else {
        return Err(TyError::String(format!(
            "Trying to execute expression which does not have a function type, as kernel, :\n\
                    {:?}\n",
            &app_kernel.fun
        )));
    };
    // build expected type to unify with
    let unit_ty = Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
        ScalarTy::Unit,
    )))));
    unify::unify(
        &mut FnTy::new(
            vec![],
            extended_arg_tys,
            *kernel_ctx.exec.ty.unwrap(),
            unit_ty.clone(),
        ),
        &mut f_mono_ty,
    )?;
    let mut inferred_k_args = infer_kinded_args::infer_kinded_args_from_mono_ty(
        f_remain_gen_args,
        f_subst_param_tys,
        &f_subst_exec_level,
        &f_subst_ret_ty,
        &f_mono_ty,
    );
    app_kernel.gen_args.append(&mut inferred_k_args);
    Ok(unit_ty)
}

fn ty_check_tuple(ctx: &mut ExprTyCtx, elems: &mut [Expr]) -> TyResult<Ty> {
    for elem in elems.iter_mut() {
        ty_check_expr(ctx, elem)?;
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
    Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
        DataTyKind::Tuple(elem_tys?),
    )))))
}

fn ty_check_proj(ctx: &mut ExprTyCtx, e: &mut Expr, i: usize) -> TyResult<Ty> {
    if let ExprKind::PlaceExpr(_) = e.expr {
        panic!("Place expression should have been typechecked by a different rule.")
    }
    ty_check_expr(ctx, e)?;
    let e_dty = if let TyKind::Data(dty) = &e.ty.as_ref().unwrap().ty {
        dty.as_ref()
    } else {
        return Err(TyError::UnexpectedType);
    };
    let elem_ty = proj_elem_dty(e_dty, i);
    Ok(Ty::new(TyKind::Data(Box::new(elem_ty?))))
}

fn ty_check_array(ctx: &mut ExprTyCtx, elems: &mut Vec<Expr>) -> TyResult<Ty> {
    assert!(!elems.is_empty());
    for elem in elems.iter_mut() {
        ty_check_expr(ctx, elem)?;
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
        Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
            DataTyKind::Array(
                Box::new(ty.as_ref().unwrap().dty().clone()),
                Nat::Lit(elems.len()),
            ),
        )))))
    }
}

fn ty_check_literal(l: &mut Lit) -> Ty {
    let scalar_data = match l {
        Lit::Unit => ScalarTy::Unit,
        Lit::Bool(_) => ScalarTy::Bool,
        Lit::I32(_) => ScalarTy::I32,
        Lit::U32(_) => ScalarTy::U32,
        Lit::F32(_) => ScalarTy::F32,
        Lit::F64(_) => ScalarTy::F64,
    };
    Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
        scalar_data,
    )))))
}

fn infer_pattern_ident_tys(
    ty_ctx: &mut TyCtx,
    exec: &ExecExpr,
    pattern: &Pattern,
    pattern_ty: &Ty,
) -> TyResult<()> {
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
                exec.clone(),
            );
            ty_ctx.append_ident_typed(ident_with_annotated_ty);
            Ok(())
        }
        (Pattern::Wildcard, _) => Ok(()),
        (Pattern::Tuple(patterns), DataTyKind::Tuple(elem_tys)) => {
            for (p, tty) in patterns.iter().zip(elem_tys) {
                infer_pattern_ident_tys(
                    ty_ctx,
                    exec,
                    p,
                    &Ty::new(TyKind::Data(Box::new(tty.clone()))),
                )?;
            }
            Ok(())
        }
        _ => Err(TyError::PatternAndTypeDoNotMatch),
    }
}

fn infer_tys_and_append_idents(
    kind_ctx: &KindCtx,
    ty_ctx: &mut TyCtx,
    exec: &ExecExpr,
    pattern: &Pattern,
    pattern_ty: &mut Option<Box<Ty>>,
    assign_ty: &mut Ty,
) -> TyResult<()> {
    let pattern_ty = if let Some(pty) = pattern_ty {
        unify::sub_unify(kind_ctx, ty_ctx, assign_ty, pty)?;
        pty.as_ref().clone()
    } else {
        assign_ty.clone()
    };
    infer_pattern_ident_tys(ty_ctx, exec, pattern, &pattern_ty)
}

fn ty_check_let(
    ctx: &mut ExprTyCtx,
    pattern: &Pattern,
    pattern_ty: &mut Option<Box<Ty>>,
    expr: &mut Expr,
) -> TyResult<Ty> {
    ty_check_expr(ctx, expr)?;
    let e_ty = expr.ty.as_mut().unwrap();
    infer_tys_and_append_idents(
        ctx.kind_ctx,
        ctx.ty_ctx,
        &ctx.exec,
        pattern,
        pattern_ty,
        e_ty,
    )?;
    Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
        DataTyKind::Scalar(ScalarTy::Unit),
    )))))
}

// TODO respect exec?
fn ty_check_let_uninit(ctx: &mut ExprTyCtx, ident: &Ident, ty: &Ty) -> TyResult<Ty> {
    // TODO is the type well-formed?
    if let TyKind::Data(dty) = &ty.ty {
        let ident_with_ty = IdentTyped::new(
            ident.clone(),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Dead(
                dty.clone(),
            ))))),
            Mutability::Mut,
            ctx.exec.clone(),
        );
        ctx.ty_ctx.append_ident_typed(ident_with_ty);
        Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
            DataTyKind::Scalar(ScalarTy::Unit),
        )))))
    } else {
        Err(TyError::MutabilityNotAllowed(ty.clone()))
    }
}

fn ty_check_seq(ctx: &mut ExprTyCtx, es: &mut [Expr]) -> TyResult<Ty> {
    for e in &mut *es {
        ty_check_expr(ctx, e)?;
        ctx.ty_ctx.garbage_collect_loans();
    }
    Ok(es.last().unwrap().ty.as_ref().unwrap().as_ref().clone())
}

fn ty_check_pl_expr_with_deref(ctx: &mut ExprTyCtx, pl_expr: &mut PlaceExpr) -> TyResult<Ty> {
    pl_expr::ty_check(&PlExprTyCtx::new(ctx, Ownership::Shrd), pl_expr)?;
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
    let potential_accesses =
        borrow_check::ownership_safe(&BorrowCheckCtx::new(ctx, vec![], Ownership::Shrd), pl_expr)
            .map_err(|err| {
            TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Shrd, err)
        })?;
    ctx.access_ctx.insert(&ctx.exec, potential_accesses);
    if pl_expr.ty.as_ref().unwrap().copyable() {
        Ok(pl_expr.ty.as_ref().unwrap().as_ref().clone())
    } else {
        Err(TyError::String("Data type is not copyable.".to_string()))
    }
}

fn ty_check_pl_expr_without_deref(ctx: &mut ExprTyCtx, pl_expr: &PlaceExpr) -> TyResult<Ty> {
    let place = pl_expr.to_place().unwrap();
    // If place is an identifier referring to a globally declared function
    let pl_ty = if let Ok(fun_ty) = ctx.gl_ctx.fn_ty_by_ident(&place.ident) {
        Ty::new(TyKind::FnTy(Box::new(fun_ty.clone())))
    } else {
        // If place is NOT referring to a globally declared function
        let pl_ty = ctx.ty_ctx.place_dty(&place)?;
        if !pl_ty.is_fully_alive() {
            return Err(TyError::String(format!(
                "Part of Place {:?} was moved before.",
                pl_expr
            )));
        }
        if pl_ty.copyable() {
            // TODO refactor
            let potential_accesses = borrow_check::ownership_safe(
                &BorrowCheckCtx::new(ctx, vec![], Ownership::Shrd),
                pl_expr,
            )
            .map_err(|err| {
                TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Shrd, err)
            })?;
            ctx.access_ctx.insert(&ctx.exec, potential_accesses);
        } else {
            let potential_accesses = borrow_check::ownership_safe(
                &BorrowCheckCtx::new(ctx, vec![], Ownership::Uniq),
                pl_expr,
            )
            .map_err(|err| {
                TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Uniq, err)
            })?;
            ctx.access_ctx.insert(&ctx.exec, potential_accesses);
            ctx.ty_ctx.kill_place(&place);
        };
        Ty::new(TyKind::Data(Box::new(pl_ty)))
    };
    Ok(pl_ty)
}

fn ty_check_borrow(
    ctx: &mut ExprTyCtx,
    prv_val_name: &Option<String>,
    own: Ownership,
    pl_expr: &mut PlaceExpr,
) -> TyResult<Ty> {
    // If borrowing a place uniquely, is it mutable?
    if let Some(place) = pl_expr.to_place() {
        if own == Ownership::Uniq && ctx.ty_ctx.ident_ty(&place.ident)?.mutbl == Mutability::Const {
            return Err(TyError::ConstBorrow(pl_expr.clone()));
        }
    }
    let prv_val_name = infer_and_append_prv(ctx.ty_ctx, prv_val_name);
    if !ctx.ty_ctx.loans_in_prv(&prv_val_name)?.is_empty() {
        return Err(TyError::PrvValueAlreadyInUse(prv_val_name));
    }
    let mems = pl_expr::ty_check_and_passed_mems(&PlExprTyCtx::new(ctx, own), pl_expr)?;
    let loans = borrow_check::ownership_safe(&BorrowCheckCtx::new(ctx, vec![], own), pl_expr)
        .map_err(|err| TyError::ConflictingBorrow(Box::new(pl_expr.clone()), own, err))?;
    mems.iter()
        .try_for_each(|mem| accessible_memory(ctx.exec.ty.as_ref().unwrap().as_ref(), mem))?;
    let pl_expr_ty = pl_expr.ty.as_ref().unwrap();
    if !pl_expr_ty.is_fully_alive() {
        return Err(TyError::String(
            "The place was at least partially moved before.".to_string(),
        ));
    }
    let (reffed_ty, rmem) = match &pl_expr_ty.ty {
        TyKind::Data(dty) => match &dty.dty {
            DataTyKind::Dead(_) => panic!("Cannot happen because of the alive check."),
            DataTyKind::At(inner_ty, m) => (inner_ty.as_ref().clone(), m.clone()),
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
        TyKind::FnTy(_) => return Err(TyError::String("Trying to borrow a function.".to_string())),
    };
    if rmem == Memory::GpuLocal {
        return Err(TyError::String(
            "Trying to take reference of unaddressable gpu.local memory.".to_string(),
        ));
    }
    let res_dty = DataTy::new(DataTyKind::Ref(Box::new(RefDty::new(
        Provenance::Value(prv_val_name.clone()),
        own,
        rmem,
        reffed_ty,
    ))));
    ctx.ty_ctx.extend_loans_for_prv(&prv_val_name, loans)?;
    Ok(Ty::new(TyKind::Data(Box::new(res_dty))))
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

pub fn accessible_memory(exec_ty: &ExecTy, mem: &Memory) -> TyResult<()> {
    if allowed_mem_for_exec(&exec_ty.ty).contains(mem) {
        Ok(())
    } else {
        Err(TyError::String(format!(
            "Trying to dereference pointer to `{:?}` from execution resource `{:?}`",
            mem, &exec_ty.ty
        )))
    }
}

// TODO respect memory
fn ty_well_formed(kind_ctx: &KindCtx, ty_ctx: &TyCtx, exec_ty: &ExecTy, ty: &Ty) -> TyResult<()> {
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
                                if let TyKind::Data(pl_expr_dty) = borrowed_pl_expr.ty.unwrap().ty {
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
                        ty_well_formed(kind_ctx, ty_ctx, exec_ty, &elem_ty)?;
                    }
                    Provenance::Ident(ident) => {
                        let elem_ty = Ty::new(TyKind::Data(reff.dty.clone()));
                        if !kind_ctx.ident_of_kind_exists(ident, Kind::Provenance) {
                            Err(CtxError::KindedIdentNotFound(ident.clone()))?
                        }
                        ty_well_formed(kind_ctx, ty_ctx, exec_ty, &elem_ty)?;
                    }
                };
            }
            DataTyKind::Tuple(elem_dtys) => {
                for elem_dty in elem_dtys {
                    ty_well_formed(
                        kind_ctx,
                        ty_ctx,
                        exec_ty,
                        &Ty::new(TyKind::Data(Box::new(elem_dty.clone()))),
                    )?;
                }
            }
            DataTyKind::Array(elem_dty, n) => {
                ty_well_formed(
                    kind_ctx,
                    ty_ctx,
                    exec_ty,
                    &Ty::new(TyKind::Data(elem_dty.clone())),
                )?;
                // TODO well-formed nat
            }
            DataTyKind::ArrayShape(elem_dty, n) => {
                ty_well_formed(
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
                ty_well_formed(
                    kind_ctx,
                    ty_ctx,
                    exec_ty,
                    &Ty::new(TyKind::Data(elem_dty.clone())),
                )?;
            }
            DataTyKind::At(elem_dty, _) => {
                ty_well_formed(
                    kind_ctx,
                    ty_ctx,
                    exec_ty,
                    &Ty::new(TyKind::Data(elem_dty.clone())),
                )?;
            }
        },
        // TODO check well-formedness of Nats
        TyKind::FnTy(fn_ty) => {
            let mut extended_kind_ctx = kind_ctx.clone();
            extended_kind_ctx.append_idents(fn_ty.generics.clone());
            ty_well_formed(&extended_kind_ctx, ty_ctx, exec_ty, &fn_ty.ret_ty)?;
            for param_ty in &fn_ty.param_tys {
                ty_well_formed(&extended_kind_ctx, ty_ctx, exec_ty, param_ty)?;
            }
        }
    }
    Ok(())
}

pub fn callable_in(callee_exec_ty: &ExecTy, caller_exec_ty: &ExecTy) -> bool {
    if &callee_exec_ty.ty == &ExecTyKind::View {
        true
    } else {
        let res = unify::unify(&mut callee_exec_ty.clone(), &mut caller_exec_ty.clone());
        res.is_ok()
    }
}

// TODO move into utility module (also used in codegen)
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
