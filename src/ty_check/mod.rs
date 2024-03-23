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
use crate::ast::printer::PrintState;
use crate::ty_check::borrow_check::BorrowCheckCtx;
use crate::ty_check::ctxs::GlobalDecl;
pub(crate) use matches_dty;

// ∀ε ∈ Σ. Σ ⊢ ε
// --------------
//      ⊢ Σ
pub fn ty_check(compil_unit: &mut CompilUnit) -> Result<(), ErrorReported> {
    let mut gl_ctx = GlobalCtx::new(
        compil_unit,
        pre_decl::fun_decls()
            .into_iter()
            .map(|(fname, fty)| GlobalDecl::FnDecl(Box::from(fname), Box::new(fty)))
            .collect(),
    );
    let mut nat_ctx = NatCtx::new();
    if let Some(main_fun) = gl_ctx.find_fun("main") {
        let mut main_fun = main_fun.clone();
        ty_check_global_fun_def(&mut gl_ctx, &mut nat_ctx, &mut main_fun).map_err(|err| {
            err.emit(compil_unit.source);
            ErrorReported
        })
    } else {
        TyError::MissingMain.emit(compil_unit.source);
        Err(ErrorReported)
    }
    // ty_check_compil_unit(&gl_ctx, compil_unit).map_err(|err| {
    //     err.emit(compil_unit.source);
    //     ErrorReported
    // })
}

// fn ty_check_compil_unit(gl_ctx: &GlobalCtx, compil_unit: &mut CompilUnit) -> TyResult<()> {
//     let errs =
//         compil_unit
//             .items
//             .iter_mut()
//             .fold(Vec::<TyError>::new(), |mut errors, fun| match fun {
//                 Item::FunDef(fun) => match ty_check_global_fun_def(gl_ctx, fun) {
//                     Ok(()) => errors,
//                     Err(err) => {
//                         errors.push(err);
//                         errors
//                     }
//                 },
//                 _ => errors,
//             });
//     if errs.is_empty() {
//         Ok(())
//     } else {
//         Err(errs.into_iter().collect::<TyError>())
//     }
// }

struct ExprTyCtx<'gl, 'ctxt> {
    gl_ctx: &'ctxt mut GlobalCtx<'gl>,
    nat_ctx: &'ctxt mut NatCtx,
    ident_exec: Option<&'ctxt IdentExec>,
    kind_ctx: &'ctxt mut KindCtx,
    exec: ExecExpr,
    ty_ctx: &'ctxt mut TyCtx,
    access_ctx: &'ctxt mut AccessCtx,
    unsafe_flag: bool,
}

// Σ ⊢ fn f <List[φ], List[ρ], List[α]> (x1: τ1, ..., xn: τn) → τr where List[ρ1:ρ2] { e }
fn ty_check_global_fun_def(
    gl_ctx: &mut GlobalCtx,
    nat_ctx: &mut NatCtx,
    gf: &mut FunDef,
) -> TyResult<()> {
    // TODO check that every prv_rel only uses provenance variables bound in generic_params
    let mut kind_ctx = KindCtx::gl_fun_kind_ctx(gf.generic_params.clone(), gf.prv_rels.clone())?;
    let mut ty_ctx = TyCtx::new();
    // Build frame typing for this function
    // TODO give Frame its own type and move this into frame and/or ParamDecl
    if let Some(ident_exec) = &gf.generic_exec {
        let mut exec_ident =
            ExecExpr::new(ExecExprKind::new(BaseExec::Ident(ident_exec.ident.clone())));
        exec::ty_check(nat_ctx, &ty_ctx, gf.generic_exec.as_ref(), &mut exec_ident)?;
        ty_ctx.append_exec_mapping(ident_exec.ident.clone(), exec_ident);
    }
    exec::ty_check(nat_ctx, &ty_ctx, gf.generic_exec.as_ref(), &mut gf.exec)?;

    let param_idents_ty = gf
        .param_decls
        .iter()
        .map(
            |ParamDecl {
                 ident,
                 ty,
                 mutbl,
                 exec_expr,
             }| {
                let mut exec = exec_expr.as_ref().unwrap_or(&gf.exec).clone();
                exec::ty_check(nat_ctx, &ty_ctx, gf.generic_exec.as_ref(), &mut exec)?;
                Ok(IdentTyped {
                    ident: ident.clone(),
                    ty: ty.as_ref().unwrap().clone(),
                    exec,
                    mutbl: *mutbl,
                })
            },
        )
        .collect::<TyResult<Vec<_>>>()?;
    for pi in param_idents_ty {
        ty_ctx.append_ident_typed(pi);
    }
    for prv in &gf.body.prvs {
        ty_ctx.append_prv_mapping(PrvMapping::new(prv));
    }

    let mut access_ctx = AccessCtx::new();
    let mut ctx = ExprTyCtx {
        gl_ctx: &mut *gl_ctx,
        nat_ctx: &mut *nat_ctx,
        kind_ctx: &mut kind_ctx,
        ident_exec: gf.generic_exec.as_ref(),
        exec: gf.exec.clone(),
        ty_ctx: &mut ty_ctx,
        access_ctx: &mut access_ctx,
        unsafe_flag: false,
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
                ty_check_place(ctx, pl_expr)?
            } else {
                ty_check_non_place(ctx, pl_expr)?
            }
        }
        ExprKind::Block(block) => ty_check_block(ctx, block)?,
        ExprKind::Let(pattern, ty, e) => ty_check_let(ctx, pattern, ty, e)?,
        ExprKind::LetUninit(annot_exec, ident, ty) => {
            ty_check_let_uninit(ctx, annot_exec, ident, ty)?
        }
        ExprKind::Seq(es) => ty_check_seq(ctx, es)?,
        ExprKind::Lit(l) => ty_check_literal(l),
        ExprKind::Array(elems) => ty_check_array(ctx, elems)?,
        ExprKind::Tuple(elems) => ty_check_tuple(ctx, elems)?,
        // ExprKind::Proj(e, i) => ty_check_proj(ctx, e, *i)?,
        ExprKind::App(fn_ident, gen_args, args) => ty_check_app(ctx, fn_ident, gen_args, args)?,
        ExprKind::DepApp(fn_ident, gen_args) => Ty::new(TyKind::FnTy(Box::new(ty_check_dep_app(
            ctx, fn_ident, gen_args,
        )?))),
        ExprKind::AppKernel(app_kernel) => ty_check_app_kernel(ctx, app_kernel)?,
        ExprKind::Ref(prv, own, pl_expr) => ty_check_borrow(ctx, prv, *own, pl_expr)?,
        ExprKind::Assign(pl_expr, e) => {
            if pl_expr.is_place() {
                ty_check_assign_place(ctx, pl_expr, e)?
            } else {
                ty_check_assign_non_place(ctx, pl_expr, e)?
            }
        }
        ExprKind::IdxAssign(pl_expr, idx, e) => ty_check_idx_assign(ctx, pl_expr, idx, e)?,
        ExprKind::Split(split) => ty_check_split(ctx, split)?,
        ExprKind::Sched(sched) => ty_check_sched(ctx, sched)?,
        ExprKind::ForNat(var, range, body) => ty_check_for_nat(ctx, var, range, body)?,
        ExprKind::For(ident, collec, body) => ty_check_for(ctx, ident, collec, body)?,
        ExprKind::IfElse(cond, case_true, case_false) => {
            ty_check_if_else(ctx, cond, case_true, case_false)?
        }
        ExprKind::If(cond, case_true) => ty_check_if(ctx, cond, case_true)?,
        ExprKind::While(cond, body) => ty_check_while(ctx, cond, body)?,
        // ExprKind::Lambda(params, lambda_exec_ident, ret_ty, body) => {
        //     ty_check_lambda(ctx, params, lambda_exec_ident, ret_ty, body)?
        // }
        ExprKind::BinOp(bin_op, lhs, rhs) => ty_check_binary_op(ctx, bin_op, lhs, rhs)?,
        ExprKind::UnOp(un_op, e) => ty_check_unary_op(ctx, un_op, e)?,
        ExprKind::Sync(exec) => ty_check_sync(ctx, exec)?,
        ExprKind::Unsafe(e) => {
            ctx.unsafe_flag = true;
            ty_check_expr(ctx, e)?;
            e.ty.as_ref().unwrap().as_ref().clone()
        }
        ExprKind::Cast(expr, dty) => ty_check_cast(ctx, expr, dty)?,
        ExprKind::Range(_, _) => unimplemented!(), //ty_check_range(ctx, l, u)?,
        ExprKind::Hole => ty_check_hole(ctx)?,
    };

    // TODO reintroduce!!!!
    //if let Err(err) = self.ty_well_formed(kind_ctx, &res_ty_ctx, exec, &ty) {
    //    panic!("{:?}", err);
    //}
    expr.ty = Some(Box::new(ty));
    Ok(())
}

fn ty_check_hole(ctx: &ExprTyCtx) -> TyResult<Ty> {
    if ctx.unsafe_flag {
        Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
            DataTyKind::Ident(Ident::new_impli(&utils::fresh_name("hole"))),
        )))))
    } else {
        Err(TyError::UnsafeRequired)
    }
}

fn ty_check_sync(ctx: &mut ExprTyCtx, exec: &mut Option<ExecExpr>) -> TyResult<Ty> {
    let synced = match exec {
        Some(exec) => {
            exec::ty_check(ctx.nat_ctx, ctx.ty_ctx, ctx.ident_exec, exec)?;
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
            if matches!(ep, ExecPathElem::TakeRange(_)) {
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
        ExecTyKind::GpuBlock(_) | ExecTyKind::GpuWarp => true,
        ExecTyKind::CpuThread
        | ExecTyKind::GpuGrid(_, _)
        | ExecTyKind::GpuToThreads(_, _)
        | ExecTyKind::GpuBlockGrp(_, _)
        | ExecTyKind::GpuThreadGrp(_)
        | ExecTyKind::GpuWarpGrp(_)
        | ExecTyKind::GpuThread
        | ExecTyKind::Any => false,
    }
}

// fn ty_check_range(ctx: &mut ExprTyCtx, l: &mut Expr, u: &mut Expr) -> TyResult<Ty> {
//     // FIXME this is wrong and should check that the current exec is legal
//     if &ctx.ident_exec.ty.ty != &ExecTyKind::CpuThread
//         && &ctx.ident_exec.ty.ty != &ExecTyKind::GpuThread
//     {
//         return Err(TyError::IllegalExec);
//     }
//
//     ty_check_expr(ctx, l)?;
//     ty_check_expr(ctx, u)?;
//     if !matches_dty!(
//         l.ty.as_ref().unwrap(),
//         DataTy {
//             dty: DataTyKind::Scalar(ScalarTy::I32),
//             ..
//         }
//     ) {
//         panic!("expected i32 for l in range")
//     }
//
//     if !matches_dty!(
//         &u.ty.as_ref().unwrap(),
//         DataTy {
//             dty: DataTyKind::Scalar(ScalarTy::I32),
//             ..
//         }
//     ) {
//         panic!("expected i32 for u in range")
//     }
//
//     Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
//         DataTyKind::Range,
//     )))))
// }

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
    ident: &Ident,
    range: &NatRange,
    body: &mut Expr,
) -> TyResult<Ty> {
    let compare_ty_ctx = ctx.ty_ctx.clone();
    let lifted_range = range.lift(ctx.nat_ctx)?;

    for i in lifted_range {
        ctx.ty_ctx.push_empty_frame();
        let mut subst_body = body.clone();
        utils::subst_idents_kinded(
            std::iter::once(&IdentKinded::new(ident, Kind::Nat)),
            std::iter::once(&ArgKinded::Nat(Nat::Lit(i))),
            &mut subst_body,
        );
        ty_check_expr(ctx, &mut subst_body)?;
        if let DataTyKind::Scalar(ScalarTy::Unit) = &subst_body.ty.unwrap().dty().dty {
            ctx.ty_ctx.pop_frame();
            if ctx.ty_ctx != &compare_ty_ctx {
                return Err(TyError::String(
                    "Using a data type in loop that can only be used once.".to_string(),
                ));
            }
            ctx.kind_ctx.drop_scope();
        } else {
            return Err(TyError::UnexpectedType);
        }
    }
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
        // DataTyKind::Range => DataTyKind::Scalar(ScalarTy::I32),
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
        ctx.exec.clone(),
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
    ty_check_expr(&mut *ctx, cond)?;
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
        gl_ctx: &mut *ctx.gl_ctx,
        nat_ctx: ctx.nat_ctx,
        ident_exec: ctx.ident_exec,
        kind_ctx: &mut *ctx.kind_ctx,
        exec: ctx.exec.clone(),
        ty_ctx: &mut ty_ctx_clone,
        access_ctx: &mut *ctx.access_ctx,
        unsafe_flag: ctx.unsafe_flag,
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

fn ty_check_split(ctx: &mut ExprTyCtx, indep: &mut Split) -> TyResult<Ty> {
    // exec::ty_check(
    //     ctx.kind_ctx,
    //     ctx.ty_ctx,
    //     ctx.ident_exec,
    //     &mut indep.split_exec,
    // )?;
    exec::ty_check(
        ctx.nat_ctx,
        ctx.ty_ctx,
        ctx.ident_exec,
        &mut indep.split_exec,
    )?;
    legal_exec_under_current(ctx, &indep.split_exec)?;
    let expanded_exec_expr = expand_exec_expr(ctx, &indep.split_exec)?;
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
        let mut branch_exec = ExecExpr::new(expanded_exec_expr.exec.clone().split_proj(
            indep.dim_compo,
            indep.pos.clone(),
            if i == 0 {
                LeftOrRight::Left
            } else if i == 1 {
                LeftOrRight::Right
            } else {
                panic!("Unexepected projection.")
            },
        ));
        exec::ty_check(&ctx.nat_ctx, &ctx.ty_ctx, ctx.ident_exec, &mut branch_exec)?;
        let mut branch_expr_ty_ctx = ExprTyCtx {
            gl_ctx: ctx.gl_ctx,
            nat_ctx: &mut *ctx.nat_ctx,
            ident_exec: ctx.ident_exec,
            kind_ctx: &mut *ctx.kind_ctx,
            exec: branch_exec.clone(),
            ty_ctx: &mut *ctx.ty_ctx,
            access_ctx: &mut *ctx.access_ctx,
            unsafe_flag: ctx.unsafe_flag,
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
        ctx.nat_ctx,
        ctx.ty_ctx,
        ctx.ident_exec,
        &mut sched.sched_exec,
    )?;
    legal_exec_under_current(ctx, &sched.sched_exec)?;
    let expanded_exec_expr = expand_exec_expr(ctx, &sched.sched_exec)?;
    let mut body_exec = ExecExpr::new(expanded_exec_expr.exec.forall(sched.dim));
    exec::ty_check(ctx.nat_ctx, ctx.ty_ctx, ctx.ident_exec, &mut body_exec)?;
    let mut schedule_body_ctx = ExprTyCtx {
        gl_ctx: ctx.gl_ctx,
        nat_ctx: &mut *ctx.nat_ctx,
        ident_exec: ctx.ident_exec,
        kind_ctx: &mut *ctx.kind_ctx,
        exec: body_exec.clone(),
        ty_ctx: &mut *ctx.ty_ctx,
        access_ctx: &mut *ctx.access_ctx,
        unsafe_flag: ctx.unsafe_flag,
    };
    schedule_body_ctx.ty_ctx.push_empty_frame();
    if let Some(ident) = &sched.inner_exec_ident {
        schedule_body_ctx
            .ty_ctx
            .append_exec_mapping(ident.clone(), body_exec.clone());
    };
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

// fn ty_check_lambda(
//     ctx: &mut ExprTyCtx,
//     params: &mut [ParamDecl],
//     lambda_ident_exec: &IdentExec,
//     ret_dty: &DataTy,
//     body: &mut Expr,
// ) -> TyResult<Ty> {
//     // Build frame typing for this function
//     let mut fun_frame = Frame::new();
//     fun_frame.append_idents_typed(
//         params
//             .iter()
//             .map(
//                 |ParamDecl {
//                      ident,
//                      ty,
//                      mutbl,
//                      exec_expr,
//                  }| IdentTyped {
//                     ident: ident.clone(),
//                     ty: match ty {
//                         Some(tty) => tty.clone(),
//                         None => Ty::new(TyKind::Data(Box::new(DataTy::new(utils::fresh_ident(
//                             "param_ty",
//                             DataTyKind::Ident,
//                         ))))),
//                     },
//                     mutbl: *mutbl,
//                     exec: exec_expr.as_ref().unwrap().clone(),
//                 },
//             )
//             .collect(),
//     );
//     // Copy porvenance mappings into scope and append scope frame.
//     // FIXME check that no variables are captured.
//     // let compare_ctx = ctx.ty_ctx.clone();
//     ctx.ty_ctx.push_frame(fun_frame);
//     let mut body_exec = ExecExpr::new(ExecExprKind::new(BaseExec::Ident(
//         lambda_ident_exec.ident.clone(),
//     )));
//     exec::ty_check(
//         &ctx.kind_ctx,
//         &ctx.ty_ctx,
//         lambda_ident_exec,
//         &mut body_exec,
//     )?;
//     ctx.ty_ctx
//         .append_exec_mapping(lambda_ident_exec.ident.clone(), body_exec.clone());
//     let mut access_ctx = ExprTyCtx {
//         gl_ctx: ctx.gl_ctx,
//         ident_exec: ctx.ident_exec,
//         kind_ctx: ctx.kind_ctx,
//         exec: body_exec,
//         ty_ctx: &mut *ctx.ty_ctx,
//         access_ctx: &mut AccessCtx::new(),
//     };
//     ty_check_expr(&mut access_ctx, body)?;
//     ctx.ty_ctx.pop_frame();
//     // FIXME reintroduce after introducing temporary typing context
//     // let no_move_ty_ctx = capture_ty_ctx.clone().drop_last_frame();
//     // if no_move_ty_ctx != ty_ctx {
//     //     // self.ty_check_expr(
//     //     //     kind_ctx,
//     //     //     no_move_ty_ctx,
//     //     //     lambda_ident_exec,
//     //     //     &body_exec,
//     //     //     body,
//     //     // )?;
//     //     panic!(
//     //         "{:?}\n\n\n{:?}\n\n\n{:?}",
//     //         ty_ctx, capture_ty_ctx, no_move_ty_ctx
//     //     );
//     //     return Err(TyError::String(
//     //         "Cannot move values into Lambda.".to_string(),
//     //     ));
//     // }
//
//     // t <= t_f
//     let mut empty_ty_ctx = TyCtx::new();
//     subty::check(
//         ctx.kind_ctx,
//         &mut empty_ty_ctx,
//         body.ty.as_ref().unwrap().dty(),
//         ret_dty,
//     )?;
//
//     assert!(
//         empty_ty_ctx.is_empty(),
//         "Expected typing context to be empty. But TyCtx:\n {:?}",
//         empty_ty_ctx
//     );
//
//     let fun_ty = Ty::new(TyKind::FnTy(Box::new(FnTy::new(
//         vec![],
//         Some(lambda_ident_exec.clone()),
//         params
//             .iter()
//             .map(|decl| {
//                 ParamSig::new(
//                     decl.exec_expr.as_ref().unwrap().clone(),
//                     decl.ty.as_ref().unwrap().clone(),
//                 )
//             })
//             .collect(),
//         ExecExpr::new(ExecExprKind::new(BaseExec::Ident(
//             lambda_ident_exec.ident.clone(),
//         ))),
//         Ty::new(TyKind::Data(Box::new(ret_dty.clone()))),
//     ))));
//
//     Ok(fun_ty)
// }

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

fn ty_check_assign_place(
    ctx: &mut ExprTyCtx,
    pl_expr: &mut PlaceExpr,
    e: &mut Expr,
) -> TyResult<Ty> {
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
    check_mutable(ctx.ty_ctx, &pl)?;

    // If the place is not dead, check that it is safe to use, otherwise it is safe to use anyway.
    if !matches!(&place_ty.dty, DataTyKind::Dead(_),) {
        borrow_check::borrow_check(&BorrowCheckCtx::new(ctx, vec![], Ownership::Uniq), pl_expr)
            .map_err(|err| {
                TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Uniq, err)
            })?;
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
    // TODO remove: not required for correctness
    //  removing this leads to problems in Codegen, because the pl_expr is not annotated with a
    //  type which is required by gen_pl_expr
    pl_expr::ty_check(&PlExprTyCtx::new(ctx, Ownership::Uniq), pl_expr)?;
    Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
        DataTyKind::Scalar(ScalarTy::Unit),
    )))))
}

fn ty_check_assign_non_place(
    ctx: &mut ExprTyCtx,
    deref_expr: &mut PlaceExpr,
    e: &mut Expr,
) -> TyResult<Ty> {
    ty_check_expr(ctx, e)?;
    pl_expr::ty_check(&PlExprTyCtx::new(ctx, Ownership::Uniq), deref_expr)?;
    let potential_accesses = borrow_check::access_safety_check(
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
    if n.eval(ctx.nat_ctx)? <= idx.eval(ctx.nat_ctx)? {
        return Err(TyError::String(
            "Trying to access array out-of-bounds.".to_string(),
        ));
    }
    let potential_accesses = borrow_check::access_safety_check(
        &BorrowCheckCtx::new(ctx, vec![], Ownership::Uniq),
        pl_expr,
    )
    .map_err(|err| TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Shrd, err))?;
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
    let ret_dty = match bin_op {
        BinOp::Add
        | BinOp::Sub
        | BinOp::Mul
        | BinOp::Div
        | BinOp::Mod
        | BinOp::Shl
        | BinOp::Shr
        | BinOp::BitAnd
        | BinOp::BitOr => lhs_ty.as_ref().clone(),
        BinOp::Eq
        | BinOp::Lt
        | BinOp::Le
        | BinOp::Gt
        | BinOp::Ge
        | BinOp::And
        | BinOp::Or
        | BinOp::Neq => Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
            ScalarTy::Bool,
        ))))),
    };
    match bin_op {
        // Shift operators only allow integer values (lhs_ty and rhs_ty can differ!)
        BinOp::Shl
        | BinOp::Shr => match (&lhs_ty.ty, &rhs_ty.ty) {
            (TyKind::Data(dty1), TyKind::Data(dty2)) => match (&dty1.dty, &dty2.dty) {
                (
                    DataTyKind::Scalar(ScalarTy::U8)
                    | DataTyKind::Scalar(ScalarTy::U32)
                    | DataTyKind::Scalar(ScalarTy::U64)
                    | DataTyKind::Scalar(ScalarTy::I32)
                    ,
                    DataTyKind::Scalar(ScalarTy::U8)
                    | DataTyKind::Scalar(ScalarTy::U32)
                    | DataTyKind::Scalar(ScalarTy::U64)
                    | DataTyKind::Scalar(ScalarTy::I32),
                ) => Ok(ret_dty),
                _ => Err(TyError::String(format!(
                    "Expected integer types for operator {}, instead got\n Lhs: {:?}\n Rhs: {:?}",
                    bin_op, lhs, rhs
                )))
            }
            _ => Err(TyError::String(format!(
                "Expected integer types for operator {}, instead got\n Lhs: {:?}\n Rhs: {:?}",
                bin_op, lhs, rhs
            ))),
        }
        _ => match (&lhs_ty.ty, &rhs_ty.ty) {
            (TyKind::Data(dty1), TyKind::Data(dty2)) => match (&dty1.dty, &dty2.dty) {
                (
                    DataTyKind::Scalar(ScalarTy::F32),
                    DataTyKind::Scalar(ScalarTy::F32),
                ) |
                (
                    DataTyKind::Scalar(ScalarTy::U8),
                    DataTyKind::Scalar(ScalarTy::U8),
                ) |
                (
                    DataTyKind::Scalar(ScalarTy::U32),
                    DataTyKind::Scalar(ScalarTy::U32),
                ) |
                (
                    DataTyKind::Scalar(ScalarTy::U64),
                    DataTyKind::Scalar(ScalarTy::U64),
                ) |
                (
                    DataTyKind::Scalar(ScalarTy::F64),
                    DataTyKind::Scalar(ScalarTy::F64)
                ) |
                (
                    DataTyKind::Scalar(ScalarTy::I32),
                    DataTyKind::Scalar(ScalarTy::I32),
                ) |
                (
                    DataTyKind::Scalar(ScalarTy::Bool),
                    DataTyKind::Scalar(ScalarTy::Bool),
                ) => Ok(ret_dty),
                _ => Err(TyError::String(format!(
                    "Expected the same number types for operator {}, instead got\n Lhs: {:?}\n Rhs: {:?}",
                    bin_op, dty1, dty2
                )))
            }
            _ => Err(TyError::String(format!(
                "Expected the same number types for operator {}, instead got\n Lhs: {:?}\n Rhs: {:?}",
                bin_op, lhs, rhs
            ))),
        }
    }
}

fn ty_check_unary_op(ctx: &mut ExprTyCtx, un_op: &UnOp, e: &mut Expr) -> TyResult<Ty> {
    ty_check_expr(ctx, e)?;
    let e_ty = e.ty.as_ref().unwrap();
    let e_dty = if let TyKind::Data(dty) = &e_ty.ty {
        dty.as_ref()
    } else {
        return Err(TyError::String("expected data type, but found".to_string()));
    };
    match &e_dty.dty {
        DataTyKind::Scalar(ScalarTy::F32)
        | DataTyKind::Scalar(ScalarTy::F64)
        | DataTyKind::Scalar(ScalarTy::I32)
        | DataTyKind::Scalar(ScalarTy::U8)
        | DataTyKind::Scalar(ScalarTy::U32)
        | DataTyKind::Scalar(ScalarTy::U64) => Ok(e_ty.as_ref().clone()),
        _ => Err(TyError::String(format!(
            "Exected a number type (i.e., f32 or i32), but found {:?}",
            e_ty
        ))),
    }
}

fn ty_check_cast(ctx: &mut ExprTyCtx, e: &mut Expr, dty: &DataTy) -> TyResult<Ty> {
    ty_check_expr(ctx, e)?;
    let e_ty = e.ty.as_ref().unwrap();
    match &e_ty.dty().dty {
        DataTyKind::Scalar(ScalarTy::F32)
        | DataTyKind::Scalar(ScalarTy::F64)
        | DataTyKind::Scalar(ScalarTy::I32)
        | DataTyKind::Scalar(ScalarTy::U8)
        | DataTyKind::Scalar(ScalarTy::U32)
        | DataTyKind::Scalar(ScalarTy::U64)
        => match dty.dty {
            DataTyKind::Scalar(ScalarTy::I32)
            | DataTyKind::Scalar(ScalarTy::U8)
            | DataTyKind::Scalar(ScalarTy::U32)
            | DataTyKind::Scalar(ScalarTy::U64)
            | DataTyKind::Scalar(ScalarTy::F32)
            | DataTyKind::Scalar(ScalarTy::F64) => Ok(Ty::new(TyKind::Data(Box::new(dty.clone())))),
            _ => Err(TyError::String(format!(
                "Exected a number type (i.e. i32 or f32) to cast to from {:?}, but found {:?}",
                e_ty, dty
            ))),
        },
        DataTyKind::Scalar(ScalarTy::Bool)
        => match dty.dty {
            DataTyKind::Scalar(ScalarTy::I32)
            | DataTyKind::Scalar(ScalarTy::U8)
            | DataTyKind::Scalar(ScalarTy::U32)
            | DataTyKind::Scalar(ScalarTy::U64) => Ok(Ty::new(TyKind::Data(Box::new(dty.clone())))),
            _ => Err(TyError::String(format!(
                "Exected an integer type (i.e. i32 or u32) to cast to from a bool, but found {:?}",
                dty
            ))),
        },
        _ => Err(TyError::String(format!(
            "Exected a number type (i.e. f32 or i32) or bool as a type to cast from, but found {:?}",
            e_ty
        ))),
    }
}

fn ty_check_app(
    ctx: &mut ExprTyCtx,
    fn_ident: &mut Ident,
    gen_args: &mut Vec<ArgKinded>,
    args: &mut [Expr],
) -> TyResult<Ty> {
    // TODO check well-kinded: FrameTyping, Prv, Ty
    let partially_applied_dep_fn_ty = ty_check_dep_app(ctx, fn_ident, gen_args)?;
    for arg in args.iter_mut() {
        ty_check_expr(ctx, arg)?;
    }
    let param_sigs_for_args = args
        .iter()
        .map(|arg| ParamSig::new(ctx.exec.clone(), arg.ty.as_ref().unwrap().as_ref().clone()))
        .collect();
    let ret_dty_placeholder = Ty::new(TyKind::Data(Box::new(DataTy::new(utils::fresh_ident(
        "ret_ty",
        DataTyKind::Ident,
    )))));
    let mut mono_fn_ty = unify::inst_fn_ty_scheme(&partially_applied_dep_fn_ty);
    unify::unify(
        &mut FnTy::new(
            vec![],
            None,
            param_sigs_for_args,
            ctx.exec.clone(),
            ret_dty_placeholder,
            vec![],
        ),
        &mut mono_fn_ty,
    )?;
    let mut inferred_gen_args =
        infer_kinded_args::infer_kinded_args(&partially_applied_dep_fn_ty, &mono_fn_ty);
    gen_args.append(&mut inferred_gen_args);

    if let Some(fn_def) = ctx.gl_ctx.find_fun(&fn_ident.name) {
        // Recursively check function definition with instantiated natural numbers
        let mut nat_names = vec![];
        let mut nat_vals = vec![];
        for (ik, ga) in fn_def.generic_params.iter().zip(gen_args) {
            if let (Kind::Nat, ArgKinded::Nat(n)) = (ik.kind, ga) {
                nat_names.push(ik.ident.name.clone());
                nat_vals.push(n.eval(ctx.nat_ctx)?);
            }
        }
        if ctx.gl_ctx.has_been_checked(&fn_ident.name, &nat_vals) {
            let mut called_nat_ctx =
                NatCtx::with_frame(nat_names.into_iter().zip(nat_vals.clone()).collect());
            let mut fn_def_clone = fn_def.clone();
            ty_check_global_fun_def(ctx.gl_ctx, &mut called_nat_ctx, &mut fn_def_clone)?;
            ctx.gl_ctx
                .add_checked_fun(&*fn_def, nat_vals.into_boxed_slice())
        }
    }

    // TODO check provenance relations
    return Ok(mono_fn_ty.ret_ty.as_ref().clone());
}

// fn owning_exec_for_expr(ty_ctx: &TyCtx, exec_ctx: &ExecExpr, expr: &Expr) -> ExecExpr {
//     if let ExprKind::PlaceExpr(pl_expr) = &expr.expr {
//         owning_exec_for_pl_expr(ty_ctx, pl_expr)
//     } else {
//         exec_ctx.clone()
//     }
// }
//
// fn owning_exec_for_pl_expr(ty_ctx: &TyCtx, pl_expr: &PlaceExpr) -> ExecExpr {
//     match &pl_expr.pl_expr {
//         PlaceExprKind::Ident(ident) => ty_ctx.ident_ty(ident).unwrap().exec.clone(),
//         PlaceExprKind::Proj(pl_expr, _)
//         | PlaceExprKind::Deref(pl_expr)
//         | PlaceExprKind::Idx(pl_expr, _)
//         | PlaceExprKind::View(pl_expr, _) => owning_exec_for_pl_expr(ty_ctx, pl_expr),
//         PlaceExprKind::Select(pl_expr, exec_expr) => {
//             let inner_exec = owning_exec_for_pl_expr(ty_ctx, pl_expr);
//         }
//     }
// }

fn ty_check_dep_app(
    ctx: &mut ExprTyCtx,
    fn_ident: &Ident,
    gen_args: &[ArgKinded],
) -> TyResult<FnTy> {
    //ty_check_expr(ctx, ef)?;
    let fn_ty = ctx.gl_ctx.fn_ty_by_ident(fn_ident)?;
    apply_gen_args_to_fn_ty_checked(ctx.kind_ctx, &ctx.exec, &fn_ty, gen_args)
    // } else {
    //     Err(TyError::String(format!(
    //         "The provided function expression\n {:?}\n does not have a function type.",
    //         ef
    //     )))
    // }
}

fn apply_gen_args_to_fn_ty_checked(
    kind_ctx: &KindCtx,
    exec: &ExecExpr,
    fn_ty: &FnTy,
    gen_args: &[ArgKinded],
) -> TyResult<FnTy> {
    let mut subst_fn_ty = fn_ty.clone();
    apply_gen_args_checked(kind_ctx, &mut subst_fn_ty, gen_args)?;
    apply_exec_checked(&mut subst_fn_ty, exec)?;
    Ok(subst_fn_ty)
}

fn apply_gen_args_checked(
    kind_ctx: &KindCtx,
    fn_ty: &mut FnTy,
    gen_args: &[ArgKinded],
) -> TyResult<()> {
    if fn_ty.generics.len() < gen_args.len() {
        return Err(TyError::String(format!(
            "Wrong amount of generic arguments. Expected {}, found {}",
            fn_ty.generics.len(),
            gen_args.len()
        )));
    }
    for (gen_param, gen_arg) in fn_ty.generics.iter().zip(gen_args) {
        check_arg_has_correct_kind(kind_ctx, &gen_param.kind, gen_arg)?;
    }
    let substituted_gen_idents = fn_ty.generics.drain(..gen_args.len()).collect::<Vec<_>>();
    utils::subst_idents_kinded(&substituted_gen_idents, gen_args, fn_ty);
    Ok(())
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

// FIXME the correct way to do this is to unify execs and to unify an identifier with an exec_expr
//  only if the types match (i.e., the exec expr type check must happen within unify)
fn apply_exec_checked(fn_ty: &mut FnTy, exec: &ExecExpr) -> TyResult<()> {
    // TODO reintroduce
    // exec::ty_check(
    //     ctx.kind_ctx,
    //     ctx.ty_ctx,
    //     fn_ty.generic_exec.as_ref(),
    //     &mut fn_ty.exec,
    // )?;
    if let Some(ge) = &fn_ty.generic_exec {
        // FIXME this includes checking for exec < any, therefore not necessarily unifcation (wrong name)
        unify::unify(
            &mut exec.ty.as_ref().unwrap().as_ref().clone(),
            &mut ge.ty.clone(),
        )?;
        let gen_exec_ident = ge.ident.clone();
        fn_ty.generic_exec = None;
        utils::subst_ident_exec(&gen_exec_ident, exec, fn_ty);
    }
    // if no generic exec was substituted, execs must still be unifable
    unify::unify(&mut fn_ty.exec, &mut exec.clone())?;
    Ok(())
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
    let mut kernel_exec = ExecExpr::new(ExecExprKind::new(BaseExec::GpuGrid(
        app_kernel.grid_dim.clone(),
        app_kernel.block_dim.clone(),
    )));
    exec::ty_check(ctx.nat_ctx, &TyCtx::new(), None, &mut kernel_exec)?;

    let mut kernel_ctx = ExprTyCtx {
        gl_ctx: &mut *ctx.gl_ctx,
        nat_ctx: ctx.nat_ctx,
        ident_exec: None,
        kind_ctx: ctx.kind_ctx,
        exec: kernel_exec,
        ty_ctx: &mut *ctx.ty_ctx,
        access_ctx: &mut AccessCtx::new(),
        unsafe_flag: ctx.unsafe_flag,
    };
    exec::ty_check(
        kernel_ctx.nat_ctx,
        kernel_ctx.ty_ctx,
        None,
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
    let extended_arg_sigs = app_kernel
        .args
        .iter()
        .map(|a| {
            ParamSig::new(
                kernel_ctx.exec.clone(),
                a.ty.as_ref().unwrap().as_ref().clone(),
            )
        })
        .chain(refs_to_shrd.into_iter().map(|a| {
            let block_exec = exec_distrib_over_blocks(&kernel_ctx.exec);
            ParamSig::new(block_exec, *a.ty.unwrap())
        }))
        .collect::<Vec<_>>();
    // type check function application for generic args and extended argument list
    let partially_applied_dep_fn_ty = ty_check_dep_app(
        &mut kernel_ctx,
        &mut app_kernel.fun_ident,
        &mut app_kernel.gen_args,
    )?;
    // build expected type to unify with
    let unit_ty = Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
        ScalarTy::Unit,
    )))));
    let mut mono_fn_ty = unify::inst_fn_ty_scheme(&partially_applied_dep_fn_ty);
    unify::unify(
        &mut FnTy::new(
            vec![],
            None,
            extended_arg_sigs,
            kernel_ctx.exec,
            unit_ty.clone(),
            vec![],
        ),
        &mut mono_fn_ty,
    )?;
    let mut inferred_k_args =
        infer_kinded_args::infer_kinded_args(&partially_applied_dep_fn_ty, &mono_fn_ty);
    app_kernel.gen_args.append(&mut inferred_k_args);
    Ok(unit_ty)
}

fn exec_distrib_over_blocks(exec_expr: &ExecExpr) -> ExecExpr {
    let base_clone = ExecExprKind::new(exec_expr.exec.base.clone());
    let distrib_over_blocks = if let BaseExec::GpuGrid(gdim, _) = &exec_expr.exec.base {
        match gdim {
            Dim::XYZ(_) => base_clone
                .forall(DimCompo::X)
                .forall(DimCompo::Y)
                .forall(DimCompo::Z),
            Dim::XY(_) => base_clone.forall(DimCompo::X).forall(DimCompo::Y),
            Dim::XZ(_) => base_clone.forall(DimCompo::X).forall(DimCompo::Z),
            Dim::YZ(_) => base_clone.forall(DimCompo::Y).forall(DimCompo::Z),
            Dim::X(_) => base_clone.forall(DimCompo::X).forall(DimCompo::X),
            Dim::Y(_) => base_clone.forall(DimCompo::Y).forall(DimCompo::Y),
            Dim::Z(_) => base_clone.forall(DimCompo::Z).forall(DimCompo::Z),
        }
    } else {
        panic!("Expected GPU grid.")
    };
    ExecExpr::new(distrib_over_blocks)
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
        Lit::U8(_) => ScalarTy::U8,
        Lit::U32(_) => ScalarTy::U32,
        Lit::U64(_) => ScalarTy::U64,
        Lit::F32(_) => ScalarTy::F32,
        Lit::F64(_) => ScalarTy::F64,
    };
    Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
        scalar_data,
    )))))
}

fn infer_pattern_ident_tys(
    ctx: &mut ExprTyCtx,
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
                ctx.exec.clone(),
            );
            ctx.ty_ctx.append_ident_typed(ident_with_annotated_ty);
            Ok(())
        }
        (Pattern::Wildcard, _) => Ok(()),
        (Pattern::Tuple(patterns), DataTyKind::Tuple(elem_tys)) => {
            for (p, tty) in patterns.iter().zip(elem_tys) {
                infer_pattern_ident_tys(ctx, p, &Ty::new(TyKind::Data(Box::new(tty.clone()))))?;
            }
            Ok(())
        }
        _ => Err(TyError::PatternAndTypeDoNotMatch),
    }
}

fn infer_tys_and_append_idents(
    ctx: &mut ExprTyCtx,
    pattern: &Pattern,
    pattern_ty: &mut Option<Box<Ty>>,
    assign_ty: &mut Ty,
) -> TyResult<()> {
    let pattern_ty = if let Some(pty) = pattern_ty {
        unify::sub_unify(ctx.kind_ctx, ctx.ty_ctx, assign_ty, pty)?;
        pty.as_ref().clone()
    } else {
        assign_ty.clone()
    };
    infer_pattern_ident_tys(ctx, pattern, &pattern_ty)
}

fn ty_check_let(
    ctx: &mut ExprTyCtx,
    pattern: &Pattern,
    pattern_ty: &mut Option<Box<Ty>>,
    expr: &mut Expr,
) -> TyResult<Ty> {
    ty_check_expr(ctx, expr)?;
    let e_ty = expr.ty.as_mut().unwrap();
    infer_tys_and_append_idents(ctx, pattern, pattern_ty, e_ty)?;
    Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
        DataTyKind::Scalar(ScalarTy::Unit),
    )))))
}

// TODO respect exec?
fn ty_check_let_uninit(
    ctx: &mut ExprTyCtx,
    annot_exec: &Option<Box<ExecExpr>>,
    ident: &Ident,
    ty: &Ty,
) -> TyResult<Ty> {
    // TODO is the type well-formed?
    if let TyKind::Data(dty) = &ty.ty {
        let mut exec_expr = if let Some(ex) = annot_exec {
            ex.as_ref().clone()
        } else {
            ctx.exec.clone()
        };
        exec::ty_check(ctx.nat_ctx, ctx.ty_ctx, ctx.ident_exec, &mut exec_expr)?;
        let ident_with_ty = IdentTyped::new(
            ident.clone(),
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Dead(
                dty.clone(),
            ))))),
            Mutability::Mut,
            exec_expr,
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

fn ty_check_non_place(ctx: &mut ExprTyCtx, pl_expr: &mut PlaceExpr) -> TyResult<Ty> {
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
    let potential_accesses = borrow_check::access_safety_check(
        &BorrowCheckCtx::new(ctx, vec![], Ownership::Shrd),
        pl_expr,
    )
    .map_err(|err| TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Shrd, err))?;
    ctx.access_ctx.insert(&ctx.exec, potential_accesses);
    if pl_expr.ty.as_ref().unwrap().copyable() {
        Ok(pl_expr.ty.as_ref().unwrap().as_ref().clone())
    } else {
        Err(TyError::String("Data type is not copyable.".to_string()))
    }
}

fn ty_check_place(ctx: &mut ExprTyCtx, pl_expr: &mut PlaceExpr) -> TyResult<Ty> {
    pl_expr::ty_check(&PlExprTyCtx::new(ctx, Ownership::Uniq), pl_expr)?;
    let place = pl_expr.clone().to_place().unwrap();
    // If place is an identifier referring to a globally declared function
    // let pl_ty = if let Ok(fun_ty) = ctx.gl_ctx.fn_ty_by_ident(&place.ident) {
    //     Ty::new(TyKind::FnTy(Box::new(fun_ty.clone())))
    // } else {
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
        let potential_accesses = borrow_check::access_safety_check(
            &BorrowCheckCtx::new(ctx, vec![], Ownership::Shrd),
            pl_expr,
        )
        .map_err(|err| {
            TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Shrd, err)
        })?;
        ctx.access_ctx.insert(&ctx.exec, potential_accesses);
    } else {
        let potential_accesses = borrow_check::access_safety_check(
            &BorrowCheckCtx::new(ctx, vec![], Ownership::Uniq),
            pl_expr,
        )
        .map_err(|err| {
            TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Uniq, err)
        })?;
        ctx.access_ctx.insert(&ctx.exec, potential_accesses);
        ctx.ty_ctx.kill_place(&place);
    };
    Ok(Ty::new(TyKind::Data(Box::new(pl_ty))))
    // };
    // Ok(pl_ty)
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
    let loans = borrow_check::access_safety_check(&BorrowCheckCtx::new(ctx, vec![], own), pl_expr)
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
        | ExecTyKind::GpuWarpGrp(_)
        | ExecTyKind::GpuWarp
        | ExecTyKind::GpuThreadGrp(_) => {
            vec![Memory::GpuGlobal, Memory::GpuShared, Memory::GpuLocal]
        }
        ExecTyKind::GpuToThreads(_, _) => vec![Memory::GpuGlobal, Memory::GpuLocal],
        ExecTyKind::Any => vec![],
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
            // | DataTyKind::Range
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
            DataTyKind::Struct(struct_decl) => {
                for (_, dty) in &struct_decl.fields {
                    ty_well_formed(kind_ctx, ty_ctx, exec_ty, &Ty::new(TyKind::Data(Box::new(dty.clone()))))?;
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
            for param_sig in &fn_ty.param_sigs {
                // TODO which checks are necessary for the execution resource in
                //  param_sig.exec_expr?
                ty_well_formed(&extended_kind_ctx, ty_ctx, exec_ty, &param_sig.ty)?;
            }
        }
    }
    Ok(())
}

pub fn callable_in(callee_exec_ty: &ExecTy, caller_exec_ty: &ExecTy) -> bool {
    if &callee_exec_ty.ty == &ExecTyKind::Any {
        true
    } else {
        let res = unify::unify(&mut callee_exec_ty.clone(), &mut caller_exec_ty.clone());
        res.is_ok()
    }
}

fn expand_exec_expr(ctx: &ExprTyCtx, exec_expr: &ExecExpr) -> TyResult<ExecExpr> {
    match &exec_expr.exec.base {
        BaseExec::CpuThread | BaseExec::GpuGrid(_, _) => Ok(exec_expr.clone()),
        BaseExec::Ident(ident) => {
            let inner_exec_expr = ctx.ty_ctx.get_exec_expr(ident)?;
            let new_base = inner_exec_expr.exec.base.clone();
            let mut new_exec_path = inner_exec_expr.exec.path.clone();
            new_exec_path.append(&mut exec_expr.exec.path.clone());
            let mut expanded_exec_expr: ExecExpr =
                ExecExpr::new(ExecExprKind::with_path(new_base, new_exec_path));
            exec::ty_check(
                ctx.nat_ctx,
                ctx.ty_ctx,
                ctx.ident_exec,
                &mut expanded_exec_expr,
            )?;
            Ok(expanded_exec_expr)
        }
    }
}

fn legal_exec_under_current(ctx: &ExprTyCtx, exec: &ExecExpr) -> TyResult<()> {
    let expanded_exec_expr = expand_exec_expr(ctx, exec)?;
    if ctx.exec != expanded_exec_expr {
        let current_exec_ty = &ctx.exec.ty.as_ref().unwrap().ty;
        let expanded_exec_ty = expanded_exec_expr.ty.unwrap().ty;
        match (current_exec_ty, expanded_exec_ty) {
            // FIXME Piet: this does not guarantee that the GpuWarpGrp was created from the GpuBlock
            //  TODO Basti: syntactically compare the exec expressions instead of types
            //   ctx.exec.to_warps == expanded_exec?
            //   ctx.exec.to_threads == expanded_exec?
            (ExecTyKind::GpuBlock(..), ExecTyKind::GpuWarpGrp(..)) => (),
            _ => {
                let mut print_state = PrintState::new();
                print_state.print_exec_expr(exec);
                return Err(TyError::IllegalExec);
            }
        }
    }
    Ok(())
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
