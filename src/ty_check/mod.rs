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
use crate::arena_ast::internal::{Frame, IdentTyped, Loan, Place, PrvMapping};
use crate::arena_ast::utils;
use crate::arena_ast::*;
use crate::error::ErrorReported;
use bumpalo::collections::CollectIn;
use bumpalo::collections::Vec as BumpVec;
use bumpalo::Bump;
use ctxs::{AccessCtx, GlobalCtx, KindCtx, TyCtx};
use error::*;
use std::collections::HashSet;

type TyResult<'a, T> = Result<T, TyError<'a>>;

macro_rules! matches_dty {
    ($ty: expr, $dty_pat: pat_param) => {
        if let crate::arena_ast::TyKind::Data(d) = &$ty.ty {
            matches!(d, $dty_pat)
        } else {
            false
        }
    };
}
use crate::arena_ast::printer::PrintState;
use crate::ty_check::borrow_check::BorrowCheckCtx;
use crate::ty_check::ctxs::GlobalDecl;
pub(crate) use matches_dty;

// ∀ε ∈ Σ. Σ ⊢ ε
// --------------
//      ⊢ Σ
pub fn ty_check<'a>(
    compil_unit: &mut CompilUnit<'a>,
    arena: &'a Bump,
) -> Result<(), ErrorReported> {
    let predecls = pre_decl::fun_decls(arena)
        .into_iter()
        .map(|(fname, fty)| GlobalDecl::FnDecl(fname, arena.alloc(fty)))
        .collect_in(arena);

    let mut gl_ctx = GlobalCtx::new(&*compil_unit, predecls, arena);
    let mut nat_ctx = NatCtx::new(arena);
    let mut main_fun = match gl_ctx.pop_fun_def(compil_unit, "main") {
        Some(fun_def) => fun_def,
        None => {
            TyError::MissingMain.emit(compil_unit.source);
            return Err(ErrorReported);
        }
    };

    if let Err(err) =
        ty_check_global_fun_def(&mut gl_ctx, &mut nat_ctx, &mut main_fun, compil_unit, arena)
    {
        err.emit(compil_unit.source);
        return Err(ErrorReported);
    }

    gl_ctx.push_fun_checked_under_nats(compil_unit, arena, main_fun, &[]);
    Ok(())
}

struct ExprTyCtx<'ctx, 'a> {
    compil_unit: &'ctx mut CompilUnit<'a>,
    gl_ctx: &'ctx mut GlobalCtx<'a>,
    nat_ctx: &'ctx mut NatCtx<'a>,
    ident_exec: Option<&'ctx IdentExec<'a>>,
    kind_ctx: &'ctx mut KindCtx<'a>,
    exec: ExecExpr<'a>,
    ty_ctx: &'ctx mut TyCtx<'a>,
    access_ctx: &'ctx mut AccessCtx<'a>,
    unsafe_flag: bool,
}

// Σ ⊢ fn f <List[φ], List[ρ], List[α]> (x1: τ1, ..., xn: τn) → τr where List[ρ1:ρ2] { e }
fn ty_check_global_fun_def<'a>(
    gl_ctx: &mut GlobalCtx<'a>,
    nat_ctx: &mut NatCtx<'a>,
    gf: &mut FunDef<'a>,
    compil_unit: &mut CompilUnit<'a>,
    arena: &'a Bump,
) -> TyResult<'a, ()> {
    // TODO check that every prv_rel only uses provenance variables bound in generic_params
    let mut kind_ctx =
        KindCtx::gl_fun_kind_ctx(gf.generic_params.clone(), gf.prv_rels.clone(), arena)?;
    let mut ty_ctx = TyCtx::new(arena);
    // Build frame typing for this function
    // TODO give Frame its own type and move this into frame and/or ParamDecl
    if let Some(ident_exec) = &gf.generic_exec {
        let mut exec_ident = ExecExpr::new(
            arena,
            ExecExprKind::new(arena, BaseExec::Ident(ident_exec.ident.clone())),
        );
        exec::ty_check(
            nat_ctx,
            &ty_ctx,
            gf.generic_exec.as_ref(),
            &mut exec_ident,
            arena,
        )?;
        ty_ctx.append_exec_mapping(ident_exec.ident.clone(), exec_ident);
    }
    exec::ty_check(
        nat_ctx,
        &ty_ctx,
        gf.generic_exec.as_ref(),
        &mut gf.exec,
        arena,
    )?;

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
                exec::ty_check(nat_ctx, &ty_ctx, gf.generic_exec.as_ref(), &mut exec, arena)?;
                Ok(IdentTyped {
                    ident: ident.clone(),
                    ty: (*ty.unwrap()).clone(),
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

    let mut access_ctx = AccessCtx::new(arena);
    let mut ctx = ExprTyCtx {
        compil_unit,
        gl_ctx: &mut *gl_ctx,
        nat_ctx: &mut *nat_ctx,
        kind_ctx: &mut kind_ctx,
        ident_exec: gf.generic_exec.as_ref(),
        exec: gf.exec.clone(),
        ty_ctx: &mut ty_ctx,
        access_ctx: &mut access_ctx,
        unsafe_flag: false,
    };

    let mut body = gf.body.clone();
    let mut body_expr = body.body.clone();
    ty_check_expr(&mut ctx, &mut body_expr, arena)?;
    drop(ctx);
    body.body = arena.alloc(body_expr);
    gf.body = arena.alloc(body);
    // t <= t_f
    // unify::constrain(
    //     gf.body_expr.ty.as_ref().unwrap(),
    //     &Ty::new(TyKind::Data(gf.ret_dty.clone())),
    // )?;

    //coalesce::coalesce_ty(&mut self.term_constr.constr_map, &mut body_ctx, )
    let mut empty_ty_ctx = TyCtx::new(arena);
    subty::check(
        &kind_ctx,
        &mut empty_ty_ctx,
        gf.body.body.ty.as_ref().unwrap().dty(),
        &gf.ret_dty,
        arena,
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
#[inline(never)]
fn clone_to_arena<'a, T: Clone + 'a>(arena: &'a Bump, value: &T) -> &'a mut T {
    arena.alloc(value.clone())
}

#[inline(never)]
fn clone_block_to_arena<'a>(arena: &'a Bump, block: &Block<'a>) -> &'a mut Block<'a> {
    arena.alloc(block.clone_in(arena))
}

fn ty_check_expr<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    expr: &mut Expr<'a>,
    arena: &'a Bump,
) -> TyResult<'a, ()> {
    let ty = match &mut expr.expr {
        ExprKind::PlaceExpr(pl_expr) => {
            let owned = clone_to_arena(arena, *pl_expr);
            let ty = if owned.is_place() {
                ty_check_place(ctx, owned, arena)?
            } else {
                ty_check_non_place(ctx, owned, arena)?
            };
            *pl_expr = owned;
            ty
        }
        ExprKind::Block(block_ref) => {
            let block = clone_block_to_arena(arena, *block_ref);
            let ty = ty_check_block(ctx, block, arena)?;
            *block_ref = block;
            ty
        }
        ExprKind::Let(pattern, annotation, expr_ref) => {
            let rhs = clone_to_arena(arena, *expr_ref);
            let ty = ty_check_let(ctx, pattern, annotation, rhs, arena)?;
            *expr_ref = rhs;
            ty
        }
        ExprKind::LetUninit(annot_exec, ident, ty) => {
            ty_check_let_uninit(ctx, annot_exec, ident, ty, arena)?
        }
        ExprKind::Seq(exprs) => ty_check_seq(ctx, exprs, arena)?,
        ExprKind::Lit(lit) => ty_check_literal(lit, arena),
        ExprKind::Array(elems) => ty_check_array(ctx, elems, arena)?,
        ExprKind::Tuple(elems) => ty_check_tuple(ctx, elems, arena)?,
        ExprKind::App(fn_ident_ref, gen_args, args) => {
            let fn_ident = clone_to_arena(arena, *fn_ident_ref);
            let ty = ty_check_app(ctx, fn_ident, gen_args, args, arena)?;
            *fn_ident_ref = fn_ident;
            ty
        }
        ExprKind::DepApp(fn_ident, gen_args) => Ty::new(TyKind::FnTy(
            arena.alloc(ty_check_dep_app(ctx, fn_ident, gen_args, arena)?),
        )),
        ExprKind::AppKernel(app_kernel_ref) => {
            let app_kernel = clone_to_arena(arena, *app_kernel_ref);
            let ty = ty_check_app_kernel(ctx, app_kernel, arena)?;
            *app_kernel_ref = app_kernel;
            ty
        }
        ExprKind::Ref(prv, own, pl_expr) => {
            let owned = clone_to_arena(arena, *pl_expr);
            let ty = ty_check_borrow(ctx, prv, *own, owned, arena)?;
            *pl_expr = owned;
            ty
        }
        ExprKind::Assign(pl_expr_ref, rhs_ref) => {
            let pl_expr = clone_to_arena(arena, *pl_expr_ref);
            let rhs = clone_to_arena(arena, *rhs_ref);
            let ty = if pl_expr.is_place() {
                ty_check_assign_place(ctx, pl_expr, rhs, arena)?
            } else {
                ty_check_assign_non_place(ctx, pl_expr, rhs, arena)?
            };
            *pl_expr_ref = pl_expr;
            *rhs_ref = rhs;
            ty
        }
        ExprKind::IdxAssign(pl_expr_ref, idx, rhs_ref) => {
            let pl_expr = clone_to_arena(arena, *pl_expr_ref);
            let rhs = clone_to_arena(arena, *rhs_ref);
            let ty = ty_check_idx_assign(ctx, pl_expr, idx, rhs, arena)?;
            *pl_expr_ref = pl_expr;
            *rhs_ref = rhs;
            ty
        }
        ExprKind::Split(split_ref) => {
            let split = clone_to_arena(arena, *split_ref);
            let ty = ty_check_split(ctx, split, arena)?;
            *split_ref = split;
            ty
        }
        ExprKind::Sched(sched_ref) => {
            let sched = clone_to_arena(arena, *sched_ref);
            let ty = ty_check_sched(ctx, sched, arena)?;
            *sched_ref = sched;
            ty
        }
        ExprKind::ForNat(var, range, body_ref) => {
            let body = clone_to_arena(arena, *body_ref);
            let ty = ty_check_for_nat(ctx, var, range, body, arena)?;
            *body_ref = body;
            ty
        }
        ExprKind::For(ident, collection_ref, body_ref) => {
            let collection = clone_to_arena(arena, *collection_ref);
            let body = clone_to_arena(arena, *body_ref);
            let ty = ty_check_for(ctx, ident, collection, body, arena)?;
            *collection_ref = collection;
            *body_ref = body;
            ty
        }
        ExprKind::IfElse(cond_ref, true_ref, false_ref) => {
            let cond = clone_to_arena(arena, *cond_ref);
            let case_true = clone_to_arena(arena, *true_ref);
            let case_false = clone_to_arena(arena, *false_ref);
            let ty = ty_check_if_else(ctx, cond, case_true, case_false, arena)?;
            *cond_ref = cond;
            *true_ref = case_true;
            *false_ref = case_false;
            ty
        }
        ExprKind::If(cond_ref, true_ref) => {
            let cond = clone_to_arena(arena, *cond_ref);
            let case_true = clone_to_arena(arena, *true_ref);
            let ty = ty_check_if(ctx, cond, case_true, arena)?;
            *cond_ref = cond;
            *true_ref = case_true;
            ty
        }
        ExprKind::While(cond_ref, body_ref) => {
            let cond = clone_to_arena(arena, *cond_ref);
            let body = clone_to_arena(arena, *body_ref);
            let ty = ty_check_while(ctx, cond, body, arena)?;
            *cond_ref = cond;
            *body_ref = body;
            ty
        }
        ExprKind::BinOp(bin_op, lhs_ref, rhs_ref) => {
            let lhs = clone_to_arena(arena, *lhs_ref);
            let rhs = clone_to_arena(arena, *rhs_ref);
            let ty = ty_check_binary_op(ctx, bin_op, lhs, rhs, arena)?;
            *lhs_ref = lhs;
            *rhs_ref = rhs;
            ty
        }
        ExprKind::UnOp(un_op, expr_ref) => {
            let inner = clone_to_arena(arena, *expr_ref);
            let ty = ty_check_unary_op(ctx, un_op, inner, arena)?;
            *expr_ref = inner;
            ty
        }
        ExprKind::Sync(exec) => ty_check_sync(ctx, exec, arena)?,
        ExprKind::Unsafe(expr_ref) => {
            let inner = clone_to_arena(arena, *expr_ref);
            ctx.unsafe_flag = true;
            let checked = ty_check_expr(ctx, inner, arena);
            ctx.unsafe_flag = false;
            checked?;
            let ty = (*inner.ty.unwrap()).clone();
            *expr_ref = inner;
            ty
        }
        ExprKind::Cast(expr_ref, dty) => {
            let inner = clone_to_arena(arena, *expr_ref);
            let ty = ty_check_cast(ctx, inner, dty, arena)?;
            *expr_ref = inner;
            ty
        }
        ExprKind::Range(_, _) => unimplemented!(),
        ExprKind::Hole => ty_check_hole(ctx, arena)?,
    };

    expr.ty = Some(arena.alloc(ty));
    Ok(())
}

fn ty_check_hole<'a>(ctx: &ExprTyCtx<'_, 'a>, arena: &'a Bump) -> TyResult<'a, Ty<'a>> {
    if ctx.unsafe_flag {
        Ok(Ty::new(TyKind::Data(arena.alloc(DataTy::new(
            arena,
            DataTyKind::Ident(Ident::new_impli(arena, &utils::fresh_name("hole"))),
        )))))
    } else {
        Err(TyError::UnsafeRequired)
    }
}

fn ty_check_sync<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    exec: &mut Option<ExecExpr<'a>>,
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    let synced = match exec {
        Some(exec) => {
            exec::ty_check(ctx.nat_ctx, ctx.ty_ctx, ctx.ident_exec, exec, arena)?;
            exec
        }
        None => &ctx.exec,
    };
    syncable_under_exec(synced, &ctx.exec)?;
    ctx.access_ctx.clear_sync_for(ctx.ty_ctx, synced, arena);
    Ok(Ty::new(TyKind::Data(arena.alloc(DataTy::new(
        arena,
        DataTyKind::Scalar(ScalarTy::Unit),
    )))))
}

// assumes fully typed ExecExpr as input
fn syncable_under_exec<'a>(synced: &ExecExpr<'a>, under: &ExecExpr<'a>) -> TyResult<'a, ()> {
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

fn syncable_exec_ty<'a>(exec_ty: &ExecTy<'a>) -> bool {
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

fn infer_and_append_prv<'a>(ty_ctx: &mut TyCtx<'a>, prv_name: &Option<&str>) -> String {
    if let Some(prv) = prv_name.as_ref() {
        (*prv).to_owned()
    } else {
        let name = utils::fresh_name("r");
        ty_ctx.append_prv_mapping(PrvMapping::new(&name));
        name
    }
}

fn ty_check_for_nat<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    ident: &Ident<'a>,
    range: &NatRange<'a>,
    // TODO make this a block
    body: &mut Expr<'a>,
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    let compare_ty_ctx = ctx.ty_ctx.clone();
    let lifted_range = range.lift(arena, ctx.nat_ctx)?;

    for i in lifted_range {
        ctx.ty_ctx.push_empty_frame(arena);
        ctx.nat_ctx.push_empty_frame(arena);
        ctx.nat_ctx.append(&ident.name, i, arena);

        ty_check_expr(ctx, body, arena)?;

        ctx.nat_ctx.pop_frame();
        ctx.ty_ctx.pop_frame();
        if let DataTyKind::Scalar(ScalarTy::Unit) = &body.ty.as_ref().unwrap().dty().dty {
            if ctx.ty_ctx != &compare_ty_ctx {
                return Err(TyError::String(
                    "Using a data type in loop that can only be used once.".to_string(),
                ));
            }
        } else {
            return Err(TyError::UnexpectedType);
        }
    }
    Ok(Ty::new(TyKind::Data(arena.alloc(DataTy::new(
        arena,
        DataTyKind::Scalar(ScalarTy::Unit),
    )))))
}

fn ty_check_for<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    ident: &Ident<'a>,
    collec: &mut Expr<'a>,
    body: &mut Expr<'a>,
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    ty_check_expr(ctx, collec, arena)?;
    let collec_dty = if let TyKind::Data(collec_dty) = &collec.ty.as_ref().unwrap().ty {
        *collec_dty
    } else {
        return Err(TyError::String(format!(
            "Expected array data type or reference to array data type, but found {:?}",
            collec.ty.as_ref().unwrap()
        )));
    };

    let ident_dty = match &collec_dty.dty {
        // TODO
        DataTyKind::Array(elem_dty, n) => unimplemented!(),
        DataTyKind::Ref(reff) => match &reff.dty.dty {
            DataTyKind::Array(elem_dty, _) => DataTyKind::Ref(arena.alloc(RefDty::new(
                arena,
                reff.rgn.clone(),
                reff.own,
                reff.mem.clone(),
                (*elem_dty).clone(),
            ))),
            DataTyKind::ArrayShape(elem_dty, _) => DataTyKind::Ref(arena.alloc(RefDty::new(
                arena,
                reff.rgn.clone(),
                reff.own,
                reff.mem.clone(),
                (*elem_dty).clone(),
            ))),
            _ => {
                return Err(TyError::String(format!(
                    "Expected reference to array data type, but found {:?}",
                    reff.dty,
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
    let mut frame = Frame::new_in(arena);
    frame.append_idents_typed(vec![IdentTyped::new_in(
        arena,
        ident.name,
        Ty::new(TyKind::Data(arena.alloc(DataTy::new(arena, ident_dty)))),
        Mutability::Const,
        ctx.exec.clone(),
    )]);
    ctx.ty_ctx.push_frame(frame);
    ty_check_expr(ctx, body, arena)?;
    ctx.ty_ctx.pop_frame();
    if ctx.ty_ctx != &compare_ty_ctx {
        return Err(TyError::String(
            "Using a data type in loop that can only be used once.".to_string(),
        ));
    }
    Ok(Ty::new(TyKind::Data(arena.alloc(DataTy::new(
        arena,
        DataTyKind::Scalar(ScalarTy::Unit),
    )))))
}

fn ty_check_while<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    cond: &mut Expr<'a>,
    body: &mut Expr<'a>,
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    ty_check_expr(&mut *ctx, cond, arena)?;
    ctx.ty_ctx.push_empty_frame(arena);
    ty_check_expr(ctx, body, arena)?;
    ctx.ty_ctx.pop_frame();
    let compare_ty_ctx = ctx.ty_ctx.clone();
    // Is it better/more correct to push and pop scope around this as well?
    ty_check_expr(ctx, cond, arena)?;
    if ctx.ty_ctx != &compare_ty_ctx {
        return Err(TyError::String(
            "Context should have stayed the same".to_string(),
        ));
    }
    ctx.ty_ctx.push_empty_frame(arena);
    ty_check_expr(ctx, body, arena)?;
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
    Ok(Ty::new(TyKind::Data(arena.alloc(DataTy::new(
        arena,
        DataTyKind::Scalar(ScalarTy::Unit),
    )))))
}

fn ty_check_if_else<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    cond: &mut Expr<'a>,
    case_true: &mut Expr<'a>,
    case_false: &mut Expr<'a>,
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    // TODO deal with provenances in cases
    ty_check_expr(ctx, cond, arena)?;
    // TODO acccess_ctx clone
    let mut ty_ctx_clone = ctx.ty_ctx.clone();
    let mut ctx_clone = ExprTyCtx {
        compil_unit: &mut *ctx.compil_unit,
        gl_ctx: &mut *ctx.gl_ctx,
        nat_ctx: ctx.nat_ctx,
        ident_exec: ctx.ident_exec,
        kind_ctx: &mut *ctx.kind_ctx,
        exec: ctx.exec.clone(),
        ty_ctx: &mut ty_ctx_clone,
        access_ctx: &mut *ctx.access_ctx,
        unsafe_flag: ctx.unsafe_flag,
    };
    let _case_true_ty_ctx = ty_check_expr(&mut ctx_clone, case_true, arena)?;
    ctx.ty_ctx.push_empty_frame(arena);
    ty_check_expr(ctx, case_false, arena)?;
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

    Ok(Ty::new(TyKind::Data(arena.alloc(DataTy::new(
        arena,
        DataTyKind::Scalar(ScalarTy::Unit),
    )))))
}

fn ty_check_if<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    cond: &mut Expr<'a>,
    case_true: &mut Expr<'a>,
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    // TODO deal with provenances in cases
    ty_check_expr(ctx, cond, arena)?;
    ctx.ty_ctx.push_empty_frame(arena);
    ty_check_expr(ctx, case_true, arena)?;
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

    Ok(Ty::new(TyKind::Data(arena.alloc(DataTy::new(
        arena,
        DataTyKind::Scalar(ScalarTy::Unit),
    )))))
}

fn ty_check_split<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    indep: &mut Split<'a>,
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    // exec::ty_check(
    //     ctx.kind_ctx,
    //     ctx.ty_ctx,
    //     ctx.ident_exec,
    //     &mut indep.split_exec,
    // )?;
    let mut split_exec = indep.split_exec.clone();
    exec::ty_check(
        ctx.nat_ctx,
        ctx.ty_ctx,
        ctx.ident_exec,
        &mut split_exec,
        arena,
    )?;
    indep.split_exec = arena.alloc(split_exec);
    legal_exec_under_current(ctx, &indep.split_exec, arena)?;
    let expanded_exec_expr = expand_exec_expr(ctx, &indep.split_exec, arena)?;
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
        let mut branch_exec = ExecExpr::new(
            arena,
            expanded_exec_expr.exec.clone().split_proj(
                arena,
                indep.dim_compo,
                indep.pos.clone(),
                if i == 0 {
                    LeftOrRight::Left
                } else if i == 1 {
                    LeftOrRight::Right
                } else {
                    panic!("Unexepected projection.")
                },
            ),
        );
        exec::ty_check(
            &ctx.nat_ctx,
            &ctx.ty_ctx,
            ctx.ident_exec,
            &mut branch_exec,
            arena,
        )?;
        let mut branch_expr_ty_ctx = ExprTyCtx {
            compil_unit: &mut *ctx.compil_unit,
            gl_ctx: &mut *ctx.gl_ctx,
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
            .push_empty_frame(arena)
            .append_exec_mapping(indep.branch_idents[i].clone(), branch_exec.clone());
        ty_check_expr(&mut branch_expr_ty_ctx, &mut indep.branch_bodies[i], arena)?;
        if indep.branch_bodies[i].ty.as_ref().unwrap().ty
            != TyKind::Data(arena.alloc(DataTy::new(arena, DataTyKind::Scalar(ScalarTy::Unit))))
        {
            return Err(TyError::String(
                "A par_branch branch must not return a value.".to_string(),
            ));
        }
        branch_expr_ty_ctx.ty_ctx.pop_frame();
    }
    Ok(Ty::new(TyKind::Data(arena.alloc(DataTy::new(
        arena,
        DataTyKind::Scalar(ScalarTy::Unit),
    )))))
}

fn ty_check_sched<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    sched: &mut Sched<'a>,
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    let mut sched_exec = sched.sched_exec.clone();
    exec::ty_check(
        ctx.nat_ctx,
        ctx.ty_ctx,
        ctx.ident_exec,
        &mut sched_exec,
        arena,
    )?;
    sched.sched_exec = arena.alloc(sched_exec);
    legal_exec_under_current(ctx, &sched.sched_exec, arena)?;
    let expanded_exec_expr = expand_exec_expr(ctx, &sched.sched_exec, arena)?;
    let mut body_exec = ExecExpr::new(arena, expanded_exec_expr.exec.clone().forall(sched.dim));
    exec::ty_check(
        ctx.nat_ctx,
        ctx.ty_ctx,
        ctx.ident_exec,
        &mut body_exec,
        arena,
    )?;
    let mut schedule_body_ctx = ExprTyCtx {
        compil_unit: &mut *ctx.compil_unit,
        gl_ctx: &mut *ctx.gl_ctx,
        nat_ctx: &mut *ctx.nat_ctx,
        ident_exec: ctx.ident_exec,
        kind_ctx: &mut *ctx.kind_ctx,
        exec: body_exec.clone(),
        ty_ctx: &mut *ctx.ty_ctx,
        access_ctx: &mut *ctx.access_ctx,
        unsafe_flag: ctx.unsafe_flag,
    };
    schedule_body_ctx.ty_ctx.push_empty_frame(arena);
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
    let mut body = sched.body.clone_in(arena);
    let mut body_expr = body.body.clone();
    ty_check_expr(&mut schedule_body_ctx, &mut body_expr, arena)?;
    schedule_body_ctx.ty_ctx.pop_frame();
    schedule_body_ctx
        .access_ctx
        .garbage_collect(schedule_body_ctx.ty_ctx, arena);
    body.body = arena.alloc(body_expr);
    sched.body = arena.alloc(body);
    Ok(Ty::new(TyKind::Data(arena.alloc(DataTy::new(
        arena,
        DataTyKind::Scalar(ScalarTy::Unit),
    )))))
}

fn ty_check_block<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    block: &mut Block<'a>,
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    ctx.ty_ctx.push_empty_frame(arena);
    for prv in &block.prvs {
        ctx.ty_ctx.append_prv_mapping(PrvMapping::new(prv));
    }
    let mut body = block.body.clone();
    ty_check_expr(ctx, &mut body, arena)?;
    ctx.ty_ctx.pop_frame();
    ctx.access_ctx.garbage_collect(ctx.ty_ctx, arena);
    let ty = (*body.ty.unwrap()).clone();
    block.body = arena.alloc(body);
    Ok(ty)
}

fn collect_valid_loans<'a>(
    ty_ctx: &TyCtx<'a>,
    mut loans: HashSet<Loan<'a>>,
    arena: &'a Bump,
) -> HashSet<Loan<'a>> {
    // FIXME this implementations assumes unique names which is not the case
    loans.retain(|l| {
        let root_ident = &l.place_expr.to_pl_ctx_and_most_specif_pl(arena).1.ident;
        ty_ctx.contains(root_ident)
    });
    loans
}

fn check_mutable<'a>(ty_ctx: &TyCtx<'a>, pl: &Place<'a>, arena: &'a Bump) -> TyResult<'a, ()> {
    let ident_ty = ty_ctx.ident_ty(&pl.ident)?;
    if ident_ty.mutbl != Mutability::Mut {
        return Err(TyError::AssignToConst(pl.to_place_expr(arena)));
    }
    Ok(())
}

fn ty_check_assign_place<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    pl_expr: &mut PlaceExpr<'a>,
    expr: &mut Expr<'a>,
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    ty_check_expr(ctx, expr, arena)?;
    let place = pl_expr.to_place(arena).unwrap();
    let mut place_ty = ctx.ty_ctx.place_dty(&place)?;
    check_mutable(ctx.ty_ctx, &place, arena)?;

    if !matches!(&place_ty.dty, DataTyKind::Dead(_)) {
        borrow_check::borrow_check(
            &BorrowCheckCtx::new(ctx, vec![], Ownership::Uniq),
            pl_expr,
            arena,
        )
        .map_err(|err| {
            TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Uniq, err)
        })?;
    }

    let mut expr_ty = (*expr.ty.unwrap()).clone();
    let mut expr_dty = match &expr_ty.ty {
        TyKind::Data(dty) => (**dty).clone(),
        TyKind::FnTy(_) => return Err(TyError::UnexpectedType),
    };
    if let Err(err) = unify::sub_unify(
        ctx.kind_ctx,
        ctx.ty_ctx,
        &mut expr_dty,
        &mut place_ty,
        arena,
    ) {
        return Err(match err {
            UnifyError::CannotUnify => {
                TyError::MismatchedDataTypes(place_ty, expr_dty, expr.clone())
            }
            err => TyError::from(err),
        });
    }
    expr_ty.ty = TyKind::Data(arena.alloc(expr_dty.clone()));
    expr.ty = Some(arena.alloc(expr_ty));
    ctx.ty_ctx
        .set_place_dty(&place, expr_dty, arena)
        .without_reborrow_loans(pl_expr);
    pl_expr::ty_check(&PlExprTyCtx::new(ctx, Ownership::Uniq), pl_expr, arena)?;
    Ok(Ty::new(TyKind::Data(arena.alloc(DataTy::new(
        arena,
        DataTyKind::Scalar(ScalarTy::Unit),
    )))))
}

fn ty_check_assign_non_place<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    deref_expr: &mut PlaceExpr<'a>,
    expr: &mut Expr<'a>,
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    ty_check_expr(ctx, expr, arena)?;
    pl_expr::ty_check(&PlExprTyCtx::new(ctx, Ownership::Uniq), deref_expr, arena)?;
    let potential_accesses = borrow_check::access_safety_check(
        &BorrowCheckCtx::new(ctx, vec![], Ownership::Uniq),
        deref_expr,
        arena,
    )
    .map_err(|err| {
        TyError::ConflictingBorrow(Box::new(deref_expr.clone()), Ownership::Uniq, err)
    })?;
    ctx.access_ctx.insert(potential_accesses);

    let mut deref_ty = deref_expr.ty().unwrap().clone();
    let mut expr_ty = (*expr.ty.unwrap()).clone();
    unify::sub_unify(ctx.kind_ctx, ctx.ty_ctx, &mut expr_ty, &mut deref_ty, arena)?;
    expr.ty = Some(arena.alloc(expr_ty));

    if !deref_ty.is_fully_alive() {
        return Err(TyError::String(
            "Trying to assign through reference, to a type which is not fully alive.".to_string(),
        ));
    }
    if matches!(&deref_ty.ty, TyKind::Data(_)) {
        Ok(Ty::new(TyKind::Data(arena.alloc(DataTy::new(
            arena,
            DataTyKind::Scalar(ScalarTy::Unit),
        )))))
    } else {
        Err(TyError::String(
            "Trying to dereference view type which is not allowed.".to_string(),
        ))
    }
}

fn ty_check_idx_assign<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    pl_expr: &mut PlaceExpr<'a>,
    idx: &Nat<'a>,
    e: &mut Expr<'a>,
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    ty_check_expr(ctx, e, arena)?;
    pl_expr::ty_check(&PlExprTyCtx::new(ctx, Ownership::Uniq), pl_expr, arena)?;
    let pl_expr_dty = if let TyKind::Data(dty) = &pl_expr.ty().unwrap().ty {
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
            } = *arr_dty
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
                (n, reff.own, &reff.mem, *sdty)
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
    accessible_memory(ctx.exec.ty.unwrap(), &mem)?;
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
        arena,
    )
    .map_err(|err| TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Shrd, err))?;
    ctx.access_ctx.insert(potential_accesses);
    subty::check(
        ctx.kind_ctx,
        ctx.ty_ctx,
        e.ty.as_ref().unwrap().dty(),
        dty,
        arena,
    )?;
    Ok(Ty::new(TyKind::Data(arena.alloc(DataTy::new(
        arena,
        DataTyKind::Scalar(ScalarTy::Unit),
    )))))
}

// FIXME currently assumes that binary operators exist only for f32 and i32 and that both
//  arguments have to be of the same type
fn ty_check_binary_op<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    bin_op: &BinOp,
    lhs: &mut Expr<'a>,
    rhs: &mut Expr<'a>,
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    // FIXME certain operations should only be allowed for certain data types
    //      true > false is currently valid
    ty_check_expr(ctx, lhs, arena)?;
    ty_check_expr(ctx, rhs, arena)?;
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
        | BinOp::BitOr => (**lhs_ty).clone(),
        BinOp::Eq
        | BinOp::Lt
        | BinOp::Le
        | BinOp::Gt
        | BinOp::Ge
        | BinOp::And
        | BinOp::Or
        | BinOp::Neq => Ty::new(TyKind::Data(
            arena.alloc(DataTy::new(arena, DataTyKind::Scalar(ScalarTy::Bool))),
        )),
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

fn ty_check_unary_op<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    un_op: &UnOp,
    e: &mut Expr<'a>,
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    ty_check_expr(ctx, e, arena)?;
    let e_ty = e.ty.as_ref().unwrap();
    let e_dty = if let TyKind::Data(dty) = &e_ty.ty {
        *dty
    } else {
        return Err(TyError::String("expected data type, but found".to_string()));
    };
    match &e_dty.dty {
        DataTyKind::Scalar(ScalarTy::F32)
        | DataTyKind::Scalar(ScalarTy::F64)
        | DataTyKind::Scalar(ScalarTy::I32)
        | DataTyKind::Scalar(ScalarTy::U8)
        | DataTyKind::Scalar(ScalarTy::U32)
        | DataTyKind::Scalar(ScalarTy::U64) => Ok((**e_ty).clone()),
        _ => Err(TyError::String(format!(
            "Exected a number type (i.e., f32 or i32), but found {:?}",
            e_ty
        ))),
    }
}

fn ty_check_cast<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    e: &mut Expr<'a>,
    dty: &'a DataTy<'a>,
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    ty_check_expr(ctx, e, arena)?;
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
            | DataTyKind::Scalar(ScalarTy::F64) => Ok(Ty::new(TyKind::Data(arena.alloc(dty.clone())))),
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
            | DataTyKind::Scalar(ScalarTy::U64) => Ok(Ty::new(TyKind::Data(arena.alloc(dty.clone())))),
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

fn ty_check_app<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    fn_ident: &mut Ident<'a>,
    gen_args: &mut BumpVec<'a, ArgKinded<'a>>,
    args: &mut [Expr<'a>],
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    // TODO check well-kinded: FrameTyping, Prv, Ty
    let partially_applied_dep_fn_ty = ty_check_dep_app(ctx, fn_ident, gen_args, arena)?;
    for arg in args.iter_mut() {
        ty_check_expr(ctx, arg, arena)?;
    }
    let param_sigs_for_args: Vec<_> = args
        .iter()
        .map(|arg| ParamSig::new(ctx.exec.clone(), arg.ty.unwrap()))
        .collect();
    let ret_dty_placeholder = Ty::new(TyKind::Data(arena.alloc(DataTy::new(
        arena,
        utils::fresh_ident(arena, "ret_ty", DataTyKind::Ident),
    ))));
    let mut mono_fn_ty = unify::inst_fn_ty_scheme(&partially_applied_dep_fn_ty, arena);
    unify::unify(
        &mut FnTy::new(
            arena,
            vec![],
            None,
            param_sigs_for_args,
            ctx.exec.clone(),
            arena.alloc(ret_dty_placeholder),
            vec![],
        ),
        &mut mono_fn_ty,
        arena,
    )?;
    let mut inferred_gen_args =
        infer_kinded_args::infer_kinded_args(&partially_applied_dep_fn_ty, &mono_fn_ty, arena)?;
    gen_args.append(&mut inferred_gen_args);

    if let Some(mut fn_def) = ctx.gl_ctx.pop_fun_def(ctx.compil_unit, &fn_ident.name) {
        // Recursively check function definition with instantiated natural numbers
        let mut nat_names = vec![];
        let mut nat_vals = vec![];
        for (ik, ga) in fn_def.generic_params.iter().zip(gen_args) {
            if let (Kind::Nat, ArgKinded::Nat(n)) = (ik.kind, ga) {
                nat_names.push(ik.ident.name.clone());
                match n.eval(ctx.nat_ctx) {
                    Ok(value) => nat_vals.push(value),
                    Err(err) => {
                        ctx.gl_ctx.push_fun_def(ctx.compil_unit, arena, fn_def);
                        return Err(err.into());
                    }
                }
            }
        }
        if !ctx.gl_ctx.has_been_checked(&fn_ident.name, &nat_vals) {
            let mut called_nat_ctx = NatCtx::with_frame(
                arena,
                nat_names
                    .into_iter()
                    .zip(nat_vals.iter().copied())
                    .collect_in(arena),
            );
            if let Err(err) = ty_check_global_fun_def(
                ctx.gl_ctx,
                &mut called_nat_ctx,
                &mut fn_def,
                ctx.compil_unit,
                arena,
            ) {
                ctx.gl_ctx.push_fun_def(ctx.compil_unit, arena, fn_def);
                return Err(err);
            }
            ctx.gl_ctx
                .push_fun_checked_under_nats(ctx.compil_unit, arena, fn_def, &nat_vals);
        } else {
            ctx.gl_ctx.push_fun_def(ctx.compil_unit, arena, fn_def);
        }
    }

    // TODO check provenance relations
    return Ok((*mono_fn_ty.ret_ty).clone());
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

fn ty_check_dep_app<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    fn_ident: &Ident<'a>,
    gen_args: &[ArgKinded<'a>],
    arena: &'a Bump,
) -> TyResult<'a, FnTy<'a>> {
    //ty_check_expr(ctx, ef)?;
    let fn_ty = ctx.gl_ctx.fn_ty_by_ident(fn_ident)?;
    apply_gen_args_to_fn_ty_checked(ctx.kind_ctx, &ctx.exec, &fn_ty, gen_args, arena)
    // } else {
    //     Err(TyError::String(format!(
    //         "The provided function expression\n {:?}\n does not have a function type.",
    //         ef
    //     )))
    // }
}

fn apply_gen_args_to_fn_ty_checked<'a>(
    kind_ctx: &KindCtx<'a>,
    exec: &ExecExpr<'a>,
    fn_ty: &FnTy<'a>,
    gen_args: &[ArgKinded<'a>],
    arena: &'a Bump,
) -> TyResult<'a, FnTy<'a>> {
    let mut subst_fn_ty = fn_ty.clone();
    apply_gen_args_checked(kind_ctx, &mut subst_fn_ty, gen_args, arena)?;
    apply_exec_checked(&mut subst_fn_ty, exec, arena)?;
    Ok(subst_fn_ty)
}

fn apply_gen_args_checked<'a>(
    kind_ctx: &KindCtx<'a>,
    fn_ty: &mut FnTy<'a>,
    gen_args: &[ArgKinded<'a>],
    arena: &'a Bump,
) -> TyResult<'a, ()> {
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
    utils::subst_idents_kinded(arena, &substituted_gen_idents, gen_args, fn_ty);
    Ok(())
}

fn check_arg_has_correct_kind<'a>(
    kind_ctx: &KindCtx<'a>,
    expected: &Kind,
    kv: &ArgKinded<'a>,
) -> TyResult<'a, ()> {
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
fn apply_exec_checked<'a>(
    fn_ty: &mut FnTy<'a>,
    exec: &ExecExpr<'a>,
    arena: &'a Bump,
) -> TyResult<'a, ()> {
    // TODO reintroduce
    // exec::ty_check(
    //     ctx.kind_ctx,
    //     ctx.ty_ctx,
    //     fn_ty.generic_exec.as_ref(),
    //     &mut fn_ty.exec,
    // )?;
    if let Some(ge) = &fn_ty.generic_exec {
        // FIXME this includes checking for exec < any, therefore not necessarily unifcation (wrong name)
        unify::unify(&mut (*exec.ty.unwrap()).clone(), &mut ge.ty.clone(), arena)?;
        let gen_exec_ident = ge.ident.clone();
        fn_ty.generic_exec = None;
        utils::subst_ident_exec(arena, &gen_exec_ident, exec, fn_ty);
    }
    // if no generic exec was substituted, execs must still be unifable
    unify::unify(&mut fn_ty.exec, &mut exec.clone(), arena)?;
    Ok(())
}

fn ty_check_app_kernel<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    app_kernel: &mut AppKernel<'a>,
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    // current exec = cpu.thread
    if !matches!(ctx.exec.ty.as_ref().unwrap().ty, ExecTyKind::CpuThread) {
        return Err(TyError::String(
            "A kernel must be called from a CPU thread.".to_string(),
        ));
    }
    // type check argument list
    for arg in app_kernel.args.iter_mut() {
        ty_check_expr(ctx, arg, arena)?;
    }
    let mut kernel_exec = ExecExpr::new(
        arena,
        ExecExprKind::new(
            arena,
            BaseExec::GpuGrid(
                arena.alloc(app_kernel.grid_dim.clone()),
                arena.alloc(app_kernel.block_dim.clone()),
            ),
        ),
    );
    exec::ty_check(
        ctx.nat_ctx,
        &TyCtx::new(arena),
        None,
        &mut kernel_exec,
        arena,
    )?;

    let mut kernel_ctx = ExprTyCtx {
        compil_unit: &mut *ctx.compil_unit,
        gl_ctx: &mut *ctx.gl_ctx,
        nat_ctx: ctx.nat_ctx,
        ident_exec: None,
        kind_ctx: ctx.kind_ctx,
        exec: kernel_exec,
        ty_ctx: &mut *ctx.ty_ctx,
        access_ctx: &mut AccessCtx::new(arena),
        unsafe_flag: ctx.unsafe_flag,
    };
    exec::ty_check(
        kernel_ctx.nat_ctx,
        kernel_ctx.ty_ctx,
        None,
        &mut kernel_ctx.exec,
        arena,
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
            IdentTyped::new_in(
                arena,
                arena.alloc_str(&utils::fresh_name("shared_mem")),
                Ty::new(TyKind::Data(arena.alloc(DataTy::new(
                    arena,
                    DataTyKind::At(arena.alloc(dty.clone()), Memory::GpuShared),
                )))),
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
                arena.alloc(PlaceExpr::new(PlaceExprKind::Ident(idt.ident.clone()))),
            ))
        })
        .collect::<Vec<_>>();
    for shrd_mem_arg in refs_to_shrd.iter_mut() {
        ty_check_expr(&mut kernel_ctx, shrd_mem_arg, arena)?;
    }
    // create extended argument list with references to shared memory
    let extended_arg_sigs = app_kernel
        .args
        .iter()
        .map(|a| ParamSig::new(kernel_ctx.exec.clone(), a.ty.unwrap()))
        .chain(refs_to_shrd.into_iter().map(|a| {
            let block_exec = exec_distrib_over_blocks(&kernel_ctx.exec, arena);
            ParamSig::new(block_exec, a.ty.unwrap())
        }))
        .collect::<Vec<_>>();
    // type check function application for generic args and extended argument list
    let partially_applied_dep_fn_ty = ty_check_dep_app(
        &mut kernel_ctx,
        &mut app_kernel.fun_ident,
        &mut app_kernel.gen_args,
        arena,
    )?;
    // build expected type to unify with
    let unit_ty = Ty::new(TyKind::Data(
        arena.alloc(DataTy::new(arena, DataTyKind::Scalar(ScalarTy::Unit))),
    ));
    let mut mono_fn_ty = unify::inst_fn_ty_scheme(&partially_applied_dep_fn_ty, arena);
    unify::unify(
        &mut FnTy::new(
            arena,
            vec![],
            None,
            extended_arg_sigs,
            kernel_ctx.exec.clone(),
            arena.alloc(unit_ty.clone()),
            vec![],
        ),
        &mut mono_fn_ty,
        arena,
    )?;
    let mut inferred_k_args =
        infer_kinded_args::infer_kinded_args(&partially_applied_dep_fn_ty, &mono_fn_ty, arena)?;
    app_kernel.gen_args.append(&mut inferred_k_args);

    if let Some(mut fn_def) = kernel_ctx
        .gl_ctx
        .pop_fun_def(kernel_ctx.compil_unit, &app_kernel.fun_ident.name)
    {
        // Recursively check function definition with instantiated natural numbers
        let mut nat_names = vec![];
        let mut nat_vals = vec![];
        for (ik, ga) in fn_def.generic_params.iter().zip(&app_kernel.gen_args) {
            if let (Kind::Nat, ArgKinded::Nat(n)) = (ik.kind, ga) {
                nat_names.push(ik.ident.name.clone());
                match n.eval(kernel_ctx.nat_ctx) {
                    Ok(value) => nat_vals.push(value),
                    Err(err) => {
                        kernel_ctx
                            .gl_ctx
                            .push_fun_def(kernel_ctx.compil_unit, arena, fn_def);
                        return Err(err.into());
                    }
                }
            }
        }
        if !kernel_ctx
            .gl_ctx
            .has_been_checked(&app_kernel.fun_ident.name, &nat_vals)
        {
            let mut called_nat_ctx = NatCtx::with_frame(
                arena,
                nat_names
                    .into_iter()
                    .zip(nat_vals.iter().copied())
                    .collect_in(arena),
            );
            if let Err(err) = ty_check_global_fun_def(
                kernel_ctx.gl_ctx,
                &mut called_nat_ctx,
                &mut fn_def,
                kernel_ctx.compil_unit,
                arena,
            ) {
                kernel_ctx
                    .gl_ctx
                    .push_fun_def(kernel_ctx.compil_unit, arena, fn_def);
                return Err(err);
            }
            kernel_ctx.gl_ctx.push_fun_checked_under_nats(
                kernel_ctx.compil_unit,
                arena,
                fn_def,
                &nat_vals,
            );
        } else {
            kernel_ctx
                .gl_ctx
                .push_fun_def(kernel_ctx.compil_unit, arena, fn_def);
        }
    }
    Ok(unit_ty)
}

fn exec_distrib_over_blocks<'a>(exec_expr: &ExecExpr<'a>, arena: &'a Bump) -> ExecExpr<'a> {
    let base_clone = ExecExprKind::new(arena, exec_expr.exec.base.clone());
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
    ExecExpr::new(arena, distrib_over_blocks)
}

fn ty_check_tuple<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    elems: &mut [Expr<'a>],
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    for elem in elems.iter_mut() {
        ty_check_expr(ctx, elem, arena)?;
    }
    let elem_tys: TyResult<Vec<_>> = elems
        .iter()
        .map(|elem| match &elem.ty.as_ref().unwrap().ty {
            TyKind::Data(dty) => Ok((**dty).clone()),
            TyKind::FnTy(_) => Err(TyError::String(
                "Tuple elements must be data types, but found function type.".to_string(),
            )),
        })
        .collect();
    Ok(Ty::new(TyKind::Data(arena.alloc(DataTy::new(
        arena,
        DataTyKind::Tuple(elem_tys?.into_iter().collect_in(arena)),
    )))))
}

fn ty_check_proj<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    e: &mut Expr<'a>,
    i: usize,
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    if let ExprKind::PlaceExpr(_) = e.expr {
        panic!("Place expression should have been typechecked by a different rule.")
    }
    ty_check_expr(ctx, e, arena)?;
    let e_dty = if let TyKind::Data(dty) = &e.ty.as_ref().unwrap().ty {
        *dty
    } else {
        return Err(TyError::UnexpectedType);
    };
    let elem_ty = proj_elem_dty(e_dty, i);
    Ok(Ty::new(TyKind::Data(arena.alloc(elem_ty?))))
}

fn ty_check_array<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    elems: &mut BumpVec<'a, Expr<'a>>,
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    assert!(!elems.is_empty());
    for elem in elems.iter_mut() {
        ty_check_expr(ctx, elem, arena)?;
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
        Ok(Ty::new(TyKind::Data(arena.alloc(DataTy::new(
            arena,
            DataTyKind::Array(
                arena.alloc(ty.as_ref().unwrap().dty().clone()),
                Nat::Lit(elems.len()),
            ),
        )))))
    }
}

fn ty_check_literal<'a>(l: &mut Lit, arena: &'a Bump) -> Ty<'a> {
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
    Ty::new(TyKind::Data(
        arena.alloc(DataTy::new(arena, DataTyKind::Scalar(scalar_data))),
    ))
}

fn infer_pattern_ident_tys<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    pattern: &Pattern<'a>,
    pattern_ty: &Ty<'a>,
    arena: &'a Bump,
) -> TyResult<'a, ()> {
    let pattern_dty = if let TyKind::Data(dty) = &pattern_ty.ty {
        *dty
    } else {
        return Err(TyError::UnexpectedType);
    };
    match (pattern, &pattern_dty.dty) {
        (Pattern::Ident(mutbl, ident), _) => {
            let ident_with_annotated_ty = IdentTyped::new_in(
                arena,
                ident.name,
                Ty::new(TyKind::Data(arena.alloc(pattern_dty.clone()))),
                *mutbl,
                ctx.exec.clone(),
            );
            ctx.ty_ctx.append_ident_typed(ident_with_annotated_ty);
            Ok(())
        }
        (Pattern::Wildcard, _) => Ok(()),
        (Pattern::Tuple(patterns), DataTyKind::Tuple(elem_tys)) => {
            for (p, tty) in patterns.iter().zip(elem_tys) {
                infer_pattern_ident_tys(
                    ctx,
                    p,
                    &Ty::new(TyKind::Data(arena.alloc(tty.clone()))),
                    arena,
                )?;
            }
            Ok(())
        }
        _ => Err(TyError::PatternAndTypeDoNotMatch),
    }
}

fn infer_tys_and_append_idents<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    pattern: &Pattern<'a>,
    pattern_ty: &mut Option<&'a Ty<'a>>,
    assign_ty: &mut Ty<'a>,
    arena: &'a Bump,
) -> TyResult<'a, ()> {
    let resolved_ty = if let Some(annotation_ref) = *pattern_ty {
        let mut annotation = annotation_ref.clone();
        unify::sub_unify(ctx.kind_ctx, ctx.ty_ctx, assign_ty, &mut annotation, arena)?;
        let annotation_ref = arena.alloc(annotation);
        *pattern_ty = Some(annotation_ref);
        (*annotation_ref).clone()
    } else {
        assign_ty.clone()
    };
    infer_pattern_ident_tys(ctx, pattern, &resolved_ty, arena)
}

fn ty_check_let<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    pattern: &Pattern<'a>,
    pattern_ty: &mut Option<&'a Ty<'a>>,
    expr: &mut Expr<'a>,
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    ty_check_expr(ctx, expr, arena)?;
    let mut expr_ty = (*expr.ty.unwrap()).clone();
    infer_tys_and_append_idents(ctx, pattern, pattern_ty, &mut expr_ty, arena)?;
    expr.ty = Some(arena.alloc(expr_ty));
    Ok(Ty::new(TyKind::Data(arena.alloc(DataTy::new(
        arena,
        DataTyKind::Scalar(ScalarTy::Unit),
    )))))
}

// TODO respect exec?
fn ty_check_let_uninit<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    annot_exec: &Option<&'a ExecExpr<'a>>,
    ident: &Ident<'a>,
    ty: &Ty<'a>,
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    // TODO is the type well-formed?
    if let TyKind::Data(dty) = &ty.ty {
        let mut exec_expr = if let Some(ex) = annot_exec {
            (*ex).clone()
        } else {
            ctx.exec.clone()
        };
        exec::ty_check(
            ctx.nat_ctx,
            ctx.ty_ctx,
            ctx.ident_exec,
            &mut exec_expr,
            arena,
        )?;
        let ident_with_ty = IdentTyped::new_in(
            arena,
            ident.name,
            Ty::new(TyKind::Data(
                arena.alloc(DataTy::new(arena, DataTyKind::Dead(dty.clone()))),
            )),
            Mutability::Mut,
            exec_expr,
        );
        ctx.ty_ctx.append_ident_typed(ident_with_ty);
        Ok(Ty::new(TyKind::Data(arena.alloc(DataTy::new(
            arena,
            DataTyKind::Scalar(ScalarTy::Unit),
        )))))
    } else {
        Err(TyError::MutabilityNotAllowed(ty.clone()))
    }
}

fn ty_check_seq<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    es: &mut [Expr<'a>],
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    for e in &mut *es {
        ty_check_expr(ctx, e, arena)?;
        ctx.ty_ctx.garbage_collect_loans();
    }
    Ok((*es.last().unwrap().ty.unwrap()).clone())
}

fn ty_check_non_place<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    pl_expr: &mut PlaceExpr<'a>,
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    pl_expr::ty_check(&PlExprTyCtx::new(ctx, Ownership::Shrd), pl_expr, arena)?;
    let mut place_ty = pl_expr.ty().unwrap().clone();
    if !place_ty.is_fully_alive() {
        return Err(TyError::String(format!(
            "Part of Place {:?} was moved before.",
            pl_expr
        )));
    }
    let mut copyable_ty = Ty::new(TyKind::Data(arena.alloc(DataTy::with_constr(
        arena,
        utils::fresh_ident(arena, "pl_deref", DataTyKind::Ident),
        vec![Constraint::Copyable],
    ))));
    unify::unify(&mut place_ty, &mut copyable_ty, arena)?;
    let potential_accesses = borrow_check::access_safety_check(
        &BorrowCheckCtx::new(ctx, vec![], Ownership::Shrd),
        pl_expr,
        arena,
    )
    .map_err(|err| TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Shrd, err))?;
    ctx.access_ctx.insert(potential_accesses);
    if place_ty.copyable() {
        Ok(place_ty)
    } else {
        Err(TyError::String("Data type is not copyable.".to_string()))
    }
}

fn ty_check_place<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    pl_expr: &mut PlaceExpr<'a>,
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    pl_expr::ty_check(&PlExprTyCtx::new(ctx, Ownership::Uniq), pl_expr, arena)?;
    let place = pl_expr.clone().to_place(arena).unwrap();
    let pl_ty = ctx.ty_ctx.place_dty(&place)?;
    if !pl_ty.is_fully_alive() {
        return Err(TyError::String(format!(
            "Part of Place {:?} was moved before.",
            pl_expr
        )));
    }
    if pl_ty.copyable() {
        // TODO refactor
        borrow_check::access_safety_check(
            &BorrowCheckCtx::new(ctx, vec![], Ownership::Shrd),
            pl_expr,
            arena,
        )
        .map_err(|err| {
            TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Shrd, err)
        })?;
    } else {
        borrow_check::access_safety_check(
            &BorrowCheckCtx::new(ctx, vec![], Ownership::Uniq),
            pl_expr,
            arena,
        )
        .map_err(|err| {
            TyError::ConflictingBorrow(Box::new(pl_expr.clone()), Ownership::Uniq, err)
        })?;
        ctx.ty_ctx.kill_place(&place, arena);
    };
    Ok(Ty::new(TyKind::Data(arena.alloc(pl_ty))))
}

fn ty_check_borrow<'a>(
    ctx: &mut ExprTyCtx<'_, 'a>,
    prv_val_name: &Option<&str>,
    own: Ownership,
    pl_expr: &mut PlaceExpr<'a>,
    arena: &'a Bump,
) -> TyResult<'a, Ty<'a>> {
    // If borrowing a place uniquely, is it mutable?
    if let Some(place) = pl_expr.to_place(arena) {
        if own == Ownership::Uniq && ctx.ty_ctx.ident_ty(&place.ident)?.mutbl == Mutability::Const {
            return Err(TyError::ConstBorrow(pl_expr.clone()));
        }
    }
    let prv_val_name = infer_and_append_prv(ctx.ty_ctx, prv_val_name);
    if !ctx.ty_ctx.loans_in_prv(&prv_val_name)?.is_empty() {
        return Err(TyError::PrvValueAlreadyInUse(prv_val_name));
    }
    let mems = pl_expr::ty_check_and_passed_mems(&PlExprTyCtx::new(ctx, own), pl_expr, arena)?;
    let loans =
        borrow_check::access_safety_check(&BorrowCheckCtx::new(ctx, vec![], own), pl_expr, arena)
            .map_err(|err| TyError::ConflictingBorrow(Box::new(pl_expr.clone()), own, err))?;
    mems.iter()
        .try_for_each(|mem| accessible_memory(ctx.exec.ty.unwrap(), mem))?;
    let pl_expr_ty = pl_expr.ty().unwrap();
    if !pl_expr_ty.is_fully_alive() {
        return Err(TyError::String(
            "The place was at least partially moved before.".to_string(),
        ));
    }
    let (reffed_ty, rmem) = match &pl_expr_ty.ty {
        TyKind::Data(dty) => match &dty.dty {
            DataTyKind::Dead(_) => panic!("Cannot happen because of the alive check."),
            DataTyKind::At(inner_ty, m) => ((**inner_ty).clone(), m.clone()),
            _ => (
                (**dty).clone(),
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
    let res_dty = DataTy::new(
        arena,
        DataTyKind::Ref(arena.alloc(RefDty::new(
            arena,
            Provenance::Value(arena.alloc_str(&prv_val_name)),
            own,
            rmem,
            reffed_ty,
        ))),
    );
    ctx.ty_ctx.extend_loans_for_prv(&prv_val_name, loans)?;
    Ok(Ty::new(TyKind::Data(arena.alloc(res_dty))))
}

fn allowed_mem_for_exec<'a>(exec_ty: &ExecTyKind<'a>) -> Vec<Memory<'a>> {
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

pub fn accessible_memory<'a>(exec_ty: &ExecTy<'a>, mem: &Memory<'a>) -> TyResult<'a, ()> {
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
fn ty_well_formed<'a>(
    kind_ctx: &KindCtx<'a>,
    ty_ctx: &TyCtx<'a>,
    exec_ty: &ExecTy<'a>,
    ty: &Ty<'a>,
    arena: &'a Bump,
) -> TyResult<'a, ()> {
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
                        let elem_ty = Ty::new(TyKind::Data(reff.dty));
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
                                if let TyKind::Data(pl_expr_dty) = borrowed_pl_expr.ty().unwrap().ty {
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
                        ty_well_formed(kind_ctx, ty_ctx, exec_ty, &elem_ty, arena)?;
                    }
                    Provenance::Ident(ident) => {
                        let elem_ty = Ty::new(TyKind::Data(reff.dty));
                        if !kind_ctx.ident_of_kind_exists(ident, Kind::Provenance) {
                            Err(CtxError::KindedIdentNotFound(ident.clone()))?
                        }
                        ty_well_formed(kind_ctx, ty_ctx, exec_ty, &elem_ty, arena)?;
                    }
                };
            }
            DataTyKind::Tuple(elem_dtys) => {
                for elem_dty in elem_dtys {
                    ty_well_formed(
                        kind_ctx,
                        ty_ctx,
                        exec_ty,
                        &Ty::new(TyKind::Data(arena.alloc(elem_dty.clone()))),
                        arena
                    )?;
                }
            }
            DataTyKind::Struct(struct_decl) => {
                for (_, dty) in &struct_decl.fields {
                    ty_well_formed(kind_ctx, ty_ctx, exec_ty, &Ty::new(TyKind::Data(arena.alloc(dty.clone()))), arena)?;
                }
            }
            DataTyKind::Array(elem_dty, n) => {
                ty_well_formed(
                    kind_ctx,
                    ty_ctx,
                    exec_ty,
                    &Ty::new(TyKind::Data(elem_dty.clone())),
                    arena
                )?;
                // TODO well-formed nat
            }
            DataTyKind::ArrayShape(elem_dty, n) => {
                ty_well_formed(
                    kind_ctx,
                    ty_ctx,
                    exec_ty,
                    &Ty::new(TyKind::Data(elem_dty.clone())),
                    arena
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
                    arena
                )?;
            }
            DataTyKind::At(elem_dty, _) => {
                ty_well_formed(
                    kind_ctx,
                    ty_ctx,
                    exec_ty,
                    &Ty::new(TyKind::Data(elem_dty.clone())),
                    arena
                )?;
            }
        },
        // TODO check well-formedness of Nats
        TyKind::FnTy(fn_ty) => {
            let mut extended_kind_ctx = kind_ctx.clone();
            extended_kind_ctx.append_idents(fn_ty.generics.clone());
            ty_well_formed(&extended_kind_ctx, ty_ctx, exec_ty, &fn_ty.ret_ty, arena)?;
            for param_sig in &fn_ty.param_sigs {
                // TODO which checks are necessary for the execution resource in
                //  param_sig.exec_expr?
                ty_well_formed(&extended_kind_ctx, ty_ctx, exec_ty, &param_sig.ty, arena)?;
            }
        }
    }
    Ok(())
}

pub fn callable_in<'a>(
    callee_exec_ty: &ExecTy<'a>,
    caller_exec_ty: &ExecTy<'a>,
    arena: &'a Bump,
) -> bool {
    if &callee_exec_ty.ty == &ExecTyKind::Any {
        true
    } else {
        let res = unify::unify(
            &mut callee_exec_ty.clone(),
            &mut caller_exec_ty.clone(),
            arena,
        );
        res.is_ok()
    }
}

fn expand_exec_expr<'a>(
    ctx: &ExprTyCtx<'_, 'a>,
    exec_expr: &ExecExpr<'a>,
    arena: &'a Bump,
) -> TyResult<'a, ExecExpr<'a>> {
    match &exec_expr.exec.base {
        BaseExec::CpuThread | BaseExec::GpuGrid(_, _) => Ok(exec_expr.clone()),
        BaseExec::Ident(ident) => {
            let inner_exec_expr = ctx.ty_ctx.get_exec_expr_for_exec_ident(ident)?;
            let new_base = inner_exec_expr.exec.base.clone();
            let mut new_exec_path = inner_exec_expr.exec.path.clone();
            new_exec_path.append(&mut exec_expr.exec.path.clone());
            let mut expanded_exec_expr: ExecExpr =
                ExecExpr::new(arena, ExecExprKind::with_path(new_base, new_exec_path));
            exec::ty_check(
                ctx.nat_ctx,
                ctx.ty_ctx,
                ctx.ident_exec,
                &mut expanded_exec_expr,
                arena,
            )?;
            Ok(expanded_exec_expr)
        }
    }
}

fn legal_exec_under_current<'a>(
    ctx: &ExprTyCtx<'_, 'a>,
    exec: &ExecExpr<'a>,
    arena: &'a Bump,
) -> TyResult<'a, ()> {
    let expanded_exec_expr = expand_exec_expr(ctx, exec, arena)?;
    if ctx.exec != expanded_exec_expr {
        let current_exec_ty = &ctx.exec.ty.as_ref().unwrap().ty;
        let expanded_exec_ty = &expanded_exec_expr.ty.unwrap().ty;
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
pub fn proj_elem_dty<'a>(dty: &'a DataTy<'a>, i: usize) -> TyResult<'a, DataTy<'a>> {
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
