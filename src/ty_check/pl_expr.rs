use super::borrow_check::BorrowCheckCtx;
use super::error::TyError;
use super::TyResult;
use crate::arena_ast::{
    utils, DataTy, DataTyKind, ExecExpr, ExecTyKind, FnTy, Ident, IdentExec, Memory, Nat, NatCtx,
    Ownership, ParamSig, PlaceExpr, PlaceExprKind, Provenance, Ty, TyKind, View,
};
use crate::ty_check::ctxs::{AccessCtx, GlobalCtx, KindCtx, TyCtx};

use crate::ty_check::unify;
use crate::ty_check::unify::ConstrainMap;
use crate::ty_check::{exec, ExprTyCtx};
use bumpalo::collections::Vec as BumpVec;
use bumpalo::Bump;

pub(super) struct PlExprTyCtx<'ctx, 'a> {
    gl_ctx: &'ctx GlobalCtx<'a>,
    nat_ctx: &'ctx NatCtx<'a>,
    kind_ctx: &'ctx KindCtx<'a>,
    ident_exec: Option<&'ctx IdentExec<'a>>,
    exec: ExecExpr<'a>,
    ty_ctx: &'ctx TyCtx<'a>,
    exec_borrow_ctx: &'ctx AccessCtx<'a>,
    own: Ownership,
}

impl<'ctx, 'a> PlExprTyCtx<'ctx, 'a> {
    pub(super) fn new(expr_ty_ctx: &'ctx ExprTyCtx<'_, 'a>, own: Ownership) -> Self {
        PlExprTyCtx {
            gl_ctx: &*expr_ty_ctx.gl_ctx,
            nat_ctx: &*expr_ty_ctx.nat_ctx,
            kind_ctx: &*expr_ty_ctx.kind_ctx,
            ident_exec: expr_ty_ctx.ident_exec,
            exec: expr_ty_ctx.exec.clone(),
            ty_ctx: &*expr_ty_ctx.ty_ctx,
            exec_borrow_ctx: &*expr_ty_ctx.access_ctx,
            own,
        }
    }
}

impl<'ctx, 'a> From<&'ctx BorrowCheckCtx<'_, 'a>> for PlExprTyCtx<'ctx, 'a> {
    fn from(ctx: &'ctx BorrowCheckCtx<'_, 'a>) -> Self {
        PlExprTyCtx {
            gl_ctx: ctx.gl_ctx,
            nat_ctx: ctx.nat_ctx,
            kind_ctx: ctx.kind_ctx,
            ident_exec: ctx.ident_exec,
            exec: ctx.exec.clone(),
            ty_ctx: ctx.ty_ctx,
            exec_borrow_ctx: ctx.access_ctx,
            own: Ownership::Shrd,
        }
    }
}

// Δ; Γ ⊢ω p:τ
// p in an ω context has type τ under Δ and Γ
pub(super) fn ty_check<'a>(
    ctx: &PlExprTyCtx<'_, 'a>,
    pl_expr: &mut PlaceExpr<'a>,
    arena: &'a Bump,
) -> TyResult<'a, ()> {
    let _mem = ty_check_and_passed_mems(ctx, pl_expr, arena)?;
    Ok(())
}

pub(super) fn ty_check_and_passed_mems<'a>(
    ctx: &PlExprTyCtx<'_, 'a>,
    pl_expr: &mut PlaceExpr<'a>,
    arena: &'a Bump,
) -> TyResult<'a, Vec<Memory<'a>>> {
    let (mem, _) = ty_check_and_passed_mems_prvs(ctx, pl_expr, arena)?;
    Ok(mem)
}

// Δ; Γ ⊢ω p:τ,{ρ}
// p in an ω context has type τ under Δ and Γ, passing through provenances in Vec<ρ>
fn ty_check_and_passed_mems_prvs<'a>(
    ctx: &PlExprTyCtx<'_, 'a>,
    pl_expr: &mut PlaceExpr<'a>,
    arena: &'a Bump,
) -> TyResult<'a, (Vec<Memory<'a>>, Vec<Provenance<'a>>)> {
    let (ty, mem, prvs) = match &mut pl_expr.pl_expr {
        // TC-Var
        PlaceExprKind::Ident(ident) => ty_check_ident(ctx, ident)?,
        // TC-Proj
        PlaceExprKind::Proj(tuple_expr, n) => {
            let mut owned = (**tuple_expr).clone();
            let result = ty_check_proj(ctx, &mut owned, *n, arena)?;
            *tuple_expr = arena.alloc(owned);
            result
        }
        // TC-Field
        PlaceExprKind::FieldProj(struct_expr, ident) => {
            let mut owned = (**struct_expr).clone();
            let result = ty_check_field_proj(ctx, &mut owned, ident, arena)?;
            *struct_expr = arena.alloc(owned);
            result
        }
        // TC-Deref
        PlaceExprKind::Deref(borr_expr) => {
            let mut owned = (**borr_expr).clone();
            let result = ty_check_deref(ctx, &mut owned, arena)?;
            *borr_expr = arena.alloc(owned);
            result
        }
        // TC-Select
        PlaceExprKind::Select(pl_expr, select_exec) => {
            let mut owned_place = (**pl_expr).clone();
            let mut owned_exec = (**select_exec).clone_in(arena);
            let result = ty_check_select(ctx, &mut owned_place, &mut owned_exec, arena)?;
            *pl_expr = arena.alloc(owned_place);
            *select_exec = arena.alloc(owned_exec);
            result
        }
        PlaceExprKind::View(pl_expr, view) => {
            let mut owned_place = (**pl_expr).clone();
            let mut owned_view = (**view).clone_in(arena);
            let result = ty_check_view_pl_expr(ctx, &mut owned_place, &mut owned_view, arena)?;
            *pl_expr = arena.alloc(owned_place);
            *view = arena.alloc(owned_view);
            result
        }
        PlaceExprKind::Idx(pl_expr, idx) => {
            let mut owned_place = (**pl_expr).clone();
            let result = ty_check_index(ctx, &mut owned_place, idx, arena)?;
            *pl_expr = arena.alloc(owned_place);
            result
        }
    };

    let _ = pl_expr.ty.set(arena.alloc(ty));
    Ok((mem, prvs))
}

fn ty_check_view_pl_expr<'a>(
    ctx: &PlExprTyCtx<'_, 'a>,
    pl_expr: &mut PlaceExpr<'a>,
    view: &mut View<'a>,
    arena: &'a Bump,
) -> TyResult<'a, (Ty<'a>, Vec<Memory<'a>>, Vec<Provenance<'a>>)> {
    let (mems, prvs) = ty_check_and_passed_mems_prvs(ctx, pl_expr, arena)?;
    let view_fn_ty = ty_check_view(ctx, view, arena)?;
    let in_dty_ref: &'a DataTy<'a> = {
        let tmp = pl_expr.ty.get().unwrap().dty().clone_in(arena);
        arena.alloc(tmp)
    };
    let (res_dty, constr_map) = ty_check_app_view_fn_ty(ctx, in_dty_ref, view_fn_ty, arena)?;
    unify::substitute(&constr_map, view, arena);
    Ok((Ty::new(TyKind::Data(arena.alloc(res_dty))), mems, prvs))
}

fn ty_check_app_view_fn_ty<'a>(
    ctx: &PlExprTyCtx<'_, 'a>,
    in_dty: &DataTy<'a>,
    view_fn_ty: FnTy<'a>,
    arena: &'a Bump,
) -> TyResult<'a, (DataTy<'a>, ConstrainMap<'a>)> {
    let arg_dty_fn_ty = FnTy::new(
        arena,
        std::iter::empty(),
        None,
        [ParamSig::new(
            ctx.exec.clone(),
            arena.alloc(Ty::new(TyKind::Data(arena.alloc(in_dty.clone_in(arena))))),
        )],
        ctx.exec.clone(),
        arena.alloc(Ty::new(TyKind::Data(arena.alloc(DataTy::new(
            arena,
            DataTyKind::Ident(Ident::new_impli(arena, "ret_dty")),
        ))))),
        std::iter::empty(),
    );

    let arg_ptr = arena.alloc(arg_dty_fn_ty);
    let view_ptr = arena.alloc(view_fn_ty);

    let (constr_map, _prv) = unify::constrain(arg_ptr, view_ptr, arena)?;

    let mut res_dty = DataTy::new(arena, DataTyKind::Ident(Ident::new_impli(arena, "ret_dty")));
    unify::substitute(&constr_map, &mut res_dty, arena);

    Ok((res_dty, constr_map))
}

fn ty_check_view<'a, 'm>(
    ctx: &PlExprTyCtx<'_, 'a>,
    view: &'m mut View<'a>,
    arena: &'a Bump,
) -> TyResult<'a, FnTy<'a>> {
    let mut arg_tys = BumpVec::new_in(arena);
    for v in view.args.iter_mut() {
        let inner = ty_check_view(ctx, v, arena)?;
        arg_tys.push(Ty::new(TyKind::FnTy(arena.alloc(inner))));
    }

    let name_ref: &'a Ident<'a> = arena.alloc(view.name.clone());
    let view_fn_ty = ctx.gl_ctx.fn_ty_by_ident(name_ref)?;

    let gen_args_ref = {
        let mut tmp = BumpVec::new_in(arena);
        for ga in view.gen_args.iter() {
            tmp.push(ga.clone_in(arena));
        }
        arena.alloc(tmp)
    };

    let partially_applied_view_fn_ty = arena.alloc(super::apply_gen_args_to_fn_ty_checked(
        ctx.kind_ctx,
        &ctx.exec,
        view_fn_ty,
        gen_args_ref,
        arena,
    )?);

    let actual_view_fn_ty = arena.alloc(create_view_ty_with_input_view_and_free_ret(
        &ctx.exec, arg_tys, arena,
    ));

    let mono_fn_ty = arena.alloc(unify::inst_fn_ty_scheme(
        partially_applied_view_fn_ty,
        arena,
    ));

    let (constr_map, _) = unify::constrain(actual_view_fn_ty, mono_fn_ty, arena)?;

    unify::substitute(&constr_map, view, arena);

    let inferred_k_args = super::infer_kinded_args::infer_kinded_args(
        partially_applied_view_fn_ty,
        mono_fn_ty,
        arena,
    )?;
    view.gen_args.extend(inferred_k_args.into_iter());

    let res_view_ty = FnTy::new(
        arena,
        std::iter::empty(),
        actual_view_fn_ty.generic_exec.clone(),
        std::iter::once(actual_view_fn_ty.param_sigs.pop().expect("param exists")),
        actual_view_fn_ty.exec.clone(),
        actual_view_fn_ty.ret_ty, // &'a Ty<'a>
        std::iter::empty(),
    );

    Ok(res_view_ty)
}

fn create_view_ty_with_input_view_and_free_ret<'a>(
    exec: &ExecExpr<'a>,
    mut arg_tys: BumpVec<'a, Ty<'a>>,
    arena: &'a Bump,
) -> FnTy<'a> {
    arg_tys.push(Ty::new(TyKind::Data(arena.alloc(DataTy::new(
        arena,
        utils::fresh_ident(arena, "in_view_dty", DataTyKind::Ident),
    )))));

    let mut param_sigs = BumpVec::new_in(arena);
    for ty in arg_tys.into_iter() {
        let ty_ref: &'a Ty<'a> = arena.alloc(ty);
        param_sigs.push(ParamSig::new(exec.clone(), ty_ref));
    }

    let ret_ty_ref: &'a Ty<'a> = arena.alloc(Ty::new(TyKind::Data(arena.alloc(DataTy::new(
        arena,
        utils::fresh_ident(arena, "view_out_dty", DataTyKind::Ident),
    )))));

    FnTy::new(
        arena,
        std::iter::empty(),
        None,
        param_sigs,
        exec.clone(),
        ret_ty_ref,
        std::iter::empty(),
    )
}

fn ty_check_ident<'a>(
    ctx: &PlExprTyCtx<'_, 'a>,
    ident: &Ident<'a>,
) -> TyResult<'a, (Ty<'a>, Vec<Memory<'a>>, Vec<Provenance<'a>>)> {
    // if let Ok(tty) = ctx.ty_ctx.ty_of_ident(ident) {
    let tty = ctx.ty_ctx.ty_of_ident(ident)?;
    if !&tty.is_fully_alive() {
        return Err(TyError::String(format!(
            "The value in `{}` has been moved out.",
            ident
        )));
    }
    // FIXME Should throw an error if thread local memory is accessed by a block
    //  for example.
    let mem = default_mem_by_exec(&ctx.exec.ty.as_ref().unwrap().ty);
    Ok((
        tty.clone(),
        if mem.is_some() {
            vec![mem.unwrap()]
        } else {
            vec![]
        },
        vec![],
    ))
    // } else {
    //     let fn_ty = ctx.gl_ctx.fn_ty_by_ident(ident)?;
    //     Ok((Ty::new(TyKind::FnTy(Box::new(fn_ty))), vec![], vec![]))
    // }
}

fn default_mem_by_exec<'a>(exec_ty: &ExecTyKind<'a>) -> Option<Memory<'a>> {
    match exec_ty {
        ExecTyKind::CpuThread => Some(Memory::CpuMem),
        ExecTyKind::GpuThread => Some(Memory::GpuLocal),
        ExecTyKind::GpuGrid(_, _) => Some(Memory::GpuLocal),
        ExecTyKind::GpuToThreads(_, _) => Some(Memory::GpuLocal),
        ExecTyKind::GpuBlockGrp(_, _) => Some(Memory::GpuLocal),
        ExecTyKind::GpuThreadGrp(_) => Some(Memory::GpuLocal),
        ExecTyKind::GpuBlock(_) => Some(Memory::GpuLocal),
        ExecTyKind::GpuWarpGrp(_) => Some(Memory::GpuLocal),
        ExecTyKind::GpuWarp => Some(Memory::GpuLocal),
        ExecTyKind::Any => None,
    }
}

// TODO refactor by fusing with ty_check_field_proj
fn ty_check_proj<'a>(
    ctx: &PlExprTyCtx<'_, 'a>,
    tuple_expr: &mut PlaceExpr<'a>,
    n: usize,
    arena: &'a Bump,
) -> TyResult<'a, (Ty<'a>, Vec<Memory<'a>>, Vec<Provenance<'a>>)> {
    let (mem, passed_prvs) = ty_check_and_passed_mems_prvs(ctx, tuple_expr, arena)?;
    let tuple_dty = match &tuple_expr.ty.get().unwrap().ty {
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
                    Ty::new(TyKind::Data(arena.alloc(dty.clone()))),
                    mem,
                    passed_prvs,
                ))
            } else {
                Err(TyError::String(
                    "Trying to access non existing tuple element.".to_string(),
                ))
            }
        }
        dty_kind => Err(TyError::ExpectedTupleType(
            TyKind::Data(arena.alloc(DataTy::new(arena, dty_kind.clone()))),
            tuple_expr.clone(),
        )),
    }
}

fn ty_check_field_proj<'a>(
    ctx: &PlExprTyCtx<'_, 'a>,
    struct_expr: &mut PlaceExpr<'a>,
    ident: &Ident<'a>,
    arena: &'a Bump,
) -> TyResult<'a, (Ty<'a>, Vec<Memory<'a>>, Vec<Provenance<'a>>)> {
    let (mem, passed_prvs) = ty_check_and_passed_mems_prvs(ctx, struct_expr, arena)?;
    let struct_dty = match &struct_expr.ty.get().unwrap().ty {
        TyKind::Data(dty) => dty,
        ty_kind => {
            return Err(TyError::ExpectedTupleType(
                ty_kind.clone(),
                struct_expr.clone(),
            ));
        }
    };

    match &struct_dty.dty {
        DataTyKind::Struct(struct_decl) => {
            if let Some(field) = struct_decl.fields.iter().find(|f| &f.0 == ident) {
                Ok((
                    Ty::new(TyKind::Data(arena.alloc(field.1.clone()))),
                    mem,
                    passed_prvs,
                ))
            } else {
                Err(TyError::String(
                    "Trying to access non existing struct field.".to_string(),
                ))
            }
        }
        dty_kind => Err(TyError::ExpectedTupleType(
            TyKind::Data(arena.alloc(DataTy::new(arena, dty_kind.clone()))),
            struct_expr.clone(),
        )),
    }
}

fn ty_check_deref<'a>(
    ctx: &PlExprTyCtx<'_, 'a>,
    borr_expr: &mut PlaceExpr<'a>,
    arena: &'a Bump,
) -> TyResult<'a, (Ty<'a>, Vec<Memory<'a>>, Vec<Provenance<'a>>)> {
    let (mut inner_mem, mut passed_prvs) = ty_check_and_passed_mems_prvs(ctx, borr_expr, arena)?;
    let borr_dty = if let TyKind::Data(dty) = &borr_expr.ty.get().unwrap().ty {
        dty
    } else {
        return Err(TyError::String(
            "Trying to dereference non reference type.".to_string(),
        ));
    };
    match &borr_dty.dty {
        DataTyKind::Ref(reff) => {
            if reff.own < ctx.own {
                return Err(TyError::String(
                    "Trying to dereference and mutably use a shrd reference.".to_string(),
                ));
            }
            passed_prvs.push(reff.rgn.clone());
            inner_mem.push(reff.mem.clone());
            Ok((
                Ty::new(TyKind::Data(arena.alloc(reff.dty.clone()))),
                inner_mem,
                passed_prvs,
            ))
        }
        DataTyKind::RawPtr(dty) => {
            // TODO is anything of this correct?
            Ok((
                Ty::new(TyKind::Data(arena.alloc(dty.clone()))),
                inner_mem,
                passed_prvs,
            ))
        }
        _ => Err(TyError::String(
            "Trying to dereference non reference type.".to_string(),
        )),
    }
}

fn ty_check_select<'a>(
    ctx: &PlExprTyCtx<'_, 'a>,
    p: &mut PlaceExpr<'a>,
    select_exec: &mut ExecExpr<'a>,
    arena: &'a Bump,
) -> TyResult<'a, (Ty<'a>, Vec<Memory<'a>>, Vec<Provenance<'a>>)> {
    exec::ty_check(ctx.nat_ctx, ctx.ty_ctx, ctx.ident_exec, select_exec, arena)?;
    // FIXME this check is required for uniq accesses, but not for shared accesses because there
    //  the duplication of accesses is fine. Move this check into ownership/borrow checking?
    //    if &ctx.exec != select_exec {
    //        return Err(TyError::String(
    //            "Trying select memory for illegal combination of excution resources.".to_string(),
    //        ));
    //    }
    let mut outer_exec = select_exec.remove_last_distrib(arena);
    exec::ty_check(
        ctx.nat_ctx,
        ctx.ty_ctx,
        ctx.ident_exec,
        &mut outer_exec,
        arena,
    )?;
    let outer_ctx = PlExprTyCtx {
        gl_ctx: ctx.gl_ctx,
        nat_ctx: ctx.nat_ctx,
        kind_ctx: ctx.kind_ctx,
        ident_exec: ctx.ident_exec,
        exec: outer_exec,
        ty_ctx: ctx.ty_ctx,
        exec_borrow_ctx: ctx.exec_borrow_ctx,
        own: ctx.own,
    };
    let (mems, prvs) = ty_check_and_passed_mems_prvs(&outer_ctx, p, arena)?;
    let mut p_dty = p.ty.get().unwrap().dty().clone_in(arena);
    match p_dty.dty {
        DataTyKind::Array(elem_dty, _n) | DataTyKind::ArrayShape(elem_dty, _n) => {
            // TODO check sizes
            // if n != distrib_exec.active_distrib_size() {
            //     return Err(TyError::String("There must be as many elements in the view
            //  as there exist execution resources that select from it.".to_string()));
            // }
            p_dty = (*elem_dty).clone_in(arena);
        }
        _ => {
            return Err(TyError::String("Expected an array or view.".to_string()));
        }
    }
    Ok((Ty::new(TyKind::Data(arena.alloc(p_dty))), mems, prvs))
}

fn ty_check_index<'a>(
    ctx: &PlExprTyCtx<'_, 'a>,
    pl_expr: &mut PlaceExpr<'a>,
    idx: &Nat<'a>,
    arena: &'a Bump,
) -> TyResult<'a, (Ty<'a>, Vec<Memory<'a>>, Vec<Provenance<'a>>)> {
    let (mems, passed_prvs) = ty_check_and_passed_mems_prvs(ctx, pl_expr, arena)?;

    let pl_expr_dty = if let TyKind::Data(dty) = &pl_expr.ty.get().unwrap().ty {
        dty
    } else {
        return Err(TyError::String(
            "Trying to index into non array type.".to_string(),
        ));
    };
    let (elem_dty_ref, n_ref): (&'a DataTy<'a>, &'a Nat<'a>) = match &pl_expr_dty.dty {
        DataTyKind::Array(elem_dty, n) | DataTyKind::ArrayShape(elem_dty, n) => (*elem_dty, n),
        DataTyKind::At(arr_dty, _) => {
            if let DataTyKind::Array(elem_ty, n) = &arr_dty.dty {
                (*elem_ty, n)
            } else {
                return Err(TyError::String(
                    "Trying to index into non array type.".to_string(),
                ));
            }
        }
        _ => {
            return Err(TyError::String(
                "Trying to index into non array type.".to_string(),
            ))
        }
    };

    if n_ref.eval(ctx.nat_ctx)? <= idx.eval(ctx.nat_ctx)? {
        return Err(TyError::String(
            "Trying to access array out-of-bounds.".to_string(),
        ));
    }

    let elem_dty_owned = elem_dty_ref.clone_in(arena);

    Ok((
        Ty::new(TyKind::Data(arena.alloc(elem_dty_owned))),
        mems,
        passed_prvs,
    ))
}
