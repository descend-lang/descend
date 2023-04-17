use super::borrow_check::BorrowCheckCtx;
use super::error::TyError;
use super::TyResult;
use crate::ast::{
    utils, BinOpNat, DataTy, DataTyKind, ExecExpr, ExecTy, ExecTyKind, FnTy, Ident, IdentExec,
    Memory, Nat, Ownership, PlaceExpr, PlaceExprKind, Provenance, RefDty, Ty, TyKind, View,
};
use crate::ty_check::ctxs::{AccessCtx, GlobalCtx, KindCtx, TyCtx};

use crate::ty_check::{accessible_memory, exec, unify, ExprTyCtx};

pub(super) struct PlExprTyCtx<'ctxt> {
    gl_ctx: &'ctxt GlobalCtx,
    kind_ctx: &'ctxt KindCtx,
    ident_exec: &'ctxt IdentExec,
    exec: ExecExpr,
    ty_ctx: &'ctxt TyCtx,
    exec_borrow_ctx: &'ctxt AccessCtx,
    own: Ownership,
}

impl<'ctxt> PlExprTyCtx<'ctxt> {
    pub(super) fn new(expr_ty_ctx: &'ctxt ExprTyCtx, own: Ownership) -> Self {
        PlExprTyCtx {
            gl_ctx: &*expr_ty_ctx.gl_ctx,
            kind_ctx: &*expr_ty_ctx.kind_ctx,
            ident_exec: &*expr_ty_ctx.ident_exec,
            exec: expr_ty_ctx.exec.clone(),
            ty_ctx: &*expr_ty_ctx.ty_ctx,
            exec_borrow_ctx: &*expr_ty_ctx.access_ctx,
            own,
        }
    }
}

impl<'ctxt> From<&'ctxt BorrowCheckCtx<'ctxt>> for PlExprTyCtx<'ctxt> {
    fn from(ctx: &'ctxt BorrowCheckCtx<'ctxt>) -> Self {
        PlExprTyCtx::<'ctxt> {
            gl_ctx: ctx.gl_ctx,
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
pub(super) fn ty_check(ctx: &PlExprTyCtx, pl_expr: &mut PlaceExpr) -> TyResult<()> {
    let _mem = ty_check_and_passed_mems(ctx, pl_expr)?;
    Ok(())
}

pub(super) fn ty_check_and_passed_mems(
    ctx: &PlExprTyCtx,
    pl_expr: &mut PlaceExpr,
) -> TyResult<Vec<Memory>> {
    let (mem, _) = ty_check_and_passed_mems_prvs(ctx, pl_expr)?;
    Ok(mem)
}

// Δ; Γ ⊢ω p:τ,{ρ}
// p in an ω context has type τ under Δ and Γ, passing through provenances in Vec<ρ>
fn ty_check_and_passed_mems_prvs(
    ctx: &PlExprTyCtx,
    pl_expr: &mut PlaceExpr,
) -> TyResult<(Vec<Memory>, Vec<Provenance>)> {
    let (ty, mem, prvs) = match &mut pl_expr.pl_expr {
        // TC-Var
        PlaceExprKind::Ident(ident) => ty_check_ident(ctx, ident)?,
        // TC-Proj
        PlaceExprKind::Proj(tuple_expr, n) => ty_check_proj(ctx, tuple_expr, *n)?,
        // TC-Deref
        PlaceExprKind::Deref(borr_expr) => ty_check_deref(ctx, borr_expr)?,
        // TC-Select
        PlaceExprKind::Select(p, select_exec) => ty_check_select(ctx, p, select_exec)?,
        // TC-Split-Proj
        PlaceExprKind::SplitAt(split_pos, split_pl_expr) => {
            ty_check_split_at(ctx, split_pl_expr, split_pos)?
        }
        PlaceExprKind::View(pl_expr, view) => ty_check_view_pl_expr(ctx, pl_expr, view)?,
        PlaceExprKind::Idx(pl_expr, idx) => ty_check_index_copy(ctx, pl_expr, idx)?,
    };
    pl_expr.ty = Some(Box::new(ty));
    Ok((mem, prvs))
}

fn ty_check_view_pl_expr(
    ctx: &PlExprTyCtx,
    pl_expr: &mut PlaceExpr,
    view: &mut [View],
) -> TyResult<(Ty, Vec<Memory>, Vec<Provenance>)> {
    let (mems, prvs) = ty_check_and_passed_mems_prvs(ctx, pl_expr)?;
    let composed_views_fn_ty = ty_check_composed_views(ctx, view)?;
    let in_dty = pl_expr.ty.as_ref().unwrap().dty().clone();
    let res_dty = ty_check_app_view_fn_ty(ctx, &in_dty, composed_views_fn_ty)?;
    Ok((Ty::new(TyKind::Data(Box::new(res_dty))), mems, prvs))
}

fn ty_check_composed_views(ctx: &PlExprTyCtx, views: &mut [View]) -> TyResult<FnTy> {
    let fst_view_fn_ty = ty_check_view(ctx, &mut views[0])?;
    let mut ret_dty = fst_view_fn_ty.ret_ty.dty().clone();
    for v in &mut views[1..] {
        let view_fn_ty = ty_check_view(ctx, v)?;
        ret_dty = ty_check_app_view_fn_ty(ctx, &ret_dty, view_fn_ty)?;
    }
    let res_fn_ty = FnTy::new(
        vec![],
        vec![fst_view_fn_ty.param_tys.last().unwrap().clone()],
        ExecTy::new(ExecTyKind::View),
        Ty::new(TyKind::Data(Box::new(ret_dty))),
    );
    Ok(res_fn_ty)
}

fn ty_check_app_view_fn_ty(
    ctx: &PlExprTyCtx,
    in_dty: &DataTy,
    mut view_fn_ty: FnTy,
) -> TyResult<DataTy> {
    let mut arg_dty_fn_ty = FnTy::new(
        vec![],
        vec![Ty::new(TyKind::Data(Box::new(in_dty.clone())))],
        ExecTy::new(ExecTyKind::View),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ident(
            Ident::new_impli("ret_dty"),
        ))))),
    );
    unify::unify(&mut view_fn_ty, &mut arg_dty_fn_ty)?;
    let res_dty = arg_dty_fn_ty.ret_ty.dty().clone();
    Ok(res_dty)
}

fn ty_check_view(ctx: &PlExprTyCtx, view: &mut View) -> TyResult<FnTy> {
    let arg_tys = view
        .args
        .iter_mut()
        .map(|v| -> TyResult<Ty> {
            Ok(Ty::new(TyKind::FnTy(Box::new(ty_check_composed_views(
                ctx, v,
            )?))))
        })
        .collect::<TyResult<Vec<_>>>()?;
    let fn_ty = ctx.gl_ctx.fn_ty_by_ident(&view.name)?.clone();
    if fn_ty.generics.len() < view.gen_args.len() {
        return Err(TyError::String(format!(
            "Wrong amount of generic arguments. Expected {}, found {}",
            fn_ty.generics.len(),
            view.gen_args.len()
        )));
    }
    for (gp, kv) in fn_ty.generics.iter().zip(&*view.gen_args) {
        super::check_arg_has_correct_kind(&ctx.kind_ctx, &gp.kind, kv)?;
    }
    let mut subst_param_tys = fn_ty.param_tys.clone();
    for ty in &mut subst_param_tys {
        utils::subst_idents_kinded(fn_ty.generics.iter(), view.gen_args.iter(), ty);
    }
    let mut subst_out_ty = fn_ty.ret_ty.as_ref().clone();
    utils::subst_idents_kinded(
        fn_ty.generics.iter(),
        view.gen_args.iter(),
        &mut subst_out_ty,
    );
    let mut mono_fn_ty = unify::inst_fn_ty_scheme(
        &fn_ty.generics[view.gen_args.len()..],
        &subst_param_tys,
        &fn_ty.exec_ty,
        &subst_out_ty,
    )?;
    let mut actual_view_fn_ty = view_ty_with_input_view_and_free_ret(arg_tys);
    unify::unify(&mut actual_view_fn_ty, &mut mono_fn_ty)?;
    let mut inferred_k_args = super::infer_kinded_args::infer_kinded_args_from_mono_ty(
        fn_ty.generics[view.gen_args.len()..].to_vec(),
        subst_param_tys,
        &subst_out_ty,
        &mono_fn_ty,
    );
    // TODO reintroduce. Problem: may contain implicit identifiers that are not substituted later
    // view.gen_args.append(&mut inferred_k_args);
    let res_view_ty = FnTy::new(
        vec![],
        vec![actual_view_fn_ty.param_tys.pop().unwrap()],
        ExecTy::new(ExecTyKind::View),
        actual_view_fn_ty.ret_ty.as_ref().clone(),
    );
    Ok(res_view_ty)
}

fn view_ty_with_input_view_and_free_ret(mut arg_tys: Vec<Ty>) -> FnTy {
    arg_tys.push(Ty::new(TyKind::Data(Box::new(DataTy::new(
        DataTyKind::Ident(Ident::new_impli("in_view_dty")),
    )))));
    FnTy::new(
        vec![],
        arg_tys,
        ExecTy::new(ExecTyKind::View),
        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ident(
            Ident::new_impli("view_out_dty"),
        ))))),
    )
}

fn ty_check_ident(
    ctx: &PlExprTyCtx,
    ident: &Ident,
) -> TyResult<(Ty, Vec<Memory>, Vec<Provenance>)> {
    if let Ok(tty) = ctx.ty_ctx.ty_of_ident(ident) {
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
    } else {
        let fn_ty = ctx.gl_ctx.fn_ty_by_ident(ident)?;
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

fn ty_check_proj(
    ctx: &PlExprTyCtx,
    tuple_expr: &mut PlaceExpr,
    n: usize,
) -> TyResult<(Ty, Vec<Memory>, Vec<Provenance>)> {
    let (mem, passed_prvs) = ty_check_and_passed_mems_prvs(ctx, tuple_expr)?;
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
        dty_kind => Err(TyError::ExpectedTupleType(
            TyKind::Data(Box::new(DataTy::new(dty_kind.clone()))),
            tuple_expr.clone(),
        )),
    }
}

fn ty_check_deref(
    ctx: &PlExprTyCtx,
    borr_expr: &mut PlaceExpr,
) -> TyResult<(Ty, Vec<Memory>, Vec<Provenance>)> {
    let (mut inner_mem, mut passed_prvs) = ty_check_and_passed_mems_prvs(ctx, borr_expr)?;
    let borr_dty = if let TyKind::Data(dty) = &borr_expr.ty.as_ref().unwrap().ty {
        dty
    } else {
        return Err(TyError::String(
            "Trying to dereference non reference type.".to_string(),
        ));
    };
    match &borr_dty.dty {
        DataTyKind::Ref(reff) => {
            if &reff.own < &ctx.own {
                return Err(TyError::String(
                    "Trying to dereference and mutably use a shrd reference.".to_string(),
                ));
            }
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

// FIXME needs to be qualified over ownership
//  whether a selct is possible also depends on the ownership that we are selecting with
fn ty_check_select(
    ctx: &PlExprTyCtx,
    p: &mut PlaceExpr,
    select_exec: &mut ExecExpr,
) -> TyResult<(Ty, Vec<Memory>, Vec<Provenance>)> {
    exec::ty_check(ctx.kind_ctx, ctx.ty_ctx, ctx.ident_exec, select_exec)?;
    // FIXME this check is required for uniq accesses, but not for shared accesses because there
    //  the duplication of accesses is fine. Move this check into ownership/borrow checking?
    //    if &ctx.exec != select_exec {
    //        return Err(TyError::String(
    //            "Trying select memory for illegal combination of excution resources.".to_string(),
    //        ));
    //    }
    let mut outer_exec = select_exec.remove_last_distrib();
    exec::ty_check(ctx.kind_ctx, ctx.ty_ctx, ctx.ident_exec, &mut outer_exec)?;
    let outer_ctx = PlExprTyCtx {
        gl_ctx: ctx.gl_ctx,
        kind_ctx: ctx.kind_ctx,
        ident_exec: ctx.ident_exec,
        exec: outer_exec,
        ty_ctx: ctx.ty_ctx,
        exec_borrow_ctx: ctx.exec_borrow_ctx,
        own: ctx.own,
    };
    let (mems, prvs) = ty_check_and_passed_mems_prvs(&outer_ctx, p)?;
    let mut p_dty = p.ty.as_ref().unwrap().dty().clone();
    match p_dty.dty {
        DataTyKind::Array(elem_dty, n) | DataTyKind::ArrayShape(elem_dty, n) => {
            // TODO check sizes
            // if n != distrib_exec.active_distrib_size() {
            //     return Err(TyError::String("There must be as many elements in the view
            //  as there exist execution resources that select from it.".to_string()));
            // }
            p_dty = *elem_dty;
        }
        _ => {
            return Err(TyError::String("Expected an array or view.".to_string()));
        }
    }
    Ok((Ty::new(TyKind::Data(Box::new(p_dty))), mems, prvs))
}

fn ty_check_split_at(
    ctx: &PlExprTyCtx,
    p: &mut PlaceExpr,
    split_pos: &Nat,
) -> TyResult<(Ty, Vec<Memory>, Vec<Provenance>)> {
    let (mems, passed_prvs) = ty_check_and_passed_mems_prvs(ctx, p)?;
    if let DataTyKind::ArrayShape(elem_dty, n) = &p.ty.as_ref().unwrap().dty().dty {
        if split_pos > n {
            return Err(TyError::String(
                "Trying to access array out-of-bounds.".to_string(),
            ));
        }

        let lhs_size = split_pos.clone();
        let rhs_size = Nat::BinOp(
            BinOpNat::Sub,
            Box::new(n.clone()),
            Box::new(split_pos.clone()),
        );
        Ok((
            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Tuple(
                vec![
                    DataTy::new(DataTyKind::ArrayShape(elem_dty.clone(), lhs_size)),
                    DataTy::new(DataTyKind::ArrayShape(elem_dty.clone(), rhs_size)),
                ],
            ))))),
            mems,
            passed_prvs,
        ))
    } else {
        Err(TyError::UnexpectedType)
    }
}

fn ty_check_index_copy(
    ctx: &PlExprTyCtx,
    pl_expr: &mut PlaceExpr,
    idx: &mut Nat,
) -> TyResult<(Ty, Vec<Memory>, Vec<Provenance>)> {
    let (mems, passed_prvs) = ty_check_and_passed_mems_prvs(ctx, pl_expr)?;
    let pl_expr_dty = if let TyKind::Data(dty) = &pl_expr.ty.as_ref().unwrap().ty {
        dty
    } else {
        return Err(TyError::String(
            "Trying to index into non array type.".to_string(),
        ));
    };
    let (elem_dty, n) = match pl_expr_dty.dty.clone() {
        DataTyKind::Array(elem_dty, n) | DataTyKind::ArrayShape(elem_dty, n) => (*elem_dty, n),
        DataTyKind::At(arr_dty, _) => {
            if let DataTyKind::Array(elem_ty, n) = &arr_dty.dty {
                (elem_ty.as_ref().clone(), n.clone())
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

    if &n < idx {
        return Err(TyError::String(
            "Trying to access array out-of-bounds.".to_string(),
        ));
    }

    if elem_dty.copyable() {
        Ok((Ty::new(TyKind::Data(Box::new(elem_dty))), mems, passed_prvs))
    } else {
        Err(TyError::String(format!(
            "Cannot move out of array type: {:?}",
            elem_dty
        )))
    }
}
