use super::borrow_check::BorrowCheckCtx;
use super::error::TyError;
use super::TyResult;
use crate::ast::{
    BinOpNat, DataTy, DataTyKind, ExecExpr, ExecTyKind, Ident, IdentExec, Memory, Nat, Ownership,
    PlaceExpr, PlaceExprKind, Provenance, Ty, TyKind,
};
use crate::ty_check::ctxs::{AccessCtx, GlobalCtx, KindCtx, TyCtx};

use crate::ty_check::{exec, ExprTyCtx};

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
    };
    pl_expr.ty = Some(Box::new(ty));
    Ok((mem, prvs))
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

fn ty_check_select(
    ctx: &PlExprTyCtx,
    p: &mut PlaceExpr,
    select_exec: &mut ExecExpr,
) -> TyResult<(Ty, Vec<Memory>, Vec<Provenance>)> {
    exec::ty_check(ctx.kind_ctx, ctx.ty_ctx, ctx.ident_exec, select_exec)?;
    if &ctx.exec != select_exec {
        return Err(TyError::String(
            "Trying select memory for illegal combination of excution resources.".to_string(),
        ));
    }
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
