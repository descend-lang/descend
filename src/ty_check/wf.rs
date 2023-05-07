use crate::ast::internal::Loan;
use crate::ast::{
    BaseTy, DataTyKind, ExecTy, Ident, Kind, Memory, Predicate, Provenance, Ty, TyKind,
};
use crate::ty_check::ctxs::{CtxResult, KindCtx, TyCtx};
use crate::ty_check::error::CtxError;
use crate::ty_check::error::TyError;
use crate::ty_check::TyResult;

pub(super) fn wf_pred(ty_ctx: &TyCtx, pred: &Predicate) -> TyResult<()> {
    let base_ty_ctx = BaseTyCtx::from(ty_ctx);
    let bty = base_ty_check(&base_ty_ctx, pred)?;
    if !matches!(bty, BaseTy::Bool) {
        return Err(TyError::UnexpectedType);
    }
    Ok(())
}

struct IdentBaseTy {
    ident: Ident,
    base_ty: BaseTy,
}

impl IdentBaseTy {
    fn new(ident: Ident, base_ty: BaseTy) -> Self {
        IdentBaseTy { ident, base_ty }
    }
}

struct BaseTyCtx {
    ctx: Vec<IdentBaseTy>,
}

impl BaseTyCtx {
    fn base_ty(&self, ident: &Ident) -> CtxResult<BaseTy> {
        if let Some(e) = self.ctx.iter().find(|e| &e.ident == ident) {
            Ok(e.base_ty)
        } else {
            Err(CtxError::IdentNotFound(ident.clone()))
        }
    }

    fn push_binding(&mut self, ident_base_ty: IdentBaseTy) {
        self.ctx.push(ident_base_ty)
    }
}

impl From<&TyCtx> for BaseTyCtx {
    fn from(ctx: &TyCtx) -> Self {
        let ctx = ctx
            .idents_typed()
            .filter_map(|idty| {
                if let DataTyKind::Refine(base_ty, _) = &idty.dty.dty {
                    Some(IdentBaseTy {
                        ident: idty.ident.clone(),
                        base_ty: *base_ty,
                    })
                } else {
                    None
                }
            })
            .collect();
        BaseTyCtx { ctx }
    }
}

fn base_ty_check(ty_ctx: &BaseTyCtx, pred: &Predicate) -> TyResult<BaseTy> {
    Ok(match pred {
        Predicate::Ident(ident) => ty_ctx.base_ty(ident)?,
        Predicate::Not(pred) => {
            let bty = base_ty_check(ty_ctx, pred)?;
            if !matches!(bty, BaseTy::Bool) {
                return Err(TyError::UnexpectedType);
            }
            BaseTy::Bool
        }
        Predicate::And(predl, predr) | Predicate::Or(predl, predr) => {
            let btyl = base_ty_check(ty_ctx, predl)?;
            let btyr = base_ty_check(ty_ctx, predr)?;
            if !(matches!(btyl, BaseTy::Bool) && matches!(btyr, BaseTy::Bool)) {
                return Err(TyError::UnexpectedType);
            }
            BaseTy::Bool
        }
        Predicate::Add(predl, predr) => {
            let btyl = base_ty_check(ty_ctx, predl)?;
            let btyr = base_ty_check(ty_ctx, predr)?;
            if !(matches!(btyl, BaseTy::Usize) && matches!(btyr, BaseTy::Usize)) {
                return Err(TyError::UnexpectedType);
            }
            BaseTy::Usize
        }
        Predicate::ConstMul(_, pred) => {
            let bty = base_ty_check(ty_ctx, pred)?;
            if !matches!(bty, BaseTy::Usize) {
                return Err(TyError::UnexpectedType);
            }
            BaseTy::Usize
        }
        Predicate::Num(_) => BaseTy::Usize,
        Predicate::True | Predicate::False => BaseTy::Bool,
        Predicate::IfElse(cond, tt, ff) => {
            let btyc = base_ty_check(ty_ctx, cond)?;
            let btytt = base_ty_check(ty_ctx, tt)?;
            let btyff = base_ty_check(ty_ctx, ff)?;
            if !(matches!(btyc, BaseTy::Bool)
                && matches!(btytt, BaseTy::Bool)
                && matches!(btyff, BaseTy::Bool))
            {
                return Err(TyError::UnexpectedType);
            }
            BaseTy::Bool
        }
        Predicate::Uninterp(ident, preds) => {
            todo!()
        }
    })
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
            DataTyKind::Refine(base_ty, refine) => {
                BaseTyCtx::from(ty_ctx)
                    .push_binding(IdentBaseTy::new(refine.ident.clone(), *base_ty));
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
