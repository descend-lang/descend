use super::ctxs::{KindCtx, TyCtx};
use crate::ast::internal::Loan;

//
// Subtyping and Provenance Subtyping from Oxide
//

use super::error::{CtxError, SubTyError};
use crate::ast::*;
use std::collections::HashSet;

type SubTyResult<T> = Result<T, SubTyError>;

// FIXME respect memory alaways, somehow provenances can be different is this correct?
// τ1 is subtype of τ2 under Δ and Γ, producing Γ′
// Δ; Γ ⊢ τ1 ≲ τ2 ⇒ Γ′
pub(super) fn check(
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    sub_dty: &DataTy,
    super_dty: &DataTy,
) -> SubTyResult<TyCtx> {
    use super::Ownership::*;
    use DataTyKind::*;

    match (&sub_dty.dty, &super_dty.dty) {
        // Δ; Γ ⊢ τ ≲ τ ⇒ Γ
        (sub, sup) if sub == sup => Ok(ty_ctx),
        // Δ; Γ ⊢ [τ 1 ; n] ≲ [τ2 ; n] ⇒ Γ′
        (Array(sub_elem_ty, sub_size), Array(sup_elem_ty, sup_size))
        | (ArrayShape(sub_elem_ty, sub_size), ArrayShape(sup_elem_ty, sup_size)) => {
            check(kind_ctx, ty_ctx, sub_elem_ty, sup_elem_ty)
        }
        // Δ; Γ ⊢ &B ρ1 shrd τ1 ≲ &B ρ2 shrd τ2 ⇒ Γ′′
        (Ref(lref), Ref(rref)) if lref.own == Shrd && rref.own == Shrd => {
            let res_outl_ty_ctx = outlives(kind_ctx, ty_ctx, &lref.rgn, &rref.rgn)?;
            if lref.mem != rref.mem {
                return Err(SubTyError::MemoryKindsNoMatch);
            }
            check(
                kind_ctx,
                res_outl_ty_ctx,
                lref.dty.as_ref(),
                rref.dty.as_ref(),
            )
        }
        // Δ; Γ ⊢ &B ρ1 uniq τ1 ≲ &B ρ2 uniq τ2 ⇒ Γ''
        (Ref(lref), Ref(rref)) => {
            let res_outl_ty_ctx = outlives(kind_ctx, ty_ctx, &lref.rgn, &rref.rgn)?;
            let res_forw = check(
                kind_ctx,
                res_outl_ty_ctx.clone(),
                lref.dty.as_ref(),
                rref.dty.as_ref(),
            )?;
            let res_back = check(
                kind_ctx,
                res_outl_ty_ctx,
                rref.dty.as_ref(),
                lref.dty.as_ref(),
            )?;
            if lref.mem != rref.mem {
                return Err(SubTyError::MemoryKindsNoMatch);
            }
            // TODO find out why this is important (technically),
            //  and return a proper error if suitable
            assert_eq!(res_forw, res_back);
            Ok(res_back)
        }
        // Δ; Γ ⊢ (τ1, ..., τn) ≲ (τ1′, ..., τn′) ⇒ Γn
        (Tuple(sub_elems), Tuple(sup_elems)) => {
            let mut res_ctx = ty_ctx;
            for (sub, sup) in sub_elems.iter().zip(sup_elems) {
                res_ctx = check(kind_ctx, res_ctx, sub, sup)?;
            }
            Ok(res_ctx)
        }
        // Δ; Γ ⊢ \delta1 ≲ †\delta2 ⇒ Γ
        (_, Dead(sup)) => check(kind_ctx, ty_ctx, sub_dty, sup),
        //TODO add case for Transitiviy?
        // Δ; Γ ⊢ τ1 ≲ τ3 ⇒ Γ''
        (sub, sup) => panic!(
            "No case implemented for, \n sub: {:?}\n sup: {:?}\n",
            sub, sup
        ),
    }
}

// ρ1 outlives ρ2 under Δ and Γ, producing Γ′
// Δ; Γ ⊢ ρ1 :> ρ2 ⇒ Γ′
fn outlives(
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    longer_prv: &Provenance,
    shorter_prv: &Provenance,
) -> SubTyResult<TyCtx> {
    use Provenance::*;

    match (longer_prv, shorter_prv) {
        // Δ; Γ ⊢ ρ :> ρ ⇒ Γ
        // OL-Refl
        (longer, shorter) if longer == shorter => Ok(ty_ctx),
        // TODO transitivity missing
        // OL-Trans

        // OL-AbstractProvenances
        // Δ; Γ ⊢ \varρ1 :> \varρ2 ⇒ Γ
        (Ident(longer), Ident(shorter)) => {
            // TODO think about this: Oxide also checks that l and s are declared idents in the
            //  kinding context. However, that should always be the case for a well-formed kinding
            //  context. See ty_check_global_fun_def.
            kind_ctx
                .outlives(longer, shorter)
                .map_err(SubTyError::CtxError)?;
            Ok(ty_ctx)
        }
        // OL-LocalProvenances
        (Value(longer), Value(shorter)) => outl_check_val_prvs(ty_ctx, longer, shorter),
        // OL-LocalProvAbsProv
        (Value(longer_val), Ident(_)) => outl_check_val_ident_prv(ty_ctx, longer_val),
        // OL-AbsProvLocalProv
        (Ident(longer_ident), Value(shorter_val)) => {
            outl_check_ident_val_prv(kind_ctx, ty_ctx, longer_ident, shorter_val)
        }
    }
}

// OL-LocalProvenances
// Δ; Γ ⊢ r1 :> r2 ⇒ Γ[r2 ↦→ { Γ(r1) ∪ Γ(r2) }]
fn outl_check_val_prvs(ty_ctx: TyCtx, longer: &str, shorter: &str) -> SubTyResult<TyCtx> {
    // CHECK:
    //    NOT CLEAR WHY a. IS NECESSARY
    // a. for every variable of reference type with r1 in ty_ctx: there must not exist a loan
    //  dereferencing the variable for any provenance in ty_ctx.

    if exists_deref_loan_with_prv(&ty_ctx, longer) {
        // TODO better error msg
        return Err(SubTyError::Dummy);
    }

    // b. r1 occurs before r2 in Gamma (left to right)
    if !longer_occurs_before_shorter(&ty_ctx, longer, shorter) {
        return Err(SubTyError::NotOutliving(
            longer.to_string(),
            shorter.to_string(),
        ));
    }

    // Create output Ctx
    let longer_loans = ty_ctx.loans_in_prv(longer)?.clone();
    let res_ty_ctx = ty_ctx.extend_loans_for_prv(shorter, longer_loans)?;
    Ok(res_ty_ctx)
}

fn longer_occurs_before_shorter(ty_ctx: &TyCtx, longer: &str, shorter: &str) -> bool {
    for prv in ty_ctx
        .prv_mappings()
        .map(|prv_mappings| prv_mappings.prv.clone())
    {
        if prv == longer {
            return true;
        } else if prv == shorter {
            return false;
        }
    }
    panic!("Neither provenance found in typing context")
}

fn exists_deref_loan_with_prv(ty_ctx: &TyCtx, prv: &str) -> bool {
    ty_ctx
        .all_places()
        .into_iter()
        .filter(|(_, dty)| match &dty.dty {
            DataTyKind::Ref(reff) => match &reff.rgn {
                Provenance::Value(prv_name) => prv_name == prv,
                _ => false,
            },
            _ => false,
        })
        .any(|(place, _)| {
            ty_ctx.prv_mappings().into_iter().any(|prv_mapping| {
                for loan in prv_mapping.loans.iter() {
                    if let PlaceExprKind::Deref(pl_expr) = &loan.place_expr.pl_expr {
                        return pl_expr.equiv(&place);
                    }
                }
                false
            })
        })
}

fn outl_check_val_ident_prv(ty_ctx: TyCtx, longer_val: &str) -> SubTyResult<TyCtx> {
    // TODO how could the set ever be empty?
    let loan_set = ty_ctx.loans_in_prv(longer_val)?;
    if loan_set.is_empty() {
        return Err(SubTyError::PrvNotUsedInBorrow(longer_val.to_string()));
    }

    borrowed_pl_expr_no_ref_to_existing_pl(&ty_ctx, loan_set);
    panic!("Not yet implemented.")
}

// FIXME Makes no sense!
fn borrowed_pl_expr_no_ref_to_existing_pl(ty_ctx: &TyCtx, loan_set: &HashSet<Loan>) -> bool {
    ty_ctx
        .all_places()
        .iter()
        .any(|(pl, _)| loan_set.iter().any(|loan| loan.place_expr.equiv(pl)))
}

fn outl_check_ident_val_prv(
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    longer_ident: &Ident,
    shorter_val: &str,
) -> SubTyResult<TyCtx> {
    if !kind_ctx.ident_of_kind_exists(longer_ident, Kind::Provenance) {
        return Err(SubTyError::CtxError(CtxError::PrvIdentNotFound(
            longer_ident.clone(),
        )));
    }
    if !ty_ctx.prv_val_exists(shorter_val) {
        return Err(SubTyError::CtxError(CtxError::PrvValueNotFound(
            shorter_val.to_string(),
        )));
    }
    Ok(ty_ctx)
}

// Δ; Γ ⊢ List[ρ1 :> ρ2] ⇒ Γ′
pub(super) fn multiple_outlives<'a, I>(
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    prv_rels: I,
) -> SubTyResult<TyCtx>
where
    I: IntoIterator<Item = (&'a Provenance, &'a Provenance)>,
{
    prv_rels
        .into_iter()
        .try_fold(ty_ctx, |res_ty_ctx, prv_rel| {
            let (longer, shorter) = prv_rel;
            outlives(kind_ctx, res_ty_ctx, longer, shorter)
        })
}
