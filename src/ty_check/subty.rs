use super::ctxs::{KindCtx, TyCtx};
use crate::arena_ast::internal::Loan;

//
// Subtyping and Provenance Subtyping from Oxide
//

use super::error::{CtxError, SubTyError};
use crate::arena_ast::*;
use bumpalo::Bump;

type SubTyResult<'a, T> = Result<T, SubTyError<'a>>;

// FIXME respect memory always, somehow provenances can be different is this correct?
// τ1 is subtype of τ2 under Δ and Γ, producing Γ′
// Δ; Γ ⊢ τ1 ≲ τ2 ⇒ Γ′
pub(super) fn check<'a>(
    kind_ctx: &'a KindCtx<'a>,
    ty_ctx: &mut TyCtx<'a>,
    sub_dty: &'a DataTy<'a>,
    super_dty: &'a DataTy<'a>,
    arena: &'a Bump,
) -> SubTyResult<'a, ()> {
    use super::Ownership::*;
    use DataTyKind::*;

    match (&sub_dty.dty, &super_dty.dty) {
        // Δ; Γ ⊢ τ ≲ τ ⇒ Γ
        (sub, sup) if sub == sup => Ok(()),
        // Δ; Γ ⊢ [τ 1 ; n] ≲ [τ2 ; n] ⇒ Γ′
        (Array(sub_elem_ty, _sub_size), Array(sup_elem_ty, _sup_size))
        | (ArrayShape(sub_elem_ty, _sub_size), ArrayShape(sup_elem_ty, _sup_size)) => {
            check(kind_ctx, ty_ctx, sub_elem_ty, sup_elem_ty, arena)
        }
        // Δ; Γ ⊢ &B ρ1 shrd τ1 ≲ &B ρ2 shrd τ2 ⇒ Γ′′
        (Ref(lref), Ref(rref)) if lref.own == Shrd && rref.own == Shrd => {
            outlives(kind_ctx, ty_ctx, &lref.rgn, &rref.rgn, arena)?;
            if lref.mem != rref.mem {
                return Err(SubTyError::MemoryKindsNoMatch);
            }
            check(kind_ctx, ty_ctx, lref.dty, rref.dty, arena)
        }
        // Δ; Γ ⊢ &B ρ1 uniq τ1 ≲ &B ρ2 uniq τ2 ⇒ Γ''
        (Ref(lref), Ref(rref)) => {
            if lref.own != rref.own {
                return Err(SubTyError::OwnershipNoMatch);
            }
            if lref.mem != rref.mem {
                return Err(SubTyError::MemoryKindsNoMatch);
            }
            outlives(kind_ctx, ty_ctx, &lref.rgn, &rref.rgn, arena)?;
            check(kind_ctx, ty_ctx, lref.dty, rref.dty, arena)
        }
        // Δ; Γ ⊢ (τ1, ..., τn) ≲ (τ1′, ..., τn′) ⇒ Γn
        (Tuple(sub_elems), Tuple(sup_elems)) => {
            for (sub, sup) in sub_elems.iter().zip(sup_elems) {
                check(kind_ctx, ty_ctx, sub, sup, arena)?;
            }
            Ok(())
        }
        // Δ; Γ ⊢ \delta1 ≲ †\delta2 ⇒ Γ
        (_, Dead(sup)) => check(kind_ctx, ty_ctx, sub_dty, sup, arena),
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
pub(super) fn outlives<'a>(
    kind_ctx: &'a KindCtx<'a>,
    ty_ctx: &mut TyCtx<'a>,
    longer_prv: &'a Provenance<'a>,
    shorter_prv: &'a Provenance<'a>,
    arena: &'a Bump,
) -> SubTyResult<'a, ()> {
    use Provenance::*;

    match (longer_prv, shorter_prv) {
        // Δ; Γ ⊢ ρ :> ρ ⇒ Γ
        // OL-Refl
        (longer, shorter) if longer == shorter => Ok(()),
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
            Ok(())
        }
        // OL-LocalProvenances
        (Value(longer), Value(shorter)) => outl_check_val_prvs(ty_ctx, longer, shorter, arena),
        // OL-LocalProvAbsProv
        (Value(longer_val), Ident(_)) => outl_check_val_ident_prv(ty_ctx, longer_val, arena),
        // OL-AbsProvLocalProv
        (Ident(longer_ident), Value(shorter_val)) => {
            outl_check_ident_val_prv(kind_ctx, ty_ctx, longer_ident, shorter_val)
        }
    }
}

// OL-LocalProvenances
// Δ; Γ ⊢ r1 :> r2 ⇒ Γ[r2 ↦→ { Γ(r1) ∪ Γ(r2) }]
fn outl_check_val_prvs<'tcx, 'a>(
    ty_ctx: &'tcx mut TyCtx<'a>,
    longer: &str,
    shorter: &str,
    arena: &'a Bump,
) -> SubTyResult<'a, ()> {
    // CHECK:
    //    NOT CLEAR WHY a. IS NECESSARY
    // a. for every variable of reference type with r1 in ty_ctx: there must not exist a loan
    //  dereferencing the variable for any provenance in ty_ctx.

    if exists_deref_loan_with_prv(ty_ctx, longer, arena) {
        // TODO better error msg
        return Err(SubTyError::Dummy);
    }

    // b. r1 occurs before r2 in Gamma (left to right)
    if !longer_occurs_before_shorter(ty_ctx, longer, shorter) {
        return Err(SubTyError::NotOutliving(
            longer.to_string(),
            shorter.to_string(),
        ));
    }

    // Create output Ctx
    let longer_loans = ty_ctx.loans_in_prv(longer)?.clone();
    ty_ctx.extend_loans_for_prv(shorter, longer_loans)?;
    Ok(())
}

fn longer_occurs_before_shorter<'tcx, 'a>(
    ty_ctx: &'tcx TyCtx<'a>,
    longer: &str,
    shorter: &str,
) -> bool {
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

fn exists_deref_loan_with_prv<'a>(ty_ctx: &TyCtx<'a>, prv: &str, arena: &'a bumpalo::Bump) -> bool {
    ty_ctx
        .all_places(arena)
        .into_iter()
        .filter(|(_, dty)| match &dty.dty {
            DataTyKind::Ref(reff) => match &reff.rgn {
                Provenance::Value(prv_name) => *prv_name == prv,
                _ => false,
            },
            _ => false,
        })
        .any(|(place_owned, _)| {
            let place_ref = arena.alloc(place_owned);
            ty_ctx.prv_mappings().into_iter().any(|pm| {
                pm.loans.iter().any(|loan| match &loan.place_expr.pl_expr {
                    PlaceExprKind::Deref(pl_expr) => pl_expr.equiv(arena, place_ref),
                    _ => false,
                })
            })
        })
}

fn outl_check_val_ident_prv<'a>(
    ty_ctx: &TyCtx<'a>,
    longer_val: &str,
    arena: &'a Bump,
) -> SubTyResult<'a, ()> {
    // TODO how could the set ever be empty?
    let loan_snapshot = arena.alloc(ty_ctx.loans_in_prv_snapshot(longer_val, arena)?);
    if loan_snapshot.is_empty() {
        return Err(SubTyError::PrvNotUsedInBorrow(longer_val.to_string()));
    }

    borrowed_pl_expr_no_ref_to_existing_pl(ty_ctx, loan_snapshot.as_slice(), arena);
    panic!("Not yet implemented.")
}

// FIXME Makes no sense!
fn borrowed_pl_expr_no_ref_to_existing_pl<'a>(
    ty_ctx: &TyCtx<'a>,
    loans: &'a [Loan<'a>],
    arena: &'a bumpalo::Bump,
) -> bool {
    let places = ty_ctx.all_places(arena);

    places.into_iter().any(|(pl_owned, _)| {
        let pl_ref: &'a internal::Place<'a> = arena.alloc(pl_owned);
        loans
            .iter()
            .any(|loan| loan.place_expr.equiv(arena, pl_ref))
    })
}

fn outl_check_ident_val_prv<'tcx, 'a>(
    kind_ctx: &'a KindCtx<'a>,
    ty_ctx: &'tcx TyCtx<'a>,
    longer_ident: &'a Ident<'a>,
    shorter_val: &str,
) -> SubTyResult<'a, ()> {
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
    Ok(())
}

// Δ; Γ ⊢ List[ρ1 :> ρ2] ⇒ Γ′
pub(super) fn multiple_outlives<'a, I>(
    kind_ctx: &'a KindCtx<'a>,
    ty_ctx: &'a mut TyCtx<'a>,
    prv_rels: I,
    arena: &'a Bump,
) -> SubTyResult<'a, ()>
where
    I: IntoIterator<Item = (&'a Provenance<'a>, &'a Provenance<'a>)>,
{
    for (p1, p2) in prv_rels {
        outlives(kind_ctx, ty_ctx, p1, p2, arena)?;
    }
    Ok(())
}
