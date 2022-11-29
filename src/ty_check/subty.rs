use super::{
    ctxs::{KindCtx, TyCtx},
    unify::ConstrainMap,
};
use crate::ast::internal::Loan;
use crate::ty_check::unify::unify_without_expand;

//
// Subtyping and Provenance Subtyping from Oxide
//

use super::error::{CtxError, SubTyError};
use crate::ast::*;
use std::collections::HashSet;

type SubTyResult<T> = Result<T, SubTyError>;

// FIXME respect memory always, somehow provenances can be different is this correct?
// τ1 is subtype of τ2 under Δ and Γ, producing Γ′
// Δ; Γ ⊢ τ1 ≲ τ2 ⇒ Γ′
pub(super) fn check(
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    sub_dty: &DataTy,
    super_dty: &DataTy,
) -> SubTyResult<(TyCtx, ConstrainMap)> {
    use super::Ownership::*;
    use DataTyKind::*;

    let mut res_subs = ConstrainMap::new();
    match (&sub_dty.dty, &super_dty.dty) {
        // Δ; Γ ⊢ τ ≲ τ ⇒ Γ
        (sub, sup) if sub == sup => Ok((ty_ctx, res_subs)),
        // Δ; Γ ⊢ [τ 1 ; n] ≲ [τ2 ; n] ⇒ Γ′
        (Array(sub_elem_ty, sub_size), Array(sup_elem_ty, sup_size)) if sub_size == sup_size => {
            check(kind_ctx, ty_ctx, sub_elem_ty, sup_elem_ty)
        }
        // Δ; Γ ⊢ &B ρ1 shrd τ1 ≲ &B ρ2 shrd τ2 ⇒ Γ′′
        (Ref(sub_prv, Shrd, sub_mem, sub_ty), Ref(sup_prv, Shrd, sup_mem, sup_ty)) => {
            let res_outl_ty_ctx = outlives(kind_ctx, ty_ctx, sub_prv, sup_prv)?;
            check(kind_ctx, res_outl_ty_ctx, sub_ty, sup_ty)
        }
        // Δ; Γ ⊢ &B ρ1 uniq τ1 ≲ &B ρ2 uniq τ2 ⇒ Γ''
        (Ref(sub_prv, Uniq, sub_mem, sub_ty), Ref(sup_prv, Uniq, sup_mem, sup_ty)) => {
            let res_outl_ty_ctx = outlives(kind_ctx, ty_ctx, sub_prv, sup_prv)?;
            let (res_forw, subs_forw) = check(kind_ctx, res_outl_ty_ctx.clone(), sub_ty, sup_ty)?;
            let (res_back, subs_back) = check(kind_ctx, res_outl_ty_ctx, sup_ty, sub_ty)?;
            if let Ok(subs) = unify_without_expand(sub_mem, sup_mem) {
                res_subs = subs;
            } else {
                return Err(SubTyError::MemoryKindsNoMatch);
            }
            // TODO find out why this is important (technically),
            //  and return a proper error if suitable
            assert_eq!(res_forw, res_back);
            res_subs.composition(subs_forw);
            res_subs.composition(subs_back);
            Ok((res_back, res_subs))
        }
        // Δ; Γ ⊢ (τ1, ..., τn) ≲ (τ1′, ..., τn′) ⇒ Γn
        (Tuple(sub_elems), Tuple(sup_elems)) => {
            let mut res_ctx = ty_ctx;
            let mut subs;
            for (sub, sup) in sub_elems.iter().zip(sup_elems) {
                (res_ctx, subs) = check(kind_ctx, res_ctx, sub, sup)?;
                res_subs.composition(subs);
            }
            Ok((res_ctx, res_subs))
        }
        (Struct(sub), Struct(sup))
            if sub.name == sup.name && sub.generic_args == sup.generic_args =>
        {
            assert!(sup.struct_fields.len() == sup.struct_fields.len());
            let mut res_ctx = ty_ctx;
            let mut subs;
            for (sub, sup) in sub.struct_fields.iter().zip(sup.struct_fields.iter()) {
                assert!(sub.name == sup.name);
                (res_ctx, subs) = check(kind_ctx, res_ctx, &sub.dty, &sup.dty)?;
                res_subs.composition(subs);
            }
            Ok((res_ctx, res_subs))
        }
        // Δ; Γ ⊢ \delta1 ≲ †\delta2 ⇒ Γ
        (_, Dead(sup)) => check(kind_ctx, ty_ctx, sub_dty, sup),
        (Ident(sub_ident), Ident(_)) => {
            // FIXME if sup is also an implicit ident: use a subtyping-constraint instead?
            res_subs
                .dty_unifier
                .insert(sub_ident.name.clone(), super_dty.clone());
            Ok((ty_ctx, res_subs))
        }
        (Ident(ident), _) if ident.is_implicit => {
            let sub_dty = sub_ty_infer(super_dty);
            let (res_ctx, subs) = check(kind_ctx, ty_ctx, &sub_dty, super_dty)?;
            res_subs.dty_unifier.insert(ident.name.clone(), sub_dty);
            res_subs.composition(subs);

            Ok((res_ctx, res_subs))
        }
        (_, Ident(ident)) if ident.is_implicit => {
            let sup_dty = sub_ty_infer(sub_dty);
            let (res_ctx, subs) = check(kind_ctx, ty_ctx, sub_dty, &sup_dty)?;
            res_subs.dty_unifier.insert(ident.name.clone(), sup_dty);
            res_subs.composition(subs);

            Ok((res_ctx, res_subs))
        }
        //TODO add case for Transitiviy?
        // Δ; Γ ⊢ τ1 ≲ τ3 ⇒ Γ''
        (sub, sup) => panic!(
            "No case implemented for, \n sub: {:?}\n sup: {:?}\n",
            sub, sup
        ),
    }
}

/// Infer a sub-type or super-type if the other one an implicit identifier
fn sub_ty_infer(dty: &DataTy) -> DataTy {
    use super::Ownership::*;
    use DataTyKind::*;

    DataTy::new(match &dty.dty {
        Array(_, sub_size) => DataTyKind::Array(
            Box::new(DataTy::new(utils::fresh_ident("d", DataTyKind::Ident))),
            sub_size.clone(),
        ),
        Ref(_, Shrd, _, _) => DataTyKind::Ref(
            utils::fresh_ident("p", Provenance::Ident),
            Shrd,
            utils::fresh_ident("d", Memory::Ident),
            Box::new(DataTy::new(utils::fresh_ident("d", DataTyKind::Ident))),
        ),
        Ref(_, Uniq, _, _) => DataTyKind::Ref(
            utils::fresh_ident("p", Provenance::Ident),
            Uniq,
            utils::fresh_ident("d", Memory::Ident),
            Box::new(DataTy::new(utils::fresh_ident("d", DataTyKind::Ident))),
        ),
        Tuple(sub_elems) => DataTyKind::Tuple(
            sub_elems
                .iter()
                .map(|_| DataTy::new(utils::fresh_ident("d", DataTyKind::Ident)))
                .collect(),
        ),
        Struct(sub) => DataTyKind::Struct(StructDataType {
            name: sub.name.clone(),
            struct_fields: sub
                .struct_fields
                .iter()
                .map(|field| StructField {
                    name: field.name.clone(),
                    dty: DataTy::new(utils::fresh_ident("d", DataTyKind::Ident)),
                })
                .collect(),
            generic_args: sub.generic_args.clone(),
        }),
        _ => dty.dty.clone(),
    })
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
                .map_err(|err| SubTyError::CtxError(err))?;
            Ok(ty_ctx)
        }
        // OL-LocalProvenances
        (Value(longer), Value(shorter)) => outl_check_val_prvs(ty_ctx, longer, shorter),
        // OL-LocalProvAbsProv
        (Value(longer_val), Ident(shorter_ident)) => {
            outl_check_val_ident_prv(kind_ctx, ty_ctx, longer_val, shorter_ident)
        }
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

fn create_loan_set_err_msg(prv: &str, error_msg: &str) -> String {
    format!(
        "Error when trying to get loan set for {}: {}\n",
        prv, error_msg
    )
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
        .filter(|(_, ty)| match ty {
            Ty {
                ty:
                    TyKind::Data(DataTy {
                        dty: DataTyKind::Ref(Provenance::Value(prv_name), _, _, _),
                        ..
                    }),
                ..
            } if prv_name == prv => true,
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

fn outl_check_val_ident_prv(
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    longer_val: &str,
    shorter_ident: &Ident,
) -> SubTyResult<TyCtx> {
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
    ty_ctx.all_places().iter().any(|(pl, ty)| {
        loan_set.iter().any(|loan| {
            let Loan {
                place_expr,
                own: own_qual,
            } = loan;
            place_expr.equiv(pl)
        })
    })
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
