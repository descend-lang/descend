use super::ty_ctx::TyCtx;

//
// Subtyping and Provenance Subtyping from Oxide
//

use super::ErrMsg;
use crate::ast::*;
use std::collections::HashSet;

// τ1 is subtype of τ2 under Δ and Γ, producing Γ′
// Δ; Γ ⊢ τ1 ≲ τ2 ⇒ Γ′
pub fn subty_check(
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    sub_ty: &Ty,
    super_ty: &Ty,
) -> Result<TyCtx, String> {
    use super::Ownership::*;
    use Ty::*;

    match (sub_ty, super_ty) {
        // Δ; Γ ⊢ τ ≲ τ ⇒ Γ
        (sub, sup) if sub == sup => Ok(ty_ctx),
        // Δ; Γ ⊢ [τ 1 ; n] ≲ [τ2 ; n] ⇒ Γ′
        (Array(sub_elem_ty, sub_size), Array(sup_elem_ty, sup_size)) if sub_size == sup_size => {
            subty_check(kind_ctx, ty_ctx, &sub_elem_ty, &sup_elem_ty)
        }
        // Δ; Γ ⊢ &B ρ1 shrd τ1 ≲ &B ρ2 shrd τ2 ⇒ Γ′′
        (Ref(sub_prv, Shrd, sub_mem, sub_ty), Ref(sup_prv, Shrd, sup_mem, sup_ty)) => {
            let res_outl_ty_ctx = outlives(kind_ctx, ty_ctx, sub_prv, sup_prv)?;
            subty_check(kind_ctx, res_outl_ty_ctx, &sub_ty, &sup_ty)
        }
        // Δ; Γ ⊢ &B ρ1 uniq τ1 ≲ &B ρ2 uniq τ2 ⇒ Γ''
        (Ref(sub_prv, Uniq, sub_mem, sub_ty), Ref(sup_prv, Uniq, sup_mem, sup_ty)) => {
            let res_outl_ty_ctx = outlives(kind_ctx, ty_ctx, sub_prv, sup_prv)?;
            let res_forw = subty_check(kind_ctx, res_outl_ty_ctx.clone(), &sub_ty, &sup_ty)?;
            let res_back = subty_check(kind_ctx, res_outl_ty_ctx, &sup_ty, &sub_ty)?;
            // TODO find out why this is important (techniqually),
            //  and return a proper error if suitable
            assert_eq!(res_forw, res_back);
            Ok(res_back)
        }
        // Δ; Γ ⊢ (τ1, ..., τn) ≲ (τ1′, ..., τn′) ⇒ Γn
        (Ty::Tuple(sub_elems), Ty::Tuple(sup_elems)) => {
            let mut res_ctx = ty_ctx;
            for (sub, sup) in sub_elems.iter().zip(sup_elems) {
                res_ctx = subty_check(kind_ctx, res_ctx, sub, sup)?;
            }
            Ok(res_ctx)
        }
        // Δ; Γ ⊢ \delta1 ≲ †\delta2 ⇒ Γ
        (sub, Dead(sup)) => subty_check(kind_ctx, ty_ctx, sub, sup),
        //TODO add case for Transitiviy?
        // Δ; Γ ⊢ τ1 ≲ τ3 ⇒ Γ''
        (sub, sup) => panic!(format!(
            "No case implemented for, \n sub: {:?}\n sup: {:?}\n",
            sub, sup
        )),
    }
}

// ρ1 outlives ρ2 under Δ and Γ, producing Γ′
// Δ; Γ ⊢ ρ1 :> ρ2 ⇒ Γ′
fn outlives(
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    longer_prv: &Provenance,
    shorter_prv: &Provenance,
) -> Result<TyCtx, ErrMsg> {
    use Provenance::*;

    match (longer_prv, shorter_prv) {
        // Δ; Γ ⊢ ρ :> ρ ⇒ Γ
        // OL-Refl
        (longer, shorter) if longer == shorter => Ok(ty_ctx.clone()),
        // TODO transitivity missing
        // OL-Trans

        // OL-AbstractProvenances
        // Δ; Γ ⊢ \varρ1 :> \varρ2 ⇒ Γ
        (Ident(longer), Ident(shorter)) => {
            // TODO think about this: Oxide also checks that l and s are declared idents in the
            //  kinding context. However, that should always be the case for a well-formed kinding
            //  context. See ty_check_global_fun_def.
            kind_ctx.outlives(longer, shorter)?;
            Ok(ty_ctx.clone())
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
fn outl_check_val_prvs(ty_ctx: TyCtx, longer: &str, shorter: &str) -> Result<TyCtx, String> {
    // CHECK:
    //    NOT CLEAR WHY a. IS NECESSARY
    // a. for every variable of reference type with r1 in ty_ctx: there must not exist a loan
    //  dereferencing the variable for any provenance in ty_ctx.

    if exists_deref_loan_with_prv(&ty_ctx, longer) {
        // TODO better error msg
        return Err(String::from("first condition violated"));
    }

    // b. r1 occurs before r2 in Gamma (left to right)
    if !longer_occurs_before_shorter(&ty_ctx, longer, shorter) {
        return Err(format!("{} lives longer than {}.", shorter, longer));
    }

    // Create output Ctx
    let longer_loans = ty_ctx.loans_for_prv(longer)?.clone();
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
            Ty::Ref(Provenance::Value(prv_name), _, _, _) if prv_name == prv => true,
            _ => false,
        })
        .any(|(place, _)| {
            ty_ctx.prv_mappings().into_iter().any(|prv_mapping| {
                for loan in prv_mapping.loans.iter() {
                    if let Loan {
                        place_expr: PlaceExpr::Deref(pl_expr),
                        ..
                    } = loan
                    {
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
) -> Result<TyCtx, String> {
    // TODO how could the set ever be empty?
    let loan_set = ty_ctx.loans_for_prv(longer_val)?;
    if loan_set.is_empty() {
        return Err(format!("No loans bound to provenance."));
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
) -> Result<TyCtx, String> {
    if kind_ctx.ident_of_kind_exists(longer_ident, Kind::Provenance)
        && ty_ctx.prv_val_exists(shorter_val)
    {
        Ok(ty_ctx)
    } else {
        Err(format!(
            "{} or {} not found in contexts.",
            longer_ident, shorter_val
        ))
    }
}

// Δ; Γ ⊢ List[ρ1 :> ρ2] ⇒ Γ′
pub fn multiple_outlives<'a, I>(
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    prv_rels: I,
) -> Result<TyCtx, String>
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
