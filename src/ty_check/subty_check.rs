//
// Subtyping and Provenance Subtyping from Oxide
//

use super::ErrMsg;
use crate::ast::{PlaceCtx, PlaceExpr};
use crate::ty::*;

// τ1 is subtype of τ2 under Δ and Γ, producing Γ′
// Δ; Γ ⊢ τ1 ≲ τ2 ⇒ Γ′
pub fn subty_check(
    kind_ctx: &KindCtx,
    ty_ctx: &TypingCtx,
    sub_ty: &Ty,
    super_ty: &Ty,
) -> Result<TypingCtx, String> {
    use super::Ownership::*;
    use DataTy::*;
    use Ty::*;

    match (sub_ty, super_ty) {
        // Δ; Γ ⊢ τ ≲ τ ⇒ Γ
        (sub, sup) if sub == sup => Ok(ty_ctx.clone()),
        // Δ; Γ ⊢ [τ 1 ; n] ≲ [τ2 ; n] ⇒ Γ′
        (Data(Array(sub_size, sub_elem_dty)), Data(Array(sup_size, sup_elem_dty)))
            if sub_size == sup_size =>
        {
            subty_check(
                kind_ctx,
                ty_ctx,
                &Data((**sub_elem_dty).clone()),
                &Data((**sup_elem_dty).clone()),
            )
        }
        // Δ; Γ ⊢ &ρ1 shrd τ1 ≲ &ρ2 shrd τ2 ⇒ Γ′′
        (
            Data(Ref(sub_prv, Shrd, sub_mem, sub_dty)),
            Data(Ref(sup_prv, Shrd, sup_mem, sup_dty)),
        ) if sub_mem == sup_mem => {
            let res_outl_ty_ctx = outlives(kind_ctx, ty_ctx, sub_prv, sup_prv)?;
            subty_check(
                kind_ctx,
                &res_outl_ty_ctx,
                &Data((**sub_dty).clone()),
                &Data((**sup_dty).clone()),
            )
        }
        // Δ; Γ ⊢ &ρ1 uniq τ1 ≲ &ρ2 uniq τ2 ⇒ Γ''
        (
            Data(Ref(sub_prv, Uniq, sub_mem, sub_dty)),
            Data(Ref(sup_prv, Uniq, sup_mem, sup_dty)),
        ) if sub_mem == sup_mem => {
            let res_outl_ty_ctx = outlives(kind_ctx, ty_ctx, sub_prv, sup_prv)?;
            let res_forw = subty_check(
                kind_ctx,
                &res_outl_ty_ctx,
                &Data((**sub_dty).clone()),
                &Data((**sup_dty).clone()),
            )?;
            let res_back = subty_check(
                kind_ctx,
                &res_outl_ty_ctx,
                &Data((**sup_dty).clone()),
                &Data((**sub_dty).clone()),
            )?;

            // TODO find out why this is important (techniqually),
            //  and return a proper error if suitable
            assert_eq!(res_forw, res_back);
            Ok(res_back)
        }
        // Δ; Γ ⊢ (τ1, ..., τn) ≲ (τ1′, ..., τn′) ⇒ Γn
        (Ty::Tuple(sub_elems), Ty::Tuple(sup_elems)) => {
            let mut res_ctx = ty_ctx.clone();
            for (sub, sup) in sub_elems.iter().zip(sup_elems) {
                res_ctx = subty_check(kind_ctx, &res_ctx, sub, sup)?;
            }
            Ok(res_ctx.clone())
        }
        // Δ; Γ ⊢ \delta1 ≲ †\delta2 ⇒ Γ
        (sub @ Data(_), Dead(DeadTy::Data(sup))) => {
            subty_check(kind_ctx, ty_ctx, sub, &Data(sup.clone()))
        }
        //TODO add case for Transitiviy?
        // Δ; Γ ⊢ τ1 ≲ τ3 ⇒ Γ''
        _ => panic!("Good error message not implemented yet."),
    }
}

// ρ1 outlives ρ2 under Δ and Γ, producing Γ′
// Δ; Γ ⊢ ρ1 :> ρ2 ⇒ Γ′
fn outlives(
    kind_ctx: &KindCtx,
    ty_ctx: &TypingCtx,
    longer_prv: &Provenance,
    shorter_prv: &Provenance,
) -> Result<TypingCtx, ErrMsg> {
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
fn outl_check_val_prvs(
    ty_ctx: &TypingCtx,
    longer: &str,
    shorter: &str,
) -> Result<TypingCtx, String> {
    // CHECK:
    //    NOT CLEAR WHY a. IS NECESSARY
    // a. for every variable of reference type with r1 in ty_ctx: there must not exist a loan
    //  dereferencing the variable for any provenance in ty_ctx.

    if exists_deref_loan_with_prv(ty_ctx, longer) {
        // TODO better error msg
        return Err(String::from("first condition violated"));
    }

    // b. r1 occurs before r2 in Gamma (left to right)
    if !longer_occurs_before_shorter(ty_ctx, longer, shorter) {
        return Err(format!("{} lives longer than {}.", shorter, longer));
    }

    // Create output Ctx
    let unifed_loan_set = match (ty_ctx.get_loan_set(longer), ty_ctx.get_loan_set(shorter)) {
        (Ok(mut set_longer), Ok(mut set_shorter)) => {
            set_longer.append(&mut set_shorter);
            set_longer
        }
        (set_longer, set_shorter) => {
            let mut err_msg = String::new();
            if let Err(msg_longer) = set_longer {
                err_msg = create_loan_set_err_msg(longer, &msg_longer);
            }
            if let Err(msg_shorter) = set_shorter {
                err_msg = format!(
                    "{}\n{}",
                    err_msg,
                    create_loan_set_err_msg(shorter, &msg_shorter)
                )
            }
            return Err(err_msg);
        }
    };
    Ok(ty_ctx.clone().update_loan_set(shorter, unifed_loan_set)?)
}

fn create_loan_set_err_msg(prv: &str, error_msg: &str) -> String {
    format!(
        "Error when trying to get loan set for {}: {}\n",
        prv, error_msg
    )
}

fn longer_occurs_before_shorter(ty_ctx: &TypingCtx, longer: &str, shorter: &str) -> bool {
    for prv in ty_ctx
        .get_prv_mappings()
        .into_iter()
        .map(|prv_mappings| prv_mappings.prv)
    {
        if prv == longer {
            return true;
        } else if prv == shorter {
            return false;
        }
    }
    panic!("Neither provenance found in typing context")
}

fn exists_deref_loan_with_prv(ty_ctx: &TypingCtx, prv: &str) -> bool {
    ty_ctx
        .all_places()
        .into_iter()
        .filter(|(_, dty)| match dty {
            DataTy::Ref(Provenance::Value(prv_name), _, _, _) if prv_name == prv => true,
            _ => false,
        })
        .any(|(place, _)| {
            ty_ctx.get_prv_mappings().into_iter().any(|prv_mapping| {
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
    ty_ctx: &TypingCtx,
    longer_val: &str,
    shorter_ident: &TyIdent,
) -> Result<TypingCtx, String> {
    // TODO how could the set ever be empty?
    let loan_set = ty_ctx.get_loan_set(longer_val)?;
    if loan_set.is_empty() {
        return Err(format!("No loans bound to provenance."));
    }

    borrowed_pl_expr_no_ref_to_existing_pl(ty_ctx, loan_set);
    panic!("Not yet implemented.")
}

// FIXME Makes no sense!
fn borrowed_pl_expr_no_ref_to_existing_pl(ty_ctx: &TypingCtx, loan_set: Vec<Loan>) -> bool {
    ty_ctx.all_places().iter().any(|(pl, dty)| {
        loan_set.iter().any(|loan| {
            let Loan {
                place_expr,
                own_qual,
            } = loan;
            place_expr.equiv(pl)
        })
    })
}

fn outl_check_ident_val_prv(
    kind_ctx: &KindCtx,
    ty_ctx: &TypingCtx,
    longer_ident: &TyIdent,
    shorter_val: &str,
) -> Result<TypingCtx, String> {
    if kind_ctx.prv_ident_exists(longer_ident) && ty_ctx.prv_val_exists(shorter_val) {
        Ok(ty_ctx.clone())
    } else {
        Err(format!(
            "{} or {} not found in contexts.",
            longer_ident, shorter_val
        ))
    }
}

// Δ; Γ ⊢ List[ρ1 :> ρ2] ⇒ Γ′
fn multiple_outlives(
    kind_ctx: &KindCtx,
    ty_ctx: &TypingCtx,
    prv_rels: &Vec<(Provenance, Provenance)>,
) -> Result<TypingCtx, String> {
    // TODO figure out how `fold` works
    let mut res_ty_ctx = ty_ctx.clone();
    for prv_rel in prv_rels {
        let (longer, shorter) = prv_rel;
        res_ty_ctx = outlives(kind_ctx, &res_ty_ctx, longer, shorter)?;
    }
    Ok(res_ty_ctx)
}
