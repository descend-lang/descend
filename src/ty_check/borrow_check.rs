use super::ty_ctx::{PrvMapping, TyCtx};
use crate::ast::ty::*;
use crate::ast::*;
use std::collections::HashSet;

//
// Ownership Safety
//
//p is ω-safe under δ and γ, with reborrow exclusion list π , and may point to any of the loans in ωp
pub fn ownership_safe(
    kind_ctx: &KindCtx,
    ty_ctx: &TyCtx,
    reborrows: &[Place],
    own: Ownership,
    p: &PlaceExpr,
) -> Result<HashSet<Loan>, String> {
    if p.is_place() {
        ownership_safe_place(ty_ctx, reborrows, own, p)
    } else {
        let (pl_ctx, most_spec_pl) = p.to_pl_ctx_and_most_specif_pl();
        let pl_ctx_no_deref = pl_ctx.without_innermost_deref();
        match ty_ctx.place_ty(&most_spec_pl)? {
            Ty::Ref(Provenance::Value(_), _, _, _) => ownership_safe_deref(
                kind_ctx,
                ty_ctx,
                reborrows,
                own,
                &pl_ctx_no_deref,
                &most_spec_pl,
            ),
            Ty::Ref(Provenance::Ident(_), _, _, _) => unimplemented!(),
            _ => panic!("This must never happen."),
        }
    }
}

fn ownership_safe_place(
    ty_ctx: &TyCtx,
    reborrows: &[Place],
    own: Ownership,
    p: &PlaceExpr,
) -> Result<HashSet<Loan>, String> {
    if ownership_safe_under_existing_loans(ty_ctx, reborrows, own, p) {
        let mut loan_set = HashSet::new();
        loan_set.insert(Loan {
            place_expr: p.clone(),
            own,
        });
        Ok(loan_set)
    } else {
        Err("A borrow is being violated.".to_string())
    }
}

// TODO When calling make sure that the innermost deref in pl_ctx_no_deref is removed
fn ownership_safe_deref(
    kind_ctx: &KindCtx,
    ty_ctx: &TyCtx,
    reborrows: &[Place],
    own: Ownership,
    pl_ctx_no_deref: &PlaceCtx,
    most_spec_pl: &Place,
) -> Result<HashSet<Loan>, String> {
    // Γ(π) = &r ωπ τπ
    let pl_ty = ty_ctx.place_ty(most_spec_pl)?;
    if let Ty::Ref(Provenance::Value(prv), pl_own, _, _) = &pl_ty {
        // ω ≲ ωπ
        if pl_own < &own {
            return Err(format!(
                "Trying to use place expression with {} capability while it refers to a \
        loan with {} capability.",
                own, pl_own
            ));
        }

        // List<pi = pi□[πi]>
        let pl_ctxs_and_places_in_loans = ty_ctx
            .loans_for_prv(prv)?
            .iter()
            .map(|loan| &loan.place_expr)
            .map(|pl_expr| pl_expr.to_pl_ctx_and_most_specif_pl());
        // List<πe>, List<πi>, π
        // Refactor into own function
        let mut extended_reborrows = Vec::from(reborrows);
        extended_reborrows.extend(pl_ctxs_and_places_in_loans.map(|(_, pl)| pl));
        extended_reborrows.extend(std::iter::once(most_spec_pl.clone()));

        // ∀i ∈ {1...n}.Δ;Γ ⊢ω List<πe>,List<πi>,π  p□[pi] ⇒ {ω pi′}
        let mut all_potential_loans = ty_ctx
            .loans_for_prv(prv)?
            .iter()
            .map(|loan| &loan.place_expr)
            .try_fold(
                HashSet::<Loan>::new(),
                |mut loans, pl_expr| -> Result<HashSet<Loan>, String> {
                    let loans_for_possible_prv_pl_expr = ownership_safe(
                        kind_ctx,
                        ty_ctx,
                        reborrows,
                        own,
                        &pl_ctx_no_deref.insert_pl_expr(pl_expr.clone()),
                    )?;
                    loans.extend(loans_for_possible_prv_pl_expr);
                    Ok(loans)
                },
            )?;

        let currently_checked_pl_expr = pl_ctx_no_deref
            .insert_pl_expr(PlaceExpr::Deref(Box::new(most_spec_pl.to_place_expr())));
        if ownership_safe_under_existing_loans(ty_ctx, reborrows, own, &currently_checked_pl_expr) {
            all_potential_loans.insert(Loan {
                place_expr: currently_checked_pl_expr,
                own,
            });
            Ok(all_potential_loans)
        } else {
            Err("A borrow is being violated".to_string())
        }
    } else {
        // TODO ugly
        panic!("This should never happen.")
    }
}

fn ownership_safe_under_existing_loans(
    ty_ctx: &TyCtx,
    reborrows: &[Place],
    own: Ownership,
    pl_expr: &PlaceExpr,
) -> bool {
    ty_ctx.prv_mappings().all(|prv_mapping| {
        let PrvMapping { prv, loans } = prv_mapping;
        no_uniq_loan_overlap(own, pl_expr, loans)
            || exists_place_with_ref_to_prv_all_in_reborrow(ty_ctx, prv, reborrows)
    })
}

fn no_uniq_loan_overlap(own: Ownership, pl_expr: &PlaceExpr, loans: &HashSet<Loan>) -> bool {
    loans.iter().all(|loan| {
        !(own == Ownership::Uniq || loan.own == Ownership::Uniq)
            || !overlap(&loan.place_expr, &pl_expr)
    })
}

fn exists_place_with_ref_to_prv_all_in_reborrow(
    ty_ctx: &TyCtx,
    prv_name: &str,
    reborrows: &[Place],
) -> bool {
    let all_places = ty_ctx.all_places();
    let at_least_one = all_places.iter().any(|(_, ty)| {
        if let Ty::Ref(Provenance::Value(pn), _, _, _) = ty {
            prv_name == pn
        } else {
            false
        }
    });
    let all_in_reborrows = all_places.iter().all(|(place, ty)| {
        if let Ty::Ref(Provenance::Value(pn), _, _, _) = ty {
            if prv_name == pn {
                reborrows.iter().any(|reb_pl| reb_pl == place)
            } else {
                true
            }
        } else {
            true
        }
    });

    at_least_one && all_in_reborrows
}

fn overlap(pll: &PlaceExpr, plr: &PlaceExpr) -> bool {
    pll.prefix_of(plr) || plr.prefix_of(pll)
}
