use super::ty_ctx::{PrvMapping, TyCtx};
use crate::ast::ty::*;
use crate::ast::*;
use std::collections::HashSet;

//
// Ownership Safety
//
//p is ω-safe under δ and γ, with reborrow exclusion list π , and may point to any of the loans in ωp
pub fn borrowable(
    kind_ctx: &KindCtx,
    ty_ctx: &TyCtx,
    reborrows: &[PlaceExpr],
    own: Ownership,
    p: &PlaceExpr,
) -> Result<Vec<Loan>, String> {
    if p.is_place() {
        if borrowable_under_existing_loans(ty_ctx, reborrows, own, p) {
            Ok(vec![Loan {
                place_expr: p.clone(),
                own_qual: own,
            }])
        } else {
            Err(String::from("A borrow is being violated."))
        }
    } else {
        panic!("Reborrowing not implemented yet.")
    }
}

fn borrowable_under_existing_loans(
    ty_ctx: &TyCtx,
    reborrows: &[PlaceExpr],
    own: Ownership,
    p: &PlaceExpr,
) -> bool {
    ty_ctx.prv_mappings().all(|prv_mapping| {
        let PrvMapping { prv, loans } = prv_mapping;
        no_uniq_loan_overlap(own, p, loans)
            || exists_place_with_ref_to_prv_all_in_reborrow(ty_ctx, prv, reborrows)
    })
}

fn no_uniq_loan_overlap(own: Ownership, place: &PlaceExpr, loans: &HashSet<Loan>) -> bool {
    loans.iter().all(|loan| {
        !(own == Ownership::Uniq || loan.own_qual == Ownership::Uniq)
            || !overlap(
                &loan.place_expr.to_place().unwrap(),
                &place.to_place().unwrap(),
            )
    })
}

// Invariant: for all place_expr in reborrows. place_expr.is_place()
fn exists_place_with_ref_to_prv_all_in_reborrow(
    ty_ctx: &TyCtx,
    prv_name: &str,
    reborrows: &[PlaceExpr],
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
                reborrows.iter().any(|reb| reb.equiv(place))
            } else {
                true
            }
        } else {
            true
        }
    });

    at_least_one && all_in_reborrows
}

fn overlap(pll: &Place, plr: &Place) -> bool {
    pll.prefix_of(plr) || plr.prefix_of(pll)
}
