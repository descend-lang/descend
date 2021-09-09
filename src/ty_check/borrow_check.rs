use super::ctxs::{KindCtx, TyCtx};
use crate::ast::internal::{Loan, PlaceCtx, PrvMapping};
use crate::ast::*;
use crate::ty_check::error::BorrowingError;
use crate::ty_check::error::BorrowingError::TyError;
use crate::ty_check::TyChecker;
use std::collections::HashSet;

type OwnResult<T> = Result<T, BorrowingError>;

//
// Ownership Safety
//
//p is ω-safe under δ and γ, with reborrow exclusion list π , and may point to any of the loans in ωp
pub(super) fn ownership_safe(
    ty_checker: &TyChecker,
    kind_ctx: &KindCtx,
    ty_ctx: &TyCtx,
    exec: Exec,
    reborrows: &[internal::Place],
    own: Ownership,
    p: &PlaceExpr,
) -> OwnResult<HashSet<Loan>> {
    if p.is_place() {
        ownership_safe_place(ty_ctx, reborrows, own, p)
    } else {
        let (pl_ctx, most_spec_pl) = p.to_pl_ctx_and_most_specif_pl();
        let pl_ctx_no_deref = pl_ctx.without_innermost_deref();
        // Γ(π) = &r ωπ τπ
        match ty_ctx.place_ty(&most_spec_pl)?.ty {
            TyKind::Data(DataTy::Ref(Provenance::Value(prv_val_name), ref_own, _, _)) => {
                ownership_safe_deref(
                    ty_checker,
                    kind_ctx,
                    ty_ctx,
                    exec,
                    reborrows,
                    own,
                    &pl_ctx_no_deref,
                    &most_spec_pl,
                    prv_val_name.as_str(),
                    ref_own,
                )
            }
            TyKind::Data(DataTy::Ref(Provenance::Ident(_), ref_own, _, _)) => {
                ownership_safe_deref_abs(
                    ty_checker,
                    kind_ctx,
                    ty_ctx,
                    exec,
                    reborrows,
                    own,
                    &pl_ctx_no_deref,
                    &most_spec_pl,
                    ref_own,
                )
            }
            // TODO improve error message
            _ => panic!("Is the type dead?"),
        }
    }
}

fn ownership_safe_place(
    ty_ctx: &TyCtx,
    reborrows: &[internal::Place],
    own: Ownership,
    p: &PlaceExpr,
) -> OwnResult<HashSet<Loan>> {
    ownership_safe_under_existing_loans(ty_ctx, reborrows, own, p)?;
    let mut loan_set = HashSet::new();
    loan_set.insert(Loan {
        place_expr: p.clone(),
        own,
    });
    Ok(loan_set)
}

fn ownership_safe_deref(
    ty_checker: &TyChecker,
    kind_ctx: &KindCtx,
    ty_ctx: &TyCtx,
    exec: Exec,
    reborrows: &[internal::Place],
    own: Ownership,
    pl_ctx_no_deref: &PlaceCtx,
    most_spec_pl: &internal::Place,
    ref_prv_val_name: &str,
    ref_own: Ownership,
) -> OwnResult<HashSet<Loan>> {
    // Γ(r) = { ω′pi }
    let loans_for_ref_prv = ty_ctx.loans_for_prv(ref_prv_val_name)?;
    // ω ≲ ωπ
    new_own_weaker_equal(own, ref_own)?;
    // List<pi = pi□ [πi]>
    let pl_ctxs_and_places_in_loans = pl_ctxs_and_places_from_loans(loans_for_ref_prv);
    // List<πe>, List<πi>, π
    // TODO Refactor into own function
    let mut extended_reborrows = Vec::from(reborrows);
    extended_reborrows.extend(pl_ctxs_and_places_in_loans.map(|(_, pl)| pl));
    extended_reborrows.extend(std::iter::once(most_spec_pl.clone()));

    // ∀i ∈ {1...n}.Δ;Γ ⊢ω List<πe>,List<πi>,π  p□[pi] ⇒ {ω pi′}
    let mut potential_prvs_after_subst = subst_pl_with_potential_prvs_ownership_safe(
        ty_checker,
        kind_ctx,
        ty_ctx,
        exec,
        &extended_reborrows,
        own,
        pl_ctx_no_deref,
        loans_for_ref_prv,
    )?;

    let currently_checked_pl_expr = pl_ctx_no_deref.insert_pl_expr(PlaceExpr::new(
        PlaceExprKind::Deref(Box::new(most_spec_pl.to_place_expr())),
    ));
    ownership_safe_under_existing_loans(
        ty_ctx,
        &extended_reborrows,
        own,
        &currently_checked_pl_expr,
    )?;
    potential_prvs_after_subst.insert(Loan {
        place_expr: currently_checked_pl_expr,
        own,
    });
    Ok(potential_prvs_after_subst)
}

fn subst_pl_with_potential_prvs_ownership_safe(
    ty_checker: &TyChecker,
    kind_ctx: &KindCtx,
    ty_ctx: &TyCtx,
    exec: Exec,
    reborrows: &[internal::Place],
    own: Ownership,
    pl_ctx_no_deref: &PlaceCtx,
    loans_for_ref_prv: &HashSet<Loan>,
) -> OwnResult<HashSet<Loan>> {
    loans_for_ref_prv
        .iter()
        .map(|loan| &loan.place_expr)
        .try_fold(
            HashSet::<Loan>::new(),
            |mut loans, pl_expr| -> OwnResult<HashSet<Loan>> {
                let insert_dereferenced_pl_expr = &pl_ctx_no_deref.insert_pl_expr(pl_expr.clone());
                let loans_for_possible_prv_pl_expr = ownership_safe(
                    ty_checker,
                    kind_ctx,
                    ty_ctx,
                    exec,
                    reborrows,
                    own,
                    insert_dereferenced_pl_expr,
                )?;
                loans.extend(loans_for_possible_prv_pl_expr);
                Ok(loans)
            },
        )
}

fn ownership_safe_deref_abs(
    ty_checker: &TyChecker,
    kind_ctx: &KindCtx,
    ty_ctx: &TyCtx,
    exec: Exec,
    reborrows: &[internal::Place],
    own: Ownership,
    pl_ctx_no_deref: &PlaceCtx,
    most_spec_pl: &internal::Place,
    ref_own: Ownership,
) -> OwnResult<HashSet<Loan>> {
    let currently_checked_pl_expr = pl_ctx_no_deref.insert_pl_expr(PlaceExpr::new(
        PlaceExprKind::Deref(Box::new(most_spec_pl.to_place_expr())),
    ));
    let _ty = ty_checker.place_expr_ty_under_exec_own(
        kind_ctx,
        ty_ctx,
        exec,
        own,
        &currently_checked_pl_expr,
    )?;
    new_own_weaker_equal(own, ref_own)?;
    ownership_safe_under_existing_loans(ty_ctx, reborrows, own, &currently_checked_pl_expr)?;
    let mut passed_through_prvs = HashSet::new();
    passed_through_prvs.insert(Loan {
        place_expr: currently_checked_pl_expr,
        own,
    });
    Ok(passed_through_prvs)
}

fn pl_ctxs_and_places_from_loans(
    loans: &HashSet<Loan>,
) -> impl Iterator<Item = (PlaceCtx, internal::Place)> + '_ {
    loans
        .iter()
        .map(|loan| &loan.place_expr)
        .map(|pl_expr| pl_expr.to_pl_ctx_and_most_specif_pl())
}

fn new_own_weaker_equal(checked_own: Ownership, ref_own: Ownership) -> OwnResult<()> {
    if ref_own < checked_own {
        Err(BorrowingError::ConflictingOwnership)
    } else {
        Ok(())
    }
}

fn ownership_safe_under_existing_loans(
    ty_ctx: &TyCtx,
    reborrows: &[internal::Place],
    own: Ownership,
    pl_expr: &PlaceExpr,
) -> OwnResult<()> {
    ty_ctx.prv_mappings().try_for_each(|prv_mapping| {
        let PrvMapping { prv, loans } = prv_mapping;
        let no_uniq_overlap = no_uniq_loan_overlap(own, pl_expr, loans);
        if !no_uniq_overlap {
            at_least_one_borrowing_place_and_all_in_reborrow(ty_ctx, prv, reborrows)?;
        }
        Ok(())
    })
}

fn no_uniq_loan_overlap(own: Ownership, pl_expr: &PlaceExpr, loans: &HashSet<Loan>) -> bool {
    loans.iter().all(|loan| {
        let (_, most_spec_pl) = loan.place_expr.to_pl_ctx_and_most_specif_pl();
        !((own == Ownership::Uniq || loan.own == Ownership::Uniq)
            && overlap(&most_spec_pl.to_place_expr(), pl_expr))
    })
}

fn at_least_one_borrowing_place_and_all_in_reborrow(
    ty_ctx: &TyCtx,
    prv_name: &str,
    reborrows: &[internal::Place],
) -> OwnResult<()> {
    let all_places = ty_ctx.all_places();
    // check that a borrow with given provenance exists.
    // It could not exist for example in case it is used for a parameter
    // during function application. The second part of this function would succeed in this case
    // although it shouldn't because functions must not allow aliasing via parameters.
    let at_least_one = all_places
        .iter()
        .any(|(_, ty)| ty.contains_ref_to_prv(prv_name));
    if !at_least_one {
        return Err(BorrowingError::TemporaryConflictingBorrow(
            prv_name.to_string(),
        ));
    }
    // If there exists a place that is borrowing via provenance, then check that it is in the
    // reborrow exclusion list.
    all_places.iter().try_for_each(|(place, ty)| {
        if ty.contains_ref_to_prv(prv_name) && !reborrows.iter().any(|reb_pl| reb_pl == place) {
            return Err(BorrowingError::BorrowNotInReborrowList(place.clone()));
        }
        Ok(())
    })
}

fn overlap(pll: &PlaceExpr, plr: &PlaceExpr) -> bool {
    pll.prefix_of(plr) || plr.prefix_of(pll)
}
