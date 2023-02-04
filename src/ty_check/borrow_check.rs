use super::ctxs::{KindCtx, TyCtx};
use crate::ast::internal::{Loan, PlaceCtx, PrvMapping};
use crate::ast::*;
use crate::ty_check::ctxs::ExecBorrowCtx;
use crate::ty_check::error::BorrowingError;
use crate::ty_check::TyChecker;
use std::collections::HashSet;

type OwnResult<T> = Result<T, BorrowingError>;

fn borrowable_from_exec_under_exec(
    own: Ownership,
    under: &ExecExpr,
    from: &ExecExpr,
) -> OwnResult<()> {
    if own == Ownership::Shrd {
        return Ok(());
    }
    if under.exec.base != from.exec.base {
        return Err(BorrowingError::WrongDevice(
            under.exec.base.clone(),
            from.exec.base.clone(),
        ));
    }
    if under.exec.path.len() < from.exec.path.len() {
        panic!(
            "Unexpected: Trying to borrow from an execution resource that is \
                more specific than the current one."
        )
    }
    for (u, f) in under.exec.path.iter().zip(&from.exec.path) {
        if u != f {
            panic!("Unexpected: Trying to borrow from divergent execution resource.")
        }
    }
    // let mut previous_distrib = false;
    for e in &under.exec.path[from.exec.path.len()..] {
        if let ExecPathElem::Distrib(_) = e {
            // if previous_distrib {
            return Err(BorrowingError::MultipleDistribs);
            // }
            // previous_distrib = true;
        }
    }
    Ok(())
}
//
// Ownership Safety
//
//p is ω-safe under δ and γ, with reborrow exclusion list π , and may point to any of the loans in ωp
pub(super) fn ownership_safe(
    ty_checker: &TyChecker,
    kind_ctx: &KindCtx,
    exec_borrow_ctx: &ExecBorrowCtx,
    ty_ctx: &TyCtx,
    exec: &ExecExpr,
    reborrows: &[internal::Place],
    own: Ownership,
    p: &PlaceExpr,
) -> OwnResult<HashSet<Loan>> {
    let (pl_ctx, most_spec_pl) = p.to_pl_ctx_and_most_specif_pl();
    let p_exec = &ty_ctx.ident_ty(&most_spec_pl.ident)?.exec;
    borrowable_from_exec_under_exec(own, exec, p_exec)?;
    if p.is_place() {
        ownership_safe_place(exec_borrow_ctx, ty_ctx, reborrows, exec, own, p)
    } else {
        let pl_ctx_no_deref = pl_ctx.without_innermost_deref();
        // Γ(π) = &r ωπ τπ
        match &ty_ctx.place_dty(&most_spec_pl)?.dty {
            DataTyKind::Ref(reff) => match &reff.rgn {
                Provenance::Value(prv_val_name) => ownership_safe_deref(
                    ty_checker,
                    kind_ctx,
                    exec_borrow_ctx,
                    ty_ctx,
                    exec,
                    reborrows,
                    own,
                    &pl_ctx_no_deref,
                    &most_spec_pl,
                    prv_val_name.as_str(),
                    reff.own,
                    &p.split_tag_path,
                ),
                Provenance::Ident(_) => ownership_safe_deref_abs(
                    ty_checker,
                    kind_ctx,
                    exec_borrow_ctx,
                    ty_ctx,
                    exec,
                    reborrows,
                    own,
                    &pl_ctx_no_deref,
                    &most_spec_pl,
                    reff.own,
                    &p.split_tag_path,
                ),
            },
            DataTyKind::RawPtr(_) => ownership_safe_deref_raw(
                ty_checker,
                kind_ctx,
                ty_ctx,
                exec,
                reborrows,
                own,
                &pl_ctx_no_deref,
                &most_spec_pl,
            ),
            // TODO improve error message
            t => panic!("Is the type dead? `{:?}`", t),
        }
    }
}

// TODO remove!
fn ownership_safe_deref_raw(
    _ty_checker: &TyChecker,
    _kind_ctx: &KindCtx,
    _ty_ctx: &TyCtx,
    _exec: &ExecExpr,
    _reborrows: &[internal::Place],
    own: Ownership,
    pl_ctx_no_deref: &PlaceCtx,
    most_spec_pl: &internal::Place,
) -> OwnResult<HashSet<Loan>> {
    // TODO is anything here correct?
    let currently_checked_pl_expr = pl_ctx_no_deref.insert_pl_expr(PlaceExpr::new(
        PlaceExprKind::Deref(Box::new(most_spec_pl.to_place_expr())),
    ));
    let mut passed_through_prvs = HashSet::new();
    passed_through_prvs.insert(Loan {
        place_expr: currently_checked_pl_expr,
        own,
    });
    Ok(passed_through_prvs)
}

fn ownership_safe_place(
    exec_borrow_ctx: &ExecBorrowCtx,
    ty_ctx: &TyCtx,
    reborrows: &[internal::Place],
    exec: &ExecExpr,
    own: Ownership,
    p: &PlaceExpr,
) -> OwnResult<HashSet<Loan>> {
    ownership_safe_under_existing_loans(exec_borrow_ctx, ty_ctx, reborrows, exec, own, p)?;
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
    exec_borrow_ctx: &ExecBorrowCtx,
    ty_ctx: &TyCtx,
    exec: &ExecExpr,
    reborrows: &[internal::Place],
    own: Ownership,
    pl_ctx_no_deref: &PlaceCtx,
    most_spec_pl: &internal::Place,
    prv_val_name: &str,
    ref_own: Ownership,
    split_tag_path: &[SplitTag],
) -> OwnResult<HashSet<Loan>> {
    // Γ(r) = { ω′pi }
    let loans_in_prv = ty_ctx.loans_in_prv(prv_val_name)?;
    // ω ≲ ωπ
    new_own_weaker_equal(own, ref_own)?;
    // List<pi = pi□ [πi]>
    let pl_ctxs_and_places_in_loans = pl_ctxs_and_places_in_loans(loans_in_prv);
    // List<πe>, List<πi>, π
    // TODO Refactor into own function
    let mut extended_reborrows = Vec::from(reborrows);
    extended_reborrows.extend(pl_ctxs_and_places_in_loans.map(|(_, pl)| pl));
    extended_reborrows.extend(std::iter::once(most_spec_pl.clone()));

    // ∀i ∈ {1...n}.Δ;Γ ⊢ω List<πe>,List<πi>,π  p□[pi] ⇒ {ω pi′}
    let mut potential_prvs_after_subst = subst_pl_with_potential_prvs_ownership_safe(
        ty_checker,
        kind_ctx,
        exec_borrow_ctx,
        ty_ctx,
        exec,
        &extended_reborrows,
        own,
        pl_ctx_no_deref,
        loans_in_prv,
        split_tag_path,
    )?;

    let mut currently_checked_pl_expr = pl_ctx_no_deref.insert_pl_expr(PlaceExpr::new(
        PlaceExprKind::Deref(Box::new(most_spec_pl.to_place_expr())),
    ));
    currently_checked_pl_expr.split_tag_path = split_tag_path.to_vec();
    ownership_safe_under_existing_loans(
        exec_borrow_ctx,
        ty_ctx,
        &extended_reborrows,
        exec,
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
    exec_borrow_ctx: &ExecBorrowCtx,
    ty_ctx: &TyCtx,
    exec: &ExecExpr,
    reborrows: &[internal::Place],
    own: Ownership,
    pl_ctx_no_deref: &PlaceCtx,
    loans_in_prv: &HashSet<Loan>,
    split_tag_path: &[SplitTag],
) -> OwnResult<HashSet<Loan>> {
    let mut loans: HashSet<Loan> = HashSet::new();
    for pl_expr in loans_in_prv.iter().map(|loan| &loan.place_expr) {
        let mut insert_dereferenced_pl_expr = pl_ctx_no_deref.insert_pl_expr(pl_expr.clone());
        insert_dereferenced_pl_expr
            .split_tag_path
            .append(&mut split_tag_path.to_vec());
        let loans_for_possible_prv_pl_expr = ownership_safe(
            ty_checker,
            kind_ctx,
            exec_borrow_ctx,
            ty_ctx,
            exec,
            reborrows,
            own,
            &insert_dereferenced_pl_expr,
        )?;
        loans.extend(loans_for_possible_prv_pl_expr);
    }
    Ok(loans)
}

fn ownership_safe_deref_abs(
    ty_checker: &TyChecker,
    kind_ctx: &KindCtx,
    exec_borrow_ctx: &ExecBorrowCtx,
    ty_ctx: &TyCtx,
    exec: &ExecExpr,
    reborrows: &[internal::Place],
    own: Ownership,
    pl_ctx_no_deref: &PlaceCtx,
    most_spec_pl: &internal::Place,
    ref_own: Ownership,
    split_tag_path: &[SplitTag],
) -> OwnResult<HashSet<Loan>> {
    let mut currently_checked_pl_expr = pl_ctx_no_deref.insert_pl_expr(PlaceExpr::new(
        PlaceExprKind::Deref(Box::new(most_spec_pl.to_place_expr())),
    ));
    currently_checked_pl_expr.split_tag_path = split_tag_path.to_vec();
    ty_checker.place_expr_ty_under_exec_own(
        kind_ctx,
        ty_ctx,
        exec,
        own,
        &mut currently_checked_pl_expr,
    )?;
    new_own_weaker_equal(own, ref_own)?;
    ownership_safe_under_existing_loans(
        exec_borrow_ctx,
        ty_ctx,
        reborrows,
        exec,
        own,
        &currently_checked_pl_expr,
    )?;
    let mut passed_through_prvs = HashSet::new();
    passed_through_prvs.insert(Loan {
        place_expr: currently_checked_pl_expr,
        own,
    });
    Ok(passed_through_prvs)
}

fn pl_ctxs_and_places_in_loans(
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
    exec_borrow_ctx: &ExecBorrowCtx,
    ty_ctx: &TyCtx,
    reborrows: &[internal::Place],
    exec: &ExecExpr,
    own: Ownership,
    pl_expr: &PlaceExpr,
) -> OwnResult<()> {
    // TODO am I allowed to borrow the place from this exec (place must be from same distrib-level in exec)
    //  for select:

    for prv_mapping in ty_ctx.prv_mappings() {
        let PrvMapping { prv, loans } = prv_mapping;
        let no_uniq_overlap = no_uniq_loan_overlap(own, pl_expr, loans);
        if !no_uniq_overlap {
            return at_least_one_borrowing_place_and_all_in_reborrow(ty_ctx, prv, reborrows);
        }
    }
    // for (_, loans) in exec_borrow_ctx.iter() {
    //     no_uniq_loan_overlap(own, pl_expr, loans);
    // }

    Ok(())
}

fn no_uniq_loan_overlap(own: Ownership, pl_expr: &PlaceExpr, loans: &HashSet<Loan>) -> bool {
    loans.iter().all(|loan| {
        let comp_pl_expr = if pl_expr.is_place() {
            let (_, most_spec_pl) = loan.place_expr.to_pl_ctx_and_most_specif_pl();
            most_spec_pl.to_place_expr()
        } else {
            loan.place_expr.clone()
        };
        !((own == Ownership::Uniq || loan.own == Ownership::Uniq)
            && overlap(&comp_pl_expr, pl_expr))
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
    for (place, ty) in &all_places {
        if ty.contains_ref_to_prv(prv_name) && !reborrows.iter().any(|reb_pl| reb_pl == place) {
            return Err(BorrowingError::BorrowNotInReborrowList(place.clone()));
        }
    }
    Ok(())
}

fn overlap(pll: &PlaceExpr, plr: &PlaceExpr) -> bool {
    pll.prefix_of(plr) || plr.prefix_of(pll)
}
