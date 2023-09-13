use super::ctxs::TyCtx;
use crate::ast::internal::{Loan, PlaceCtx, PrvMapping};
use crate::ast::*;
use crate::ty_check::ctxs::{AccessCtx, GlobalCtx, KindCtx};
use crate::ty_check::error::BorrowingError;
use crate::ty_check::ExprTyCtx;
use std::collections::HashSet;

type OwnResult<T> = Result<T, BorrowingError>;

pub(super) struct BorrowCheckCtx<'ctxt> {
    // TODO refactor: move into ctx module and remove public
    pub gl_ctx: &'ctxt GlobalCtx,
    pub kind_ctx: &'ctxt KindCtx,
    pub ident_exec: Option<&'ctxt IdentExec>,
    pub ty_ctx: &'ctxt TyCtx,
    pub access_ctx: &'ctxt AccessCtx,
    pub exec: ExecExpr,
    pub reborrows: Vec<internal::Place>,
    pub own: Ownership,
}

impl<'ctxt> BorrowCheckCtx<'ctxt> {
    pub(super) fn new(
        expr_ty_ctx: &'ctxt ExprTyCtx,
        reborrows: Vec<internal::Place>,
        own: Ownership,
    ) -> Self {
        BorrowCheckCtx::<'ctxt> {
            gl_ctx: &*expr_ty_ctx.gl_ctx,
            kind_ctx: &*expr_ty_ctx.kind_ctx,
            ident_exec: expr_ty_ctx.ident_exec,
            ty_ctx: &*expr_ty_ctx.ty_ctx,
            access_ctx: &*expr_ty_ctx.access_ctx,
            exec: expr_ty_ctx.exec.clone(),
            reborrows: reborrows.to_vec(),
            own,
        }
    }

    fn extend_reborrows<I>(&self, iter: I) -> Self
    where
        I: Iterator<Item = internal::Place>,
    {
        let mut extended_reborrows = self.reborrows.clone();
        extended_reborrows.extend(iter);
        BorrowCheckCtx {
            gl_ctx: &*self.gl_ctx,
            kind_ctx: &*self.kind_ctx,
            ident_exec: self.ident_exec,
            ty_ctx: &*self.ty_ctx,
            access_ctx: &*self.access_ctx,
            exec: self.exec.clone(),
            reborrows: extended_reborrows,
            own: self.own,
        }
    }
}

//
// Ownership Safety
//
//p is ω-safe under δ and γ, with reborrow exclusion list π , and may point to any of the loans in ωp
pub(super) fn ownership_safe(ctx: &BorrowCheckCtx, p: &PlaceExpr) -> OwnResult<HashSet<Loan>> {
    narrowing_check(ctx, p, &ctx.exec)?;
    access_conflict_check(ctx, p)?;
    // no conflict with existing borrows
    // no conflicting access:
    //  no overlapping access with any exec != this.exec
    //  if exec = this.exec: then no access through different view
    let (pl_ctx, most_spec_pl) = p.to_pl_ctx_and_most_specif_pl();
    if p.is_place() {
        ownership_safe_place(ctx, p)
    } else {
        let pl_ctx_no_deref = pl_ctx.without_innermost_deref();
        // Γ(π) = &r ωπ τπ
        match &ctx.ty_ctx.place_dty(&most_spec_pl)?.dty {
            DataTyKind::Ref(reff) => match &reff.rgn {
                Provenance::Value(prv_val_name) => ownership_safe_deref(
                    ctx,
                    &pl_ctx_no_deref,
                    &most_spec_pl,
                    prv_val_name.as_str(),
                    reff.own,
                ),
                Provenance::Ident(_) => {
                    ownership_safe_deref_abs(ctx, &pl_ctx_no_deref, &most_spec_pl, reff.own)
                }
            },
            DataTyKind::RawPtr(_) => ownership_safe_deref_raw(ctx, &pl_ctx_no_deref, &most_spec_pl),
            // TODO improve error message
            t => ownership_safe_place(ctx, p), //panic!("Is the type dead? `{:?}`\n {:?}", t, p),
        }
    }
}

// TODO remove?
fn ownership_safe_deref_raw(
    ctx: &BorrowCheckCtx,
    pl_ctx_no_deref: &PlaceCtx,
    most_spec_pl: &internal::Place,
) -> OwnResult<HashSet<Loan>> {
    // TODO is this correct?
    let currently_checked_pl_expr = pl_ctx_no_deref.insert_pl_expr(PlaceExpr::new(
        PlaceExprKind::Deref(Box::new(most_spec_pl.to_place_expr())),
    ));
    let mut passed_through_prvs = HashSet::new();
    passed_through_prvs.insert(Loan {
        place_expr: currently_checked_pl_expr,
        own: ctx.own,
    });
    Ok(passed_through_prvs)
}

fn ownership_safe_place(ctx: &BorrowCheckCtx, p: &PlaceExpr) -> OwnResult<HashSet<Loan>> {
    ownership_safe_under_existing_borrows(ctx, p)?;
    let mut loan_set = HashSet::new();
    loan_set.insert(Loan {
        place_expr: p.clone(),
        own: ctx.own,
    });
    Ok(loan_set)
}

fn ownership_safe_deref(
    ctx: &BorrowCheckCtx,
    pl_ctx_no_deref: &PlaceCtx,
    most_spec_pl: &internal::Place,
    prv_val_name: &str,
    ref_own: Ownership,
) -> OwnResult<HashSet<Loan>> {
    // Γ(r) = { ω′pi }
    let loans_in_prv = ctx.ty_ctx.loans_in_prv(prv_val_name)?;
    // ω ≲ ωπ
    new_own_weaker_equal(ctx.own, ref_own)?;
    // List<pi = pi□ [πi]>
    let pl_ctxs_and_places_in_loans = pl_ctxs_and_places_in_loans(loans_in_prv);
    // List<πe>, List<πi>, π
    let ext_reborrow_ctx = ctx.extend_reborrows(
        pl_ctxs_and_places_in_loans
            .map(|(_, pl)| pl)
            .chain(std::iter::once(most_spec_pl.clone())),
    );
    // ext_reborrow_ctx.exec = from_exec.clone();

    // ∀i ∈ {1...n}.Δ;Γ ⊢ω List<πe>,List<πi>,π  p□[pi] ⇒ {ω pi′}
    let mut potential_prvs_after_subst = subst_pl_with_potential_prvs_ownership_safe(
        &ext_reborrow_ctx,
        pl_ctx_no_deref,
        loans_in_prv,
    )?;

    let currently_checked_pl_expr = pl_ctx_no_deref.insert_pl_expr(PlaceExpr::new(
        PlaceExprKind::Deref(Box::new(most_spec_pl.to_place_expr())),
    ));
    ownership_safe_under_existing_borrows(&ext_reborrow_ctx, &currently_checked_pl_expr)?;
    potential_prvs_after_subst.insert(Loan {
        place_expr: currently_checked_pl_expr,
        own: ctx.own,
    });
    Ok(potential_prvs_after_subst)
}

fn subst_pl_with_potential_prvs_ownership_safe(
    ctx: &BorrowCheckCtx,
    pl_ctx_no_deref: &PlaceCtx,
    loans_in_prv: &HashSet<Loan>,
) -> OwnResult<HashSet<Loan>> {
    let mut loans: HashSet<Loan> = HashSet::new();
    for pl_expr in loans_in_prv.iter().map(|loan| &loan.place_expr) {
        let insert_dereferenced_pl_expr = pl_ctx_no_deref.insert_pl_expr(pl_expr.clone());
        let loans_for_possible_prv_pl_expr = ownership_safe(ctx, &insert_dereferenced_pl_expr)?;
        loans.extend(loans_for_possible_prv_pl_expr);
    }
    Ok(loans)
}

fn ownership_safe_deref_abs(
    ctx: &BorrowCheckCtx,
    pl_ctx_no_deref: &PlaceCtx,
    most_spec_pl: &internal::Place,
    ref_own: Ownership,
) -> OwnResult<HashSet<Loan>> {
    let currently_checked_pl_expr = pl_ctx_no_deref.insert_pl_expr(PlaceExpr::new(
        PlaceExprKind::Deref(Box::new(most_spec_pl.to_place_expr())),
    ));
    // FIXME the type check should not have any effect, however guaranteeing that every place
    //  expression even those which are formed recursively seem cleaner
    // pl_expr::ty_check(&PlExprTyCtx::from(ctx), &mut currently_checked_pl_expr)?;
    new_own_weaker_equal(ctx.own, ref_own)?;
    ownership_safe_under_existing_borrows(ctx, &currently_checked_pl_expr)?;
    let mut passed_through_prvs = HashSet::new();
    passed_through_prvs.insert(Loan {
        place_expr: currently_checked_pl_expr,
        own: ctx.own,
    });
    Ok(passed_through_prvs)
}

fn narrowing_check(ctx: &BorrowCheckCtx, p: &PlaceExpr, exec: &ExecExpr) -> OwnResult<()> {
    if ctx.own == Ownership::Shrd {
        return Ok(());
    }
    match &p.pl_expr {
        PlaceExprKind::Ident(ident) => {
            let from = &ctx.ty_ctx.ident_ty(ident)?.exec;
            no_distrib_in_diff(exec, from)?;
            Ok(())
        }
        PlaceExprKind::Select(pl_expr, select_exec) => {
            if exec.exec.base != select_exec.exec.base {
                return Err(BorrowingError::WrongDevice(
                    exec.exec.base.clone(),
                    select_exec.exec.base.clone(),
                ));
            }
            if exec.exec.path.len() < select_exec.exec.path.len() {
                panic!("Unexpected: Can only select for current execution resource.",)
            }
            for (u, f) in exec.exec.path.iter().zip(&select_exec.exec.path) {
                if u != f {
                    panic!("Unexpected: Trying to borrow from divergent execution resource.")
                }
            }
            no_distrib_in_diff(exec, select_exec)?;
            let outer_exec = exec.remove_last_distrib();
            narrowing_check(ctx, pl_expr, &outer_exec)
        }
        PlaceExprKind::View(pl_expr, _)
        | PlaceExprKind::Deref(pl_expr)
        | PlaceExprKind::Proj(pl_expr, _)
        | PlaceExprKind::Idx(pl_expr, _) => narrowing_check(ctx, pl_expr, exec),
    }
}

fn access_conflict_check(ctx: &BorrowCheckCtx, p: &PlaceExpr) -> OwnResult<()> {
    for (ex, loans) in ctx.access_ctx.iter().filter(|(exec, _)| *exec != &ctx.exec) {
        if !no_uniq_loan_overlap(ctx.own, p, loans) {
            return Err(BorrowingError::ConflictingAccess);
        }
    }
    Ok(())
}

fn no_distrib_in_diff(under: &ExecExpr, from: &ExecExpr) -> OwnResult<()> {
    for e in &under.exec.path[from.exec.path.len()..] {
        if let ExecPathElem::ForAll(_) = e {
            return Err(BorrowingError::MultipleDistribs);
        }
    }
    Ok(())
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

fn ownership_safe_under_existing_borrows(
    ctx: &BorrowCheckCtx,
    pl_expr: &PlaceExpr,
) -> OwnResult<()> {
    for prv_mapping in ctx.ty_ctx.prv_mappings() {
        let PrvMapping { prv, loans } = prv_mapping;
        let no_uniq_overlap = no_uniq_loan_overlap(ctx.own, pl_expr, loans);
        if !no_uniq_overlap {
            return at_least_one_borrowing_place_and_all_in_reborrow(
                ctx.ty_ctx,
                prv,
                &ctx.reborrows,
            );
        }
    }
    // for (_, loans) in exec_borrow_ctx.iter() {
    //     no_uniq_loan_overlap(own, pl_expr, loans);
    // }

    Ok(())
}

fn no_uniq_loan_overlap(own: Ownership, pl_expr: &PlaceExpr, loans: &HashSet<Loan>) -> bool {
    loans.iter().all(|loan| {
        !((own == Ownership::Uniq || loan.own == Ownership::Uniq)
            && overlap(&loan.place_expr, pl_expr))
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

fn conflicting_path(pathl: &[PlExprPathElem], pathr: &[PlExprPathElem]) -> bool {
    for lr in pathl.iter().zip(pathr) {
        match lr {
            (PlExprPathElem::Idx(_), _) => return true,
            (v @ PlExprPathElem::View(_), path_elem) if v != path_elem => return true,
            (path_eleml, path_elemr) if path_eleml == path_elemr => {}
            (PlExprPathElem::Proj(i), PlExprPathElem::Proj(j)) if i != j => return false,
            _ => panic!("unexpected"),
        }
    }
    true
}

fn overlap(pll: &PlaceExpr, plr: &PlaceExpr) -> bool {
    let (pl_ident, pl_path) = pll.as_ident_and_path();
    let (pr_ident, pr_path) = plr.as_ident_and_path();
    if pl_ident == pr_ident {
        conflicting_path(&pl_path, &pr_path) || conflicting_path(&pr_path, &pl_path)
    } else {
        false
    }
}
