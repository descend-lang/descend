use super::ctxs::TyCtx;
use crate::ast::internal::{Loan, PlaceCtx, PrvMapping};
use crate::ast::*;
use crate::ty_check::ctxs::{CtxResult, ExecBorrowCtx, GlobalCtx, KindCtx};
use crate::ty_check::error::BorrowingError;
use crate::ty_check::pl_expr::PlExprTyCtx;
use crate::ty_check::{pl_expr, ExprTyCtx};
use std::collections::HashSet;

type OwnResult<T> = Result<T, BorrowingError>;

pub(super) struct BorrowCheckCtx<'ctxt> {
    // TODO refactor move into ctx module and remove public
    pub gl_ctx: &'ctxt GlobalCtx,
    pub kind_ctx: &'ctxt KindCtx,
    pub ty_ctx: &'ctxt TyCtx,
    pub exec_borrow_ctx: &'ctxt ExecBorrowCtx,
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
            ty_ctx: &*expr_ty_ctx.ty_ctx,
            exec_borrow_ctx: &*expr_ty_ctx.exec_borrow_ctx,
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
            ty_ctx: &*self.ty_ctx,
            exec_borrow_ctx: &*self.exec_borrow_ctx,
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
    borrowable_under_exec(ctx, p, &ctx.exec)?;
    let (pl_ctx, most_spec_pl) = p.to_pl_ctx_and_most_specif_pl();
    if p.is_place() {
        ownership_safe_place(ctx, p)
    } else {
        let (pl_ctx_no_deref, select_exec_idents) = pl_ctx.without_innermost_deref();
        // Γ(π) = &r ωπ τπ
        match &ctx.ty_ctx.place_dty(&most_spec_pl)?.dty {
            DataTyKind::Ref(reff) => match &reff.rgn {
                Provenance::Value(prv_val_name) => ownership_safe_deref(
                    ctx,
                    &pl_ctx_no_deref,
                    &most_spec_pl,
                    select_exec_idents,
                    prv_val_name.as_str(),
                    reff.own,
                    &p.split_tag_path,
                ),
                Provenance::Ident(_) => ownership_safe_deref_abs(
                    ctx,
                    &pl_ctx_no_deref,
                    &most_spec_pl,
                    select_exec_idents,
                    reff.own,
                    &p.split_tag_path,
                ),
            },
            DataTyKind::RawPtr(_) => ownership_safe_deref_raw(ctx, &pl_ctx_no_deref, &most_spec_pl),
            // TODO improve error message
            t => panic!("Is the type dead? `{:?}`", t),
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
    //borrowable_from_exec_under_exec(ctx, p.to_place().as_ref().unwrap(), &[])?;
    ownership_safe_under_existing_loans(ctx, p)?;
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
    select_idents: &[Ident],
    prv_val_name: &str,
    ref_own: Ownership,
    split_tag_path: &[SplitTag],
) -> OwnResult<HashSet<Loan>> {
    // let select_execs = select_idents
    //     .iter()
    //     .map(|i| ctx.ty_ctx.get_exec_expr(i))
    //     .collect::<CtxResult<Vec<_>>>()?;
    //let from_exec = borrowable_from_exec_under_exec(ctx, most_spec_pl, &select_execs)?;
    // Γ(r) = { ω′pi }
    let loans_in_prv = ctx.ty_ctx.loans_in_prv(prv_val_name)?;
    // ω ≲ ωπ
    new_own_weaker_equal(ctx.own, ref_own)?;
    // List<pi = pi□ [πi]>
    let pl_ctxs_and_places_in_loans = pl_ctxs_and_places_in_loans(loans_in_prv);
    // List<πe>, List<πi>, π
    let mut ext_reborrow_ctx = ctx.extend_reborrows(
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
        split_tag_path,
    )?;

    let mut currently_checked_pl_expr = pl_ctx_no_deref.insert_pl_expr(PlaceExpr::new(
        PlaceExprKind::Deref(Box::new(most_spec_pl.to_place_expr())),
    ));
    currently_checked_pl_expr.split_tag_path = split_tag_path.to_vec();
    ownership_safe_under_existing_loans(&ext_reborrow_ctx, &currently_checked_pl_expr)?;
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
    split_tag_path: &[SplitTag],
) -> OwnResult<HashSet<Loan>> {
    let mut loans: HashSet<Loan> = HashSet::new();
    for pl_expr in loans_in_prv.iter().map(|loan| &loan.place_expr) {
        let mut insert_dereferenced_pl_expr = pl_ctx_no_deref.insert_pl_expr(pl_expr.clone());
        insert_dereferenced_pl_expr
            .split_tag_path
            .append(&mut split_tag_path.to_vec());
        let loans_for_possible_prv_pl_expr = ownership_safe(ctx, &insert_dereferenced_pl_expr)?;
        loans.extend(loans_for_possible_prv_pl_expr);
    }
    Ok(loans)
}

fn ownership_safe_deref_abs(
    ctx: &BorrowCheckCtx,
    pl_ctx_no_deref: &PlaceCtx,
    most_spec_pl: &internal::Place,
    select_idents: &[Ident],
    ref_own: Ownership,
    split_tag_path: &[SplitTag],
) -> OwnResult<HashSet<Loan>> {
    // let select_execs = select_idents
    //     .iter()
    //     .map(|i| ctx.ty_ctx.get_exec_expr(i))
    //     .collect::<CtxResult<Vec<_>>>()?;
    //borrowable_from_exec_under_exec(ctx, most_spec_pl, &select_execs)?;
    let mut currently_checked_pl_expr = pl_ctx_no_deref.insert_pl_expr(PlaceExpr::new(
        PlaceExprKind::Deref(Box::new(most_spec_pl.to_place_expr())),
    ));
    currently_checked_pl_expr.split_tag_path = split_tag_path.to_vec();
    pl_expr::ty_check(&PlExprTyCtx::from(ctx), &mut currently_checked_pl_expr)?;
    new_own_weaker_equal(ctx.own, ref_own)?;
    ownership_safe_under_existing_loans(ctx, &currently_checked_pl_expr)?;
    let mut passed_through_prvs = HashSet::new();
    passed_through_prvs.insert(Loan {
        place_expr: currently_checked_pl_expr,
        own: ctx.own,
    });
    Ok(passed_through_prvs)
}

fn borrowable_under_exec<'a>(
    ctx: &BorrowCheckCtx<'a>,
    p: &PlaceExpr,
    exec: &ExecExpr,
) -> OwnResult<()> {
    if ctx.own == Ownership::Shrd {
        return Ok(());
    }
    match &p.pl_expr {
        PlaceExprKind::Ident(ident) => {
            let from = &ctx.ty_ctx.ident_ty(ident)?.exec;
            no_distrib_in_diff(exec, from)
        }
        PlaceExprKind::Select(pl_expr, exec_idents) => {
            let mut exec = exec.clone();
            let mut select_execs = exec_idents
                .iter()
                .map(|i| ctx.ty_ctx.get_exec_expr(i))
                .collect::<CtxResult<Vec<_>>>()?;
            let mut select_exec_slice = select_execs.as_slice();
            while let Some((from, prevs)) = select_exec_slice.split_last() {
                if exec.exec.base != from.exec.base {
                    return Err(BorrowingError::WrongDevice(
                        exec.exec.base.clone(),
                        from.exec.base.clone(),
                    ));
                }
                if exec.exec.path.len() < from.exec.path.len() {
                    panic!(
                        "Unexpected: Trying to borrow from an execution resource that is \
                more specific than the current one."
                    )
                }
                for (u, f) in exec.exec.path.iter().zip(&from.exec.path) {
                    if u != f {
                        panic!("Unexpected: Trying to borrow from divergent execution resource.")
                    }
                }
                no_distrib_in_diff(&exec, from)?;
                exec = remove_last_distrib(&exec);
                select_exec_slice = prevs;
            }
            borrowable_under_exec(ctx, pl_expr, &exec)
        }
        PlaceExprKind::Deref(pl_expr) | PlaceExprKind::Proj(pl_expr, _) => {
            borrowable_under_exec(ctx, pl_expr, exec)
        }
    }
}

fn borrowable_from_exec_under_exec<'a>(
    ctx: &'a BorrowCheckCtx,
    pl: &internal::Place,
    mut execs: &[&ExecExpr],
) -> OwnResult<&'a ExecExpr> {
    if ctx.own == Ownership::Shrd {
        let from = &ctx.ty_ctx.ident_ty(&pl.ident)?.exec;
        return Ok(from);
    }
    let mut under = ctx.exec.clone();
    while let Some((from, prevs)) = execs.split_last() {
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
        no_distrib_in_diff(&under, from)?;
        under = remove_last_distrib(&under);
        execs = prevs;
    }
    let from = &ctx.ty_ctx.ident_ty(&pl.ident)?.exec;
    no_distrib_in_diff(&under, from)?;
    Ok(from)
}

fn no_distrib_in_diff(under: &ExecExpr, from: &ExecExpr) -> OwnResult<()> {
    for e in &under.exec.path[from.exec.path.len()..] {
        if let ExecPathElem::Distrib(_) = e {
            return Err(BorrowingError::MultipleDistribs);
        }
    }
    Ok(())
}

fn remove_last_distrib(exec: &ExecExpr) -> ExecExpr {
    let last_distrib_pos = exec
        .exec
        .path
        .iter()
        .rposition(|e| matches!(e, ExecPathElem::Distrib(_)));
    let removed_distrib_path = if let Some(ldp) = last_distrib_pos {
        exec.exec.path[..ldp].to_vec()
    } else {
        vec![]
    };
    ExecExpr::new(Exec::with_path(
        exec.exec.base.clone(),
        removed_distrib_path,
    ))
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

fn ownership_safe_under_existing_loans(ctx: &BorrowCheckCtx, pl_expr: &PlaceExpr) -> OwnResult<()> {
    // TODO am I allowed to borrow the place from this exec (place must be from same distrib-level in exec)
    //  for select:

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
