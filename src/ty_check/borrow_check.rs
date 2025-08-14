use super::ctxs::TyCtx;
use crate::arena_ast::internal::{Loan, PlaceCtx, PrvMapping};
use crate::arena_ast::*;
use crate::ty_check::ctxs::{AccessCtx, GlobalCtx, KindCtx};
use crate::ty_check::error::BorrowingError;
use crate::ty_check::exec::normalize;
use crate::ty_check::{exec, pre_decl, ExprTyCtx};
use bumpalo::{collections::Vec as BumpVec, Bump};
use std::collections::HashSet;

type OwnResult<'a, T> = Result<T, BorrowingError<'a>>;

pub(super) struct BorrowCheckCtx<'a> {
    // TODO refactor: move into ctx module and remove public
    pub gl_ctx: &'a GlobalCtx<'a>,
    pub nat_ctx: &'a NatCtx<'a>,
    pub kind_ctx: &'a KindCtx<'a>,
    pub ident_exec: Option<&'a IdentExec<'a>>,
    pub ty_ctx: &'a TyCtx<'a>,
    pub access_ctx: &'a AccessCtx<'a>,
    pub exec: ExecExpr<'a>,
    pub reborrows: Vec<internal::Place<'a>>,
    pub own: Ownership,
    pub unsafe_flag: bool,
}

impl<'a> BorrowCheckCtx<'a> {
    pub(super) fn new(
        expr_ty_ctx: &'a ExprTyCtx<'a>,
        reborrows: Vec<internal::Place<'a>>,
        own: Ownership,
    ) -> Self {
        BorrowCheckCtx {
            gl_ctx: &*expr_ty_ctx.gl_ctx,
            nat_ctx: &*expr_ty_ctx.nat_ctx,
            kind_ctx: &*expr_ty_ctx.kind_ctx,
            ident_exec: expr_ty_ctx.ident_exec,
            ty_ctx: &*expr_ty_ctx.ty_ctx,
            access_ctx: &*expr_ty_ctx.access_ctx,
            exec: expr_ty_ctx.exec.clone(),
            reborrows: reborrows.to_vec(),
            own,
            unsafe_flag: expr_ty_ctx.unsafe_flag,
        }
    }

    fn extend_reborrows<I>(&self, iter: I) -> Self
    where
        I: Iterator<Item = internal::Place<'a>>,
    {
        let mut extended_reborrows = self.reborrows.clone();
        extended_reborrows.extend(iter);
        BorrowCheckCtx {
            gl_ctx: &*self.gl_ctx,
            nat_ctx: &*self.nat_ctx,
            kind_ctx: &*self.kind_ctx,
            ident_exec: self.ident_exec,
            ty_ctx: &*self.ty_ctx,
            access_ctx: &*self.access_ctx,
            exec: self.exec.clone(),
            reborrows: extended_reborrows,
            own: self.own,
            unsafe_flag: self.unsafe_flag,
        }
    }
}

//
// Ownership Safety
//
//p is ω-safe under δ and γ, with reborrow exclusion list π , and may point to any of the loans in ωp
pub(super) fn access_safety_check<'a>(
    ctx: &'a BorrowCheckCtx<'a>,
    p: &'a PlaceExpr<'a>,
    arena: &'a Bump,
) -> OwnResult<'a, BumpVec<'a, Loan<'a>>> {
    if !ctx.unsafe_flag {
        narrowing_check(ctx, p, &ctx.exec, arena)?;
        access_conflict_check(ctx, p, arena)?;
    }
    borrow_check(ctx, p, arena)
}

pub(super) fn borrow_check<'a>(
    ctx: &'a BorrowCheckCtx<'a>,
    p: &'a PlaceExpr<'a>,
    arena: &'a Bump,
) -> OwnResult<'a, BumpVec<'a, Loan<'a>>> {
    let (pl_ctx, most_spec_pl) = p.to_pl_ctx_and_most_specif_pl(arena);

    let pl_ctx: &'a PlaceCtx<'a> = arena.alloc(pl_ctx);
    let most_spec_pl = arena.alloc(most_spec_pl);

    if p.is_place() {
        ownership_safe_place(ctx, p, arena)
    } else {
        let pl_ctx_no_deref = pl_ctx.without_innermost_deref(arena);

        // Γ(π) = &r ωπ τπ
        match &ctx.ty_ctx.place_dty(&most_spec_pl)?.dty {
            DataTyKind::Ref(reff) => match &reff.rgn {
                Provenance::Value(prv_val_name) => ownership_safe_deref(
                    ctx,
                    pl_ctx_no_deref,
                    most_spec_pl,
                    *prv_val_name,
                    reff.own,
                    arena,
                ),
                Provenance::Ident(_) => {
                    ownership_safe_deref_abs(ctx, pl_ctx_no_deref, most_spec_pl, reff.own, arena)
                }
            },
            DataTyKind::RawPtr(_) => {
                ownership_safe_deref_raw(ctx, pl_ctx_no_deref, most_spec_pl, arena)
            }
            // TODO improve error message
            t => ownership_safe_place(ctx, p, arena), //panic!("Is the type dead? `{:?}`\n {:?}", t, p),
        }
    }
}

// TODO remove?
/**
fn ownership_safe_deref_raw<'a>(
    ctx: &'a BorrowCheckCtx<'a>,
    pl_ctx_no_deref: &'a PlaceCtx<'a>,
    most_spec_pl: &'a internal::Place<'a>,
    arena: &'a Bump,
) -> OwnResult<'a, HashSet<Loan<'a>>> {
    // TODO is this correct?
    let currently_checked_pl_expr = pl_ctx_no_deref.insert_pl_expr(
        arena,
        PlaceExpr::new(PlaceExprKind::Deref(&most_spec_pl.to_place_expr(arena))),
    );
    let mut passed_through_prvs = HashSet::new();
    passed_through_prvs.insert(Loan {
        place_expr: currently_checked_pl_expr,
        own: ctx.own,
    });
    Ok(passed_through_prvs)
}
*/

fn ownership_safe_deref_raw<'a>(
    ctx: &'a BorrowCheckCtx<'a>,
    pl_ctx_no_deref: &'a PlaceCtx<'a>,
    most_spec_pl: &'a internal::Place<'a>,
    arena: &'a Bump,
) -> OwnResult<'a, BumpVec<'a, Loan<'a>>> {
    // 1) Build the inner PlaceExpr and bump-allocate it
    let inner_pe: PlaceExpr<'a> = most_spec_pl.to_place_expr(arena);
    let inner_ref: &'a PlaceExpr<'a> = arena.alloc(inner_pe);

    // 2) Create the Deref node around that borrowed reference
    let deref_pe = PlaceExpr::new(PlaceExprKind::Deref(inner_ref));

    // 3) Insert into the context to get back an &'a PlaceExpr<'a>
    let currently_checked_pl_expr = pl_ctx_no_deref.insert_pl_expr(arena, deref_pe);

    // 4) Build the result
    let mut passed_through_prvs = BumpVec::new_in(arena);
    passed_through_prvs.push(Loan {
        place_expr: currently_checked_pl_expr,
        own: ctx.own,
    });

    Ok(passed_through_prvs)
}

fn ownership_safe_place<'a>(
    ctx: &'a BorrowCheckCtx<'a>,
    p: &'a PlaceExpr<'a>,
    arena: &'a Bump,
) -> OwnResult<'a, BumpVec<'a, Loan<'a>>> {
    ownership_safe_under_existing_borrows(ctx, p, arena)?;
    let mut loan_set = BumpVec::new_in(arena);
    loan_set.push(Loan {
        place_expr: p.clone(),
        own: ctx.own,
    });
    Ok(loan_set)
}

fn ownership_safe_deref<'a>(
    ctx: &'a BorrowCheckCtx<'a>,
    pl_ctx_no_deref: &'a PlaceCtx<'a>,
    most_spec_pl: &'a internal::Place<'a>,
    prv_val_name: &str,
    ref_own: Ownership,
    arena: &'a Bump,
) -> OwnResult<'a, BumpVec<'a, Loan<'a>>> {
    // Γ(r) = { ω′pi }
    let loans_in_prv = ctx.ty_ctx.loans_in_prv(prv_val_name)?;
    // ω ≲ ωπ
    new_own_weaker_equal(ctx.own, ref_own)?;
    // List<pi = pi□ [πi]>
    let pl_ctxs_and_places_in_loans = pl_ctxs_and_places_in_loans(loans_in_prv, arena);
    // List<πe>, List<πi>, π
    let ext_reborrow_ctx = ctx.extend_reborrows(
        pl_ctxs_and_places_in_loans
            .map(|(_, pl)| pl)
            .chain(std::iter::once(most_spec_pl.clone())),
    );
    // ext_reborrow_ctx.exec = from_exec.clone();
    let ext_ctx: &'a BorrowCheckCtx<'a> = arena.alloc(ext_reborrow_ctx);

    // ∀i ∈ {1...n}.Δ;Γ ⊢ω List<πe>,List<πi>,π  p□[pi] ⇒ {ω pi′}
    let mut potential_prvs_after_subst =
        subst_pl_with_potential_prvs_ownership_safe(ext_ctx, pl_ctx_no_deref, loans_in_prv, arena)?;

    let inner_pe: PlaceExpr<'a> = most_spec_pl.to_place_expr(arena);
    let inner_ref: &'a PlaceExpr<'a> = arena.alloc(inner_pe);

    // 2) Wrap in a Deref and bump‐allocate that too
    let wrapper = PlaceExpr::new(PlaceExprKind::Deref(inner_ref));
    let stripped_ref: &'a PlaceExpr<'a> = arena.alloc(wrapper);

    ownership_safe_under_existing_borrows(ext_ctx, stripped_ref, arena)?;
    potential_prvs_after_subst.push(Loan {
        place_expr: stripped_ref.clone(),
        own: ctx.own,
    });
    Ok(potential_prvs_after_subst)
}

/**
fn subst_pl_with_potential_prvs_ownership_safe<'a>(
    ctx: &'a BorrowCheckCtx<'a>,
    pl_ctx_no_deref: &'a PlaceCtx<'a>,
    loans_in_prv: &HashSet<Loan<'a>>,
    arena: &'a Bump,
) -> OwnResult<'a, HashSet<Loan<'a>>> {
    let mut loans: HashSet<Loan<'a>> = HashSet::new();

    for pl_expr in loans_in_prv.iter().map(|loan| &loan.place_expr) {
        let insert_dereferenced_pl_expr = pl_ctx_no_deref.insert_pl_expr(arena, pl_expr.clone());
        let loans_for_possible_prv_pl_expr =
            access_safety_check(ctx, &insert_dereferenced_pl_expr, arena)?;
        loans.extend(loans_for_possible_prv_pl_expr);
    }

    Ok(loans)
}
*/

fn subst_pl_with_potential_prvs_ownership_safe<'a>(
    ctx: &'a BorrowCheckCtx<'a>,
    pl_ctx_no_deref: &'a PlaceCtx<'a>,
    loans_in_prv: &HashSet<Loan<'a>>,
    arena: &'a Bump,
) -> OwnResult<'a, BumpVec<'a, Loan<'a>>> {
    // 1) collect into a bump-vector
    let mut collected = BumpVec::new_in(arena);
    for loan in loans_in_prv {
        let base_pe: PlaceExpr<'a> = loan.place_expr.clone();
        let inserted_pe = pl_ctx_no_deref.insert_pl_expr(arena, base_pe);
        let pe_ref: &'a PlaceExpr<'a> = arena.alloc(inserted_pe);

        let new_loans = access_safety_check(ctx, pe_ref, arena)?;
        for l in new_loans {
            collected.push(l);
        }
    }

    // 2) deduplicate in place
    let mut seen = HashSet::new();
    collected.retain(|loan| seen.insert(loan.clone()));

    Ok(collected)
}

/**
fn ownership_safe_deref_abs<'a>(
    ctx: &'a BorrowCheckCtx<'a>,
    pl_ctx_no_deref: &'a PlaceCtx<'a>,
    most_spec_pl: &'a internal::Place<'a>,
    ref_own: Ownership,
    arena: &'a Bump,
) -> OwnResult<'a, BumpVec<'a, Loan<'a>>> {
    let currently_checked_pl_expr = pl_ctx_no_deref.insert_pl_expr(
        arena,
        PlaceExpr::new(PlaceExprKind::Deref(&most_spec_pl.to_place_expr(arena))),
    );
    // FIXME the type check should not have any effect, however guaranteeing that every place
    //  expression even those which are formed recursively seem cleaner
    // pl_expr::ty_check(&PlExprTyCtx::from(ctx), &mut currently_checked_pl_expr)?;
    new_own_weaker_equal(ctx.own, ref_own)?;
    ownership_safe_under_existing_borrows(ctx, &currently_checked_pl_expr, arena)?;
    let mut passed_through_prvs = BumpVec::new_in(arena);
    passed_through_prvs.push(Loan {
        place_expr: currently_checked_pl_expr,
        own: ctx.own,
    });
    Ok(passed_through_prvs)
}
    */

fn ownership_safe_deref_abs<'a>(
    ctx: &'a BorrowCheckCtx<'a>,
    pl_ctx_no_deref: &'a PlaceCtx<'a>,
    most_spec_pl: &'a internal::Place<'a>,
    ref_own: Ownership,
    arena: &'a Bump,
) -> OwnResult<'a, BumpVec<'a, Loan<'a>>> {
    // 1) Build and bump-allocate the inner PlaceExpr for the raw place
    let base_pe: PlaceExpr<'a> = most_spec_pl.to_place_expr(arena);
    let base_ref: &'a PlaceExpr<'a> = arena.alloc(base_pe);

    // 2) Insert into the context (still an owned PlaceExpr), then bump-allocate
    let inserted_pe: PlaceExpr<'a> = pl_ctx_no_deref.insert_pl_expr(arena, base_ref.clone());
    let inserted_ref: &'a PlaceExpr<'a> = arena.alloc(inserted_pe);

    // 3) Wrap that in a Deref, bump-allocate again
    let deref_pe = PlaceExpr::new(PlaceExprKind::Deref(inserted_ref));
    let deref_ref: &'a PlaceExpr<'a> = arena.alloc(deref_pe);

    // 4) Check ownership ordering
    new_own_weaker_equal(ctx.own, ref_own)?;

    // 5) Run the “under existing borrows” check
    ownership_safe_under_existing_borrows(ctx, deref_ref, arena)?;

    // 6) Return a single‐element BumpVec of the resulting loan
    let mut passed_through_prvs = BumpVec::new_in(arena);
    passed_through_prvs.push(Loan {
        place_expr: deref_ref.clone(),
        own: ctx.own,
    });

    Ok(passed_through_prvs)
}

fn narrowing_check<'a>(
    ctx: &'a BorrowCheckCtx<'a>,
    p: &'a PlaceExpr<'a>,
    active_ctx_exec: &'a ExecExpr<'a>,
    arena: &'a Bump,
) -> OwnResult<'a, ()> {
    if ctx.own == Ownership::Shrd {
        return Ok(());
    }
    match &p.pl_expr {
        PlaceExprKind::Ident(ident) => {
            narrowable(&ctx.ty_ctx.ident_ty(ident)?.exec, active_ctx_exec, arena)
        }
        PlaceExprKind::Select(pl_expr, select_exec) => {
            narrowable(select_exec, active_ctx_exec, arena)?;

            let mut outer_exec: ExecExpr<'a> = active_ctx_exec.remove_last_distrib(arena);

            exec::ty_check(
                ctx.nat_ctx,
                ctx.ty_ctx,
                ctx.ident_exec,
                &mut outer_exec,
                arena,
            )?;

            let outer_exec_ref: &'a ExecExpr<'a> = arena.alloc(outer_exec);

            narrowing_check(ctx, pl_expr, outer_exec_ref, arena)
        }
        PlaceExprKind::View(pl_expr, _)
        | PlaceExprKind::Deref(pl_expr)
        | PlaceExprKind::Proj(pl_expr, _)
        | PlaceExprKind::FieldProj(pl_expr, _)
        | PlaceExprKind::Idx(pl_expr, _) => narrowing_check(ctx, pl_expr, active_ctx_exec, arena),
    }
}

fn narrowable<'a>(
    from: &'a ExecExpr<'a>,
    to: &'a ExecExpr<'a>,
    arena: &'a Bump,
) -> OwnResult<'a, ()> {
    let normal_from = arena.alloc(normalize(from.clone(), arena));
    let normal_to = arena.alloc(normalize(to.clone(), arena));
    exec_is_prefix_of(normal_from, normal_to)?;
    no_forall_in_diff(normal_from, normal_to)
}

fn exec_is_prefix_of<'a>(prefix: &'a ExecExpr<'a>, of: &'a ExecExpr<'a>) -> OwnResult<'a, ()> {
    if prefix.exec.base != of.exec.base {
        return Err(BorrowingError::WrongDevice(
            of.exec.base.clone(),
            prefix.exec.base.clone(),
        ));
    }
    if of.exec.path.len() < prefix.exec.path.len() {
        return Err(BorrowingError::CannotNarrow);
    }
    for (u, f) in prefix.exec.path.iter().zip(&of.exec.path) {
        if u != f {
            return Err(BorrowingError::DivergingExec);
        }
    }
    Ok(())
}

fn access_conflict_check<'a>(
    ctx: &'a BorrowCheckCtx<'a>,
    p: &'a PlaceExpr<'a>,
    arena: &'a Bump,
) -> OwnResult<'a, ()> {
    for loan in ctx.access_ctx.hash_set() {
        if possible_conflict_with_previous_access(ctx.nat_ctx, ctx.own, p, loan, arena)? {
            return Err(BorrowingError::Conflict {
                checked: p.clone(),
                existing: loan.place_expr.clone(),
            });
        }
    }
    Ok(())
}

fn possible_conflict_with_previous_access<'a>(
    nat_ctx: &'a NatCtx<'a>,
    own: Ownership,
    p: &'a PlaceExpr<'a>,
    previous: &'a Loan<'a>,
    arena: &'a Bump,
) -> NatEvalResult<'a, bool> {
    if own == Ownership::Shrd && previous.own == Ownership::Shrd {
        return Ok(false);
    }

    let (p_ident, p_path_local) = p.as_ident_and_path(arena);
    let (l_ident, l_path_local) = previous.place_expr.as_ident_and_path(arena);

    let p_path: &'a [PlExprPathElem<'a>] = arena.alloc_slice_clone(&p_path_local);
    let l_path: &'a [PlExprPathElem<'a>] = arena.alloc_slice_clone(&l_path_local);

    if p_ident != l_ident {
        return Ok(false);
    }

    for (pe_p, pe_l) in p_path.iter().zip(l_path.iter()) {
        match (pe_p, pe_l) {
            (PlExprPathElem::Deref, PlExprPathElem::Deref) => {}
            (PlExprPathElem::Proj(kp), PlExprPathElem::Proj(kl)) => {
                if kp != kl {
                    return Ok(false);
                }
            }
            (PlExprPathElem::FieldProj(pident), PlExprPathElem::FieldProj(lident)) => {
                if pident.name != lident.name {
                    return Ok(false);
                }
            }
            (PlExprPathElem::Idx(i), PlExprPathElem::Idx(j)) => {
                if i.eval(nat_ctx)? != j.eval(nat_ctx)? {
                    return Ok(false);
                }
            }
            (
                PlExprPathElem::RangeSelec(plower, pupper),
                PlExprPathElem::RangeSelec(llower, lupper),
            ) => {
                if range_intersects(nat_ctx, plower, pupper, llower, lupper)? {
                    return Ok(true);
                }
                if !(plower.eval(nat_ctx)? == llower.eval(nat_ctx)?
                    && pupper.eval(nat_ctx)? == lupper.eval(nat_ctx)?)
                {
                    return Ok(false);
                }
            }
            (PlExprPathElem::View(p_view), PlExprPathElem::View(l_view))
                if p_view.equal(nat_ctx, l_view)? => {}
            (PlExprPathElem::Select(pexec), PlExprPathElem::Select(lexec))
                if pexec.equal(nat_ctx, lexec)? => {}
            _ => {
                return Ok(true);
            }
        }
    }
    if l_path.len() > p_path.len() {
        for elem in &l_path[p_path.len()..] {
            if let PlExprPathElem::Select(_) = elem {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn range_intersects<'a>(
    nat_ctx: &'a NatCtx<'a>,
    lower_left: &'a Nat<'a>,
    upper_left: &'a Nat<'a>,
    lower_right: &'a Nat<'a>,
    upper_right: &'a Nat<'a>,
) -> NatEvalResult<'a, bool> {
    Ok((lower_left.eval(nat_ctx)? < lower_right.eval(nat_ctx)?
        && upper_left.eval(nat_ctx)? <= lower_right.eval(nat_ctx)?)
        || (lower_left.eval(nat_ctx)? >= upper_right.eval(nat_ctx)?
            && upper_left.eval(nat_ctx)? > upper_right.eval(nat_ctx)?))
}

fn no_forall_in_diff<'a>(from: &'a ExecExpr<'a>, under: &'a ExecExpr<'a>) -> OwnResult<'a, ()> {
    if from.exec.path.len() > under.exec.path.len() {
        return Err(BorrowingError::CannotNarrow);
    }
    for e in &under.exec.path[from.exec.path.len()..] {
        if let ExecPathElem::ForAll(_) = e {
            return Err(BorrowingError::MultipleDistribs);
        }
    }
    Ok(())
}

/**
fn pl_ctxs_and_places_in_loans<'a>(
    loans: &HashSet<Loan<'a>>,
    arena: &'a Bump,
) -> impl Iterator<Item = (PlaceCtx<'a>, internal::Place<'a>)> + 'a {
    // was '_ before, what does that mean
    loans
        .iter()
        .map(|loan| &loan.place_expr)
        .map(|pl_expr| pl_expr.to_pl_ctx_and_most_specif_pl(arena))
}
*/

fn pl_ctxs_and_places_in_loans<'a, I>(
    loans: I,
    arena: &'a Bump,
) -> impl Iterator<Item = (PlaceCtx<'a>, internal::Place<'a>)> + 'a
where
    I: IntoIterator<Item = &'a Loan<'a>> + 'a,
    <I as IntoIterator>::IntoIter: 'a,
{
    loans
        .into_iter()
        .map(move |loan| loan.place_expr.to_pl_ctx_and_most_specif_pl(arena))
}

fn new_own_weaker_equal<'a>(checked_own: Ownership, ref_own: Ownership) -> OwnResult<'a, ()> {
    if ref_own < checked_own {
        Err(BorrowingError::ConflictingOwnership)
    } else {
        Ok(())
    }
}

fn ownership_safe_under_existing_borrows<'a>(
    ctx: &'a BorrowCheckCtx<'a>,
    pl_expr: &'a PlaceExpr<'a>,
    arena: &'a Bump,
) -> OwnResult<'a, ()> {
    if !ctx.unsafe_flag {
        for prv_mapping in ctx.ty_ctx.prv_mappings() {
            let PrvMapping { prv, loans } = prv_mapping;
            let no_uniq_overlap = no_uniq_loan_overlap(ctx.own, pl_expr, loans, arena).is_none();
            if !no_uniq_overlap {
                return at_least_one_borrowing_place_and_all_in_reborrow(
                    ctx.ty_ctx,
                    prv,
                    &ctx.reborrows,
                    arena,
                );
            }
        }
    }
    Ok(())
}

/**
// returns None if there is no unique loan overlap or Some with the existing overlapping loan
fn no_uniq_loan_overlap<'a>(
    own: Ownership,
    pl_expr: &'a PlaceExpr<'a>,
    loans: &HashSet<Loan<'a>>,
    arena: &'a Bump,
) -> Option<Loan<'a>> {
    for l in loans {
        if (own == Ownership::Uniq || l.own == Ownership::Uniq)
            && overlap(&l.place_expr, pl_expr, arena)
        {
            return Some(l.clone());
        }
    }
    None
}
*/

/// Returns `Some(clashing_loan)` if there is any unique‐ownership overlap,
/// or `None` if none of the loans conflict.
fn no_uniq_loan_overlap<'a, I>(
    own: Ownership,
    pl_expr: &'a PlaceExpr<'a>,
    loans: I,
    arena: &'a Bump,
) -> Option<Loan<'a>>
where
    I: IntoIterator<Item = &'a Loan<'a>>,
{
    loans.into_iter().find_map(|l| {
        // must be at least one Unique side, and the places must overlap
        if (own == Ownership::Uniq || l.own == Ownership::Uniq)
            && overlap(&l.place_expr, pl_expr, arena)
        {
            Some(l.clone())
        } else {
            None
        }
    })
}

fn at_least_one_borrowing_place_and_all_in_reborrow<'a>(
    ty_ctx: &'a TyCtx<'a>,
    prv_name: &str,
    reborrows: &[internal::Place<'a>],
    arena: &'a Bump,
) -> OwnResult<'a, ()> {
    let all_places = ty_ctx.all_places(arena);
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

fn conflicting_path<'a>(pathl: &[PlExprPathElem<'a>], pathr: &[PlExprPathElem<'a>]) -> bool {
    for lr in pathl.iter().zip(pathr) {
        match lr {
            (PlExprPathElem::Idx(_), _) => return true,
            (v @ PlExprPathElem::View(iv), path_elem)
                if v != path_elem && iv.name.name != pre_decl::SELECT_RANGE =>
            {
                return true
            }
            (PlExprPathElem::View(ivl), PlExprPathElem::View(ivr))
                if ivl != ivr
                    && ivl.name.name == pre_decl::SELECT_RANGE
                    && ivr.name.name == pre_decl::SELECT_RANGE =>
            {
                match (
                    &ivr.gen_args[0],
                    &ivl.gen_args[1],
                    &ivl.gen_args[0],
                    &ivr.gen_args[1],
                ) {
                    (
                        ArgKinded::Nat(_lower_left),
                        ArgKinded::Nat(_upper_left),
                        ArgKinded::Nat(_lower_right),
                        ArgKinded::Nat(_upper_right),
                    ) => {
                        // intersecting ranges
                        // TAKE CARE: the comparisons are partial and return false in case the
                        //  the values are not comparable
                        // return !((lower_left < lower_right && upper_left <= lower_right)
                        //     || (lower_left >= upper_right && upper_left > upper_right));
                        return false;
                    }
                    _ => panic!("expected nats"),
                }
            }
            (PlExprPathElem::Proj(i), PlExprPathElem::Proj(j)) if i != j => return false,
            (path_eleml, path_elemr) if path_eleml == path_elemr => {}
            _ => panic!("unexpected"),
        }
    }
    true
}

fn overlap<'a>(pll: &'a PlaceExpr<'a>, plr: &'a PlaceExpr<'a>, arena: &'a Bump) -> bool {
    let (pl_ident, pl_path) = pll.as_ident_and_path(arena);
    let (pr_ident, pr_path) = plr.as_ident_and_path(arena);
    if pl_ident == pr_ident {
        conflicting_path(&pl_path, &pr_path) || conflicting_path(&pr_path, &pl_path)
    } else {
        false
    }
}
