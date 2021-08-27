use super::ctxs::{KindCtx, TyCtx};
use crate::ast::internal::{Loan, PlaceCtx};
use crate::ast::*;
use crate::parser::SourceCode;
use crate::ty_check::error::OwnError;
use std::collections::HashSet;

type OwnResult<T> = Result<T, OwnError>;

pub(super) struct OwnershipChecker<'a> {
    source: &'a SourceCode<'a>,
}

impl<'a> OwnershipChecker<'a> {
    pub fn new(source: &'a SourceCode<'a>) -> Self {
        OwnershipChecker { source }
    }

    //
    // Ownership Safety
    //
    //p is ω-safe under δ and γ, with reborrow exclusion list π , and may point to any of the loans in ωp
    pub(super) fn ownership_safe(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        reborrows: &[internal::Place],
        own: Ownership,
        p: &PlaceExpr,
    ) -> OwnResult<HashSet<Loan>> {
        if p.is_place() {
            self.ownership_safe_place(ty_ctx, reborrows, own, p)
        } else {
            let (pl_ctx, most_spec_pl) = p.to_pl_ctx_and_most_specif_pl();
            let pl_ctx_no_deref = pl_ctx.without_innermost_deref();
            // Γ(π) = &r ωπ τπ
            match ty_ctx.place_ty(&most_spec_pl)?.ty {
                TyKind::Data(DataTy::Ref(Provenance::Value(prv_val_name), ref_own, _, _)) => self
                    .ownership_safe_deref(
                        kind_ctx,
                        ty_ctx,
                        reborrows,
                        own,
                        &pl_ctx_no_deref,
                        &most_spec_pl,
                        prv_val_name.as_str(),
                        ref_own,
                    ),
                TyKind::Data(DataTy::Ref(Provenance::Ident(_), ref_own, _, _)) => self
                    .ownership_safe_deref_abs(
                        kind_ctx,
                        ty_ctx,
                        reborrows,
                        own,
                        &pl_ctx_no_deref,
                        &most_spec_pl,
                        ref_own,
                    ),
                // TODO improve error message
                _ => panic!("Is the type dead?"),
            }
        }
    }

    fn ownership_safe_place(
        &self,
        ty_ctx: &TyCtx,
        reborrows: &[internal::Place],
        own: Ownership,
        p: &PlaceExpr,
    ) -> OwnResult<HashSet<Loan>> {
        if self.ownership_safe_under_existing_loans(ty_ctx, reborrows, own, p) {
            let mut loan_set = HashSet::new();
            loan_set.insert(Loan {
                place_expr: p.clone(),
                own,
            });
            Ok(loan_set)
        } else {
            Err(OwnError::ConflictingBorrow(p.clone(), own))
        }
    }

    fn ownership_safe_deref(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
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
        self.check_own_lte_ref(own, ref_own)?;
        // List<pi = pi□ [πi]>
        let pl_ctxs_and_places_in_loans = Self::pl_ctxs_and_places_from_loans(loans_for_ref_prv);
        // List<πe>, List<πi>, π
        // TODO Refactor into own function
        let mut extended_reborrows = Vec::from(reborrows);
        extended_reborrows.extend(pl_ctxs_and_places_in_loans.map(|(_, pl)| pl));
        extended_reborrows.extend(std::iter::once(most_spec_pl.clone()));

        // ∀i ∈ {1...n}.Δ;Γ ⊢ω List<πe>,List<πi>,π  p□[pi] ⇒ {ω pi′}
        let mut potential_prvs_after_subst = self.subst_pl_with_potential_prvs_ownership_safe(
            kind_ctx,
            ty_ctx,
            &extended_reborrows,
            own,
            &pl_ctx_no_deref,
            loans_for_ref_prv,
        )?;

        let currently_checked_pl_expr = pl_ctx_no_deref.insert_pl_expr(PlaceExpr::new(
            PlaceExprKind::Deref(Box::new(most_spec_pl.to_place_expr())),
        ));
        if self.ownership_safe_under_existing_loans(
            ty_ctx,
            reborrows,
            own,
            &currently_checked_pl_expr,
        ) {
            potential_prvs_after_subst.insert(Loan {
                place_expr: currently_checked_pl_expr,
                own,
            });
            Ok(potential_prvs_after_subst)
        } else {
            Err(OwnError::ConflictingBorrow(
                currently_checked_pl_expr.clone(),
                own,
            ))
        }
    }

    fn subst_pl_with_potential_prvs_ownership_safe(
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
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
                    let insert_dereferenced_pl_expr =
                        &pl_ctx_no_deref.insert_pl_expr(pl_expr.clone());
                    let loans_for_possible_prv_pl_expr = self.ownership_safe(
                        kind_ctx,
                        ty_ctx,
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
        &self,
        kind_ctx: &KindCtx,
        ty_ctx: &TyCtx,
        reborrows: &[internal::Place],
        own: Ownership,
        pl_ctx_no_deref: &PlaceCtx,
        most_spec_pl: &internal::Place,
        ref_own: Ownership,
    ) -> OwnResult<HashSet<Loan>> {
        let currently_checked_pl_expr = pl_ctx_no_deref.insert_pl_expr(PlaceExpr::new(
            PlaceExprKind::Deref(Box::new(most_spec_pl.to_place_expr())),
        ));
        // TODO why would this check be needed if it is not needed for dereferencing with prv values?
        //let ty = super::place_expr_ty_under_own(kind_ctx, ty_ctx, own, &currently_checked_pl_expr)?;
        self.check_own_lte_ref(own, ref_own)?;
        if self.ownership_safe_under_existing_loans(
            ty_ctx,
            reborrows,
            own,
            &currently_checked_pl_expr,
        ) {
            let mut passed_through_prvs = HashSet::new();
            passed_through_prvs.insert(Loan {
                place_expr: currently_checked_pl_expr,
                own,
            });
            Ok(passed_through_prvs)
        } else {
            Err(OwnError::ConflictingBorrow(
                currently_checked_pl_expr.clone(),
                own,
            ))
        }
    }

    fn pl_ctxs_and_places_from_loans(
        loans: &HashSet<Loan>,
    ) -> impl Iterator<Item = (PlaceCtx, internal::Place)> + '_ {
        loans
            .iter()
            .map(|loan| &loan.place_expr)
            .map(|pl_expr| pl_expr.to_pl_ctx_and_most_specif_pl())
    }

    fn check_own_lte_ref(&self, checked_own: Ownership, ref_own: Ownership) -> OwnResult<()> {
        if ref_own < checked_own {
            Err(OwnError::ConflictingOwnership(checked_own, ref_own))
        } else {
            Ok(())
        }
    }

    fn ownership_safe_under_existing_loans(
        &self,
        ty_ctx: &TyCtx,
        reborrows: &[internal::Place],
        own: Ownership,
        pl_expr: &PlaceExpr,
    ) -> bool {
        println!("WARNING: Ownership safety (overlapping loan) checks disabled.");
        // ty_ctx.prv_mappings().all(|prv_mapping| {
        //     let PrvMapping { prv, loans } = prv_mapping;
        //     no_uniq_loan_overlap(own, pl_expr, loans)
        //         || exists_place_with_ref_to_prv_all_in_reborrow(ty_ctx, prv, reborrows)
        // })
        true
    }

    fn no_uniq_loan_overlap(
        &self,
        own: Ownership,
        pl_expr: &PlaceExpr,
        loans: &HashSet<Loan>,
    ) -> bool {
        loans.iter().all(|loan| {
            !(own == Ownership::Uniq || loan.own == Ownership::Uniq)
                || !self.overlap(
                    &loan
                        .place_expr
                        .to_pl_ctx_and_most_specif_pl()
                        .1
                        .to_place_expr(),
                    &pl_expr,
                )
        })
    }

    // TODO does this not have to include views?
    fn exists_place_with_ref_to_prv_all_in_reborrow(
        &self,
        ty_ctx: &TyCtx,
        prv_name: &str,
        reborrows: &[internal::Place],
    ) -> bool {
        println!(
            "Check exists place with ref to prv all in reborrow for reborrow list:\n {:?}",
            reborrows
        );
        let all_places = ty_ctx.all_places();
        let at_least_one = all_places.iter().any(|(_, ty)| {
            if let TyKind::Data(DataTy::Ref(Provenance::Value(pn), _, _, _)) = &ty.ty {
                prv_name == pn
            } else {
                false
            }
        });
        let all_in_reborrows = all_places.iter().all(|(place, ty)| {
            if let TyKind::Data(DataTy::Ref(Provenance::Value(pn), _, _, _)) = &ty.ty {
                if prv_name == pn {
                    if reborrows.iter().any(|reb_pl| reb_pl == place) {
                        true
                    } else {
                        println!("{:?} not in reborrow list", place);
                        false
                    }
                } else {
                    true
                }
            } else {
                true
            }
        });

        at_least_one && all_in_reborrows
    }

    fn overlap(&self, pll: &PlaceExpr, plr: &PlaceExpr) -> bool {
        if pll.prefix_of(plr) || plr.prefix_of(pll) {
            println!(
                "There is an overlap between the borrows {} and {}.",
                pll, plr
            );
            true
        } else {
            false
        }
    }
}
