mod borrow_check;
mod subty_check;

use crate::ast::Ownership;
use crate::ast::*;
use crate::ty::DataTy::Scalar;
use crate::ty::*;
use borrow_check::borrowable;
use subty_check::subty_check;

// ∀ε ∈ Σ. Σ ⊢ ε
// --------------
//      ⊢ Σ

type ErrMsg = String;

pub fn ty_check(mut gl_ctx: GlobalCtx) -> Result<GlobalCtx, ErrMsg> {
    let (typed_gl_ctx, errs): (Vec<_>, Vec<_>) = gl_ctx
        .iter()
        .map(|gl_f| ty_check_global_fun_def(&gl_ctx, gl_f))
        .partition(Result::is_ok);

    if errs.is_empty() {
        Ok(typed_gl_ctx.into_iter().map(Result::unwrap).collect())
    } else {
        Err(errs.into_iter().map(Result::unwrap_err).collect())
    }
}

// Σ ⊢ fn f <List[φ], List[ρ], List[α]> (x1: τ1, ..., xn: τn) → τr where List[ρ1:ρ2] { e }
fn ty_check_global_fun_def(gl_ctx: &GlobalCtx, gf: &GlobalFunDef) -> Result<GlobalFunDef, ErrMsg> {
    let GlobalFunDef {
        name,
        ty_idents,
        params,
        ret_ty,
        exec,
        prv_rels,
        mut body_expr,
        fun_ty,
    } = gf.clone();
    let kind_ctx: KindCtx = KindCtx::new()
        .append_prv_rels(&prv_rels)
        .append_ty_idents(&ty_idents);
    prv_rels_use_declared_idents(&prv_rels, &kind_ctx)?;

    // Build frame typing for this function
    let glf_frame = append_idents_typed(
        &vec![],
        params
            .clone()
            .into_iter()
            .map(|(ident, dty)| (ident, Ty::Data(dty)))
            .collect(),
    );
    let ty_ctx = TypingCtx::from(glf_frame);
    ty_check_expr(gl_ctx, &kind_ctx, &ty_ctx, &mut body_expr)?;

    // t <= t_f
    let empty_ty_ctx = subty_check(
        &kind_ctx,
        &ty_ctx,
        &body_expr.ty.as_ref().unwrap(),
        &Ty::Data(ret_ty.clone()),
    )?;
    assert!(empty_ty_ctx.is_empty(), "This should never happen.");

    Ok(GlobalFunDef {
        name,
        ty_idents,
        params,
        ret_ty,
        exec,
        prv_rels,
        body_expr,
        fun_ty,
    })
}

fn prv_rels_use_declared_idents(
    prv_rels: &Vec<(TyIdent, TyIdent)>,
    kind_ctx: &KindCtx,
) -> Result<(), String> {
    let prv_idents = kind_ctx.get_ty_idents(Kind::Provenance);
    for prv_rel in prv_rels {
        if !prv_idents.contains(&prv_rel.0) {
            return Err(format!("{} is not declared", prv_rel.0));
        }
        if !prv_idents.contains(&prv_rel.1) {
            return Err(format!("{} is not declared", prv_rel.1));
        }
    }
    Ok(())
}

// TODO find out if Gamma is always correct by construction (similarly to Delta), also all 3 combined
// e has type τ under Σ, Δ, and Γ, producing output context Γ
// Σ; Δ; Γ ⊢ e :^exec τ ⇒ Γ′
pub fn ty_check_expr(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: &TypingCtx,
    expr: &mut Expr,
) -> Result<(Ty, TypingCtx), String> {
    match &mut expr.expr {
        // Move or copy depends on type.
        ExprKind::PlaceExpr(pl_expr) if pl_expr.is_place() => {
            borrowable(
                kind_ctx,
                ty_ctx,
                vec![].as_slice(),
                Ownership::Uniq,
                pl_expr,
            )?;
            match ty_ctx.type_place(&pl_expr.to_pl_ctx_and_most_specif_pl().1) {
                // TODO continue!!!
                _ => panic!("todo"),
            }
        }
        // Must be copyable because reference is included in path.
        ExprKind::PlaceExpr(pl_expr) if !pl_expr.is_place() => {
            borrowable(
                kind_ctx,
                ty_ctx,
                vec![].as_slice(),
                Ownership::Shrd,
                pl_expr,
            )?;
            if let Ok(Ty::Data(dty)) =
                ty_check_place_expr_under_own(kind_ctx, ty_ctx, Ownership::Shrd, pl_expr)
            {
                if dty.copyable() {
                    Ok((Ty::Data(dty), ty_ctx.clone()))
                } else {
                    Err(String::from("Data type is not copyable."))
                }
            } else {
                Err(String::from("Place expression does not have correct type."))
            }
        }
        // TODO respect mutability
        ExprKind::Let(mutable, ident, dty, ref mut e1, ref mut e2) => {
            let (ty_e1, ty_ctx_e1) = ty_check_expr(gl_ctx, kind_ctx, ty_ctx, e1)?;
            let ty_ctx_sub = subty_check(kind_ctx, &ty_ctx_e1, &ty_e1, &Ty::Data(dty.clone()))?;
            let ty_ctx_with_ident = ty_ctx_sub.append_ident_typed(IdentTyped {
                ident: ident.clone(),
                ty: Ty::Data(dty.clone()),
            });
            // TODO gc_loans
            // TODO check that x is dead, WHY?! copy types wouldn't be dead?
            //  Yes they would, because the derivation needs to call T-Drop then.
            let (ty_e2, ty_ctx_e2) = ty_check_expr(gl_ctx, kind_ctx, &ty_ctx_with_ident, e2)?;
            Ok((ty_e2, ty_ctx_e2))
        }
        ExprKind::Lit(l) => {
            let scalar_data = match l {
                Lit::Unit => ScalarData::Unit,
                Lit::Bool(_) => ScalarData::Bool,
                Lit::Int(_) => ScalarData::I32,
                Lit::Float(_) => ScalarData::F32,
            };
            Ok((Ty::Data(DataTy::Scalar(scalar_data)), ty_ctx.clone()))
        }
        _ => panic!("Impl missing"),
    }
}

fn ty_check_place_expr_under_own(
    kind_ctx: &KindCtx,
    ty_ctx: &TypingCtx,
    own: Ownership,
    pl_expr: &PlaceExpr,
) -> Result<Ty, String> {
    // TODO implement
    Ok(Ty::Data(DataTy::Scalar(ScalarData::Unit)))
}
