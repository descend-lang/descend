mod borrow_check;
mod subty_check;
pub mod ty_ctx;

use crate::ast::nat::*;
use crate::ast::ty::*;
use crate::ast::Ownership;
use crate::ast::*;
use borrow_check::borrowable;
use subty_check::subty_check;
use ty_ctx::{IdentTyped, TyCtx};

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
        .append_ty_idents(ty_idents.clone());
    prv_rels_use_declared_idents(&prv_rels, &kind_ctx)?;

    // Build frame typing for this function
    let glf_frame = append_idents_typed(&vec![], params.clone());
    let ty_ctx = TyCtx::from(glf_frame);
    ty_check_expr(gl_ctx, &kind_ctx, ty_ctx.clone(), &mut body_expr)?;

    // t <= t_f
    let empty_ty_ctx = subty_check(
        &kind_ctx,
        ty_ctx,
        &body_expr.ty.as_ref().unwrap(),
        &ret_ty.clone(),
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
// TODO think about this: currently every subexpression is annotated with a non-dead type, even if
//  the type is killed in the context.
// e has type τ under Σ, Δ, and Γ, producing output context Γ
// Σ; Δ; Γ ⊢ e :^exec τ ⇒ Γ′
// This never returns a dead type, because typing an expression with a dead type is not possible.
pub fn ty_check_expr(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    expr: &mut Expr,
) -> Result<TyCtx, String> {
    let (res_ty_ctx, ty) = match &mut expr.expr {
        ExprKind::PlaceExpr(pl_expr) if pl_expr.is_place() => {
            ty_check_place_without_deref(kind_ctx, ty_ctx, pl_expr)?
        }
        ExprKind::PlaceExpr(pl_expr) if !pl_expr.is_place() => {
            ty_check_place_with_deref(kind_ctx, ty_ctx, pl_expr)?
        }
        // TODO respect mutability
        ExprKind::Let(mutable, ident, ty, ref mut e1, ref mut e2) => {
            ty_check_let(gl_ctx, kind_ctx, ty_ctx, ident, ty, e1, e2)?
        }
        ExprKind::Lit(l) => ty_check_literal(ty_ctx, l),
        ExprKind::Array(elems) => ty_check_array(gl_ctx, kind_ctx, ty_ctx, elems)?,
        ExprKind::Tuple(elems) => ty_check_tuple(gl_ctx, kind_ctx, ty_ctx, elems)?,
        ExprKind::App(ef, args) => ty_check_app(gl_ctx, kind_ctx, ty_ctx, ef, args)?,
        ExprKind::DepApp(df, kv) => ty_check_dep_app(gl_ctx, kind_ctx, ty_ctx, df, kv)?,
        e => panic!(format!("Impl missing for: {:?}", e)),
    };

    expr.ty = Some(ty);
    Ok(res_ty_ctx)
}

fn ty_check_dep_app(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    df: &mut Expr,
    kv: &mut KindValue,
) -> Result<(TyCtx, Ty), String> {
    match kv {
        KindValue::Provenance(prv) => panic!("todo"),
        KindValue::Data(ty) => {
            let df_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, ty_ctx, df)?;
            if let Ty::DepFn(param, _, _, out_ty) = df.ty.as_ref().unwrap() {
                if param.kind() != Kind::Ty {
                    return Err(String::from("Trying to apply value of different kind."));
                }
                Ok((df_ty_ctx, *out_ty.clone()))
            } else {
                Err(String::from(
                    "The provided dependent function expression does not have a function type.",
                ))
            }
        }
        KindValue::Nat(n) => panic!("todo"),
        KindValue::Memory(mem) => panic!("todo"),
        KindValue::Frame(frm) => panic!("todo"),
    }
}

fn ty_check_app(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    ef: &mut Expr,
    args: &mut [Expr],
) -> Result<(TyCtx, Ty), String> {
    // TODO check well-kinded: FrameTyping, Prv, Ty
    let mut res_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, ty_ctx, ef)?;
    if let Ty::Fn(param_tys, _, _, out_ty) = ef.ty.as_ref().unwrap() {
        for (arg, f_arg_ty) in args.iter_mut().zip(param_tys) {
            res_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, res_ty_ctx, arg)?;
            // No subtyping for Application
            if arg.ty.as_ref().unwrap() != f_arg_ty {
                return Err(String::from("Argument types do not match."));
            }
        }
        Ok((res_ty_ctx, *out_ty.clone()))
    } else {
        Err(String::from(
            "The provided function expression does not have a function type.",
        ))
    }
}

fn ty_check_tuple(
    gl_ctx: &Vec<GlobalFunDef>,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    elems: &mut [Expr],
) -> Result<(TyCtx, Ty), String> {
    let mut tmp_ty_ctx = ty_ctx;
    for elem in elems.iter_mut() {
        tmp_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, tmp_ty_ctx, elem)?;
    }
    let elem_tys: Vec<_> = elems.iter().map(|elem| elem.ty.clone().unwrap()).collect();
    Ok((tmp_ty_ctx, Ty::Tuple(elem_tys)))
}

fn ty_check_array(
    gl_ctx: &Vec<GlobalFunDef>,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    elems: &mut Vec<Expr>,
) -> Result<(TyCtx, Ty), String> {
    assert!(!elems.is_empty());
    let mut tmp_ty_ctx = ty_ctx;
    for elem in elems.iter_mut() {
        tmp_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, tmp_ty_ctx, elem)?;
    }
    let ty = elems.first().unwrap().ty.clone();
    if elems.iter().any(|elem| ty != elem.ty) {
        Err(String::from(
            "Not all provided elements have the same type.",
        ))
    } else {
        Ok((
            tmp_ty_ctx,
            Ty::Array(Nat::Lit(elems.len()), Box::new(ty.unwrap())),
        ))
    }
}

fn ty_check_literal(ty_ctx: TyCtx, l: &mut Lit) -> (TyCtx, Ty) {
    let scalar_data = match l {
        Lit::Unit => ScalarData::Unit,
        Lit::Bool(_) => ScalarData::Bool,
        Lit::Int(_) => ScalarData::I32,
        Lit::Float(_) => ScalarData::F32,
    };
    (ty_ctx, Ty::Scalar(scalar_data))
}

fn ty_check_let(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    ident: &mut Ident,
    ty: &Ty,
    e1: &mut Expr,
    e2: &mut Expr,
) -> Result<(TyCtx, Ty), String> {
    let ty_ctx_e1 = ty_check_expr(gl_ctx, kind_ctx, ty_ctx, e1)?;
    let ty_ctx_sub = subty_check(kind_ctx, ty_ctx_e1, &e1.ty.as_ref().unwrap(), ty)?;
    let ident_with_annotated_ty = IdentTyped::new(ident.clone(), ty.clone());
    let ty_ctx_with_ident = ty_ctx_sub.append_ident_typed(ident_with_annotated_ty);
    // TODO gc_loans
    // TODO check that x is dead,
    //  the derivation needs to call T-Drop in case of copy types then.
    //  Equivalent to saying that the variable must be used.
    let ty_ctx_e2 = ty_check_expr(gl_ctx, kind_ctx, ty_ctx_with_ident, e2)?;
    Ok((ty_ctx_e2, e2.ty.as_ref().unwrap().clone()))
}

fn ty_check_place_with_deref(
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    pl_expr: &PlaceExpr,
) -> Result<(TyCtx, Ty), String> {
    let own = Ownership::Shrd;
    borrowable(kind_ctx, &ty_ctx, vec![].as_slice(), own, pl_expr)?;
    if let Ok(ty) = ty_check_place_expr_under_own(kind_ctx, &ty_ctx, Ownership::Shrd, pl_expr) {
        if !ty.is_fully_alive() {
            return Err(String::from("Place was moved before."));
        }
        if ty.copyable() {
            Ok((ty_ctx, ty))
        } else {
            Err(String::from("Data type is not copyable."))
        }
    } else {
        Err(String::from("Place expression does not have correct type."))
    }
}

fn ty_check_place_without_deref(
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    pl_expr: &PlaceExpr,
) -> Result<(TyCtx, Ty), String> {
    let place = pl_expr.to_place().unwrap();
    // TODO reintroduce Dead Type syntax for Frame Entries and return type of type_place.
    let pl_ty = ty_ctx.type_place(&place)?;
    if !pl_ty.is_fully_alive() {
        return Err(String::from("Place was moved before."));
    }
    let res_ty_ctx = if pl_ty.copyable() {
        borrowable(
            kind_ctx,
            &ty_ctx,
            vec![].as_slice(),
            Ownership::Shrd,
            pl_expr,
        )?;
        // TODO check whether the shared type checking of a place expr will be needed
        ty_ctx
    } else {
        borrowable(
            kind_ctx,
            &ty_ctx,
            vec![].as_slice(),
            Ownership::Uniq,
            pl_expr,
        )?;
        ty_ctx.kill_place(&place)
    };
    Ok((res_ty_ctx, pl_ty.clone()))
}

fn ty_check_place_expr_under_own(
    kind_ctx: &KindCtx,
    ty_ctx: &TyCtx,
    own: Ownership,
    pl_expr: &PlaceExpr,
    // TODO return reference to type
) -> Result<Ty, String> {
    // TODO implement
    Ok(Ty::Scalar(ScalarData::Unit))
}
