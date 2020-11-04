mod borrow_check;
mod subty_check;
pub mod ty_ctx;

use crate::ast::nat::*;
use crate::ast::ty::*;
use crate::ast::Ownership;
use crate::ast::*;
use crate::ty_check::subty_check::multiple_outlives;
use borrow_check::ownership_safe;
use std::ops::Deref;
use subty_check::subty_check;
use ty_ctx::{IdentTyped, TyCtx};

// ∀ε ∈ Σ. Σ ⊢ ε
// --------------
//      ⊢ Σ

type ErrMsg = String;

pub fn ty_check(gl_ctx: &mut GlobalCtx) -> Result<(), ErrMsg> {
    let gl_ctx_copy_for_fun_defs = gl_ctx.clone();
    let errs = gl_ctx
        .fun_defs_mut()
        .fold(
            Vec::<ErrMsg>::new(),
            |mut err_msgs, gl_f| match ty_check_global_fun_def(&gl_ctx_copy_for_fun_defs, gl_f) {
                Ok(()) => err_msgs,
                Err(msg) => {
                    err_msgs.push(msg);
                    err_msgs
                }
            },
        );

    if errs.is_empty() {
        Ok(())
    } else {
        Err(errs.into_iter().collect::<String>())
    }
}

// Σ ⊢ fn f <List[φ], List[ρ], List[α]> (x1: τ1, ..., xn: τn) → τr where List[ρ1:ρ2] { e }
fn ty_check_global_fun_def(gl_ctx: &GlobalCtx, gf: &mut GlobalFunDef) -> Result<(), ErrMsg> {
    let kind_ctx = KindCtx::from(gf.ty_idents.clone(), gf.prv_rels.clone())?;

    // Build frame typing for this function
    let glf_frame = append_idents_typed(&vec![], gf.params.clone());
    let ty_ctx = TyCtx::from(glf_frame);

    ty_check_expr(gl_ctx, &kind_ctx, ty_ctx.clone(), &mut gf.body_expr)?;

    // t <= t_f
    let empty_ty_ctx = subty_check(
        &kind_ctx,
        TyCtx::new(),
        gf.body_expr.ty.as_ref().unwrap(),
        &gf.ret_ty,
    )?;
    //TODO why is this the case?
    assert!(
        empty_ty_ctx.is_empty(),
        format!(
            "Expected typing context to be empty. But TyCtx:\n {:?}",
            empty_ty_ctx
        )
    );

    Ok(())
    // TODO IMPORTANT write function that computes the function type for a global fun
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
        ExprKind::GlobalFunIdent(name) => (ty_ctx, gl_ctx.fun_ty_by_name(name)?.clone()),
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
        ExprKind::Seq(e1, e2) => ty_check_seq(gl_ctx, kind_ctx, ty_ctx, e1, e2)?,
        ExprKind::Lit(l) => ty_check_literal(ty_ctx, l),
        ExprKind::Array(elems) => ty_check_array(gl_ctx, kind_ctx, ty_ctx, elems)?,
        ExprKind::Tuple(elems) => ty_check_tuple(gl_ctx, kind_ctx, ty_ctx, elems)?,
        ExprKind::App(ef, args) => ty_check_app(gl_ctx, kind_ctx, ty_ctx, ef, args)?,
        ExprKind::DepApp(df, kv) => ty_check_dep_app(gl_ctx, kind_ctx, ty_ctx, df, kv)?,
        ExprKind::Ref(Provenance::Value(prv_val_name), own, pl_expr) => {
            ty_check_ref(gl_ctx, kind_ctx, ty_ctx, prv_val_name, *own, pl_expr)?
        }
        ExprKind::Binary(bin_op, lhs, rhs) => {
            ty_check_binary_op(gl_ctx, kind_ctx, ty_ctx, bin_op, lhs, rhs)?
        }
        e => panic!(format!("Impl missing for: {:?}", e)),
    };

    expr.ty = Some(ty);
    Ok(res_ty_ctx)
}

fn ty_check_binary_op(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    bin_op: &BinOp,
    lhs: &mut Expr,
    rhs: &mut Expr,
) -> Result<(TyCtx, Ty), String> {
    let lhs_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, ty_ctx, lhs)?;
    let rhs_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, lhs_ty_ctx, rhs)?;

    let lhs_ty = lhs.ty.as_ref().unwrap();
    let rhs_ty = rhs.ty.as_ref().unwrap();
    match (lhs_ty, rhs_ty) {
        (Ty::Scalar(ScalarData::F32), Ty::Scalar(ScalarData::F32))
        | (Ty::Scalar(ScalarData::I32), Ty::Scalar(ScalarData::I32)) => {
            Ok((rhs_ty_ctx, lhs_ty.clone()))
        }
        _ => Err(format!(
            "Expected the same number types for operator {}, instead got\n Lhs: {:?}\n Rhs: {:?}",
            bin_op, lhs, rhs
        )),
    }
}

// TODO bring functions in order of the pattern matching
fn ty_check_dep_app(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    df: &mut Expr,
    kv: &mut KindValue,
) -> Result<(TyCtx, Ty), String> {
    match kv {
        KindValue::Provenance(prv) => unimplemented!(),
        KindValue::Data(ty) => {
            let df_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, ty_ctx, df)?;
            if let Ty::DepFn(param, _, _, out_ty) = df.ty.as_ref().unwrap() {
                if param.kind() != Kind::Ty {
                    return Err("Trying to apply value of different kind.".to_string());
                }
                Ok((df_ty_ctx, *out_ty.clone()))
            } else {
                Err(
                    "The provided dependent function expression does not have a function type."
                        .to_string(),
                )
            }
        }
        KindValue::Nat(n) => unimplemented!(),
        KindValue::Memory(mem) => unimplemented!(),
        KindValue::Frame(frm) => unimplemented!(),
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
            if arg.ty.as_ref().unwrap() != f_arg_ty {
                return Err(String::from("Argument types do not match."));
            }
        }
        Ok((res_ty_ctx, *out_ty.clone()))
    } else {
        Err("The provided function expression does not have a function type.".to_string())
    }
}

fn ty_check_tuple(
    gl_ctx: &GlobalCtx,
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
    gl_ctx: &GlobalCtx,
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
        Err("Not all provided elements have the same type.".to_string())
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
    let garbage_coll_ty_ctx_with_ident = ty_ctx_sub
        .append_ident_typed(ident_with_annotated_ty)
        .garbage_collect_loans();
    // TODO gc_loans
    // TODO check that x is dead,
    //  the derivation needs to call T-Drop in case of copy types then.
    //  Equivalent to saying that the variable must be used.
    let ty_ctx_e2 = ty_check_expr(gl_ctx, kind_ctx, garbage_coll_ty_ctx_with_ident, e2)?;
    Ok((ty_ctx_e2, e2.ty.as_ref().unwrap().clone()))
}

fn ty_check_seq(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    e1: &mut Expr,
    e2: &mut Expr,
) -> Result<(TyCtx, Ty), String> {
    let ty_ctx_e1 = ty_check_expr(gl_ctx, kind_ctx, ty_ctx, e1)?;
    let ty_ctx_e2 = ty_check_expr(gl_ctx, kind_ctx, ty_ctx_e1.garbage_collect_loans(), e2)?;
    Ok((ty_ctx_e2, e2.ty.as_ref().unwrap().clone()))
}

fn ty_check_place_with_deref(
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    pl_expr: &PlaceExpr,
) -> Result<(TyCtx, Ty), String> {
    let own = Ownership::Shrd;
    ownership_safe(kind_ctx, &ty_ctx, vec![].as_slice(), own, pl_expr)?;
    if let Ok(ty) = place_expr_ty_under_own(kind_ctx, &ty_ctx, Ownership::Shrd, pl_expr) {
        if !ty.is_fully_alive() {
            return Err("Place was moved before.".to_string());
        }
        if ty.copyable() {
            // this line is a trick to release a life time that is connected to ty_ctx
            let ty = ty.clone();
            Ok((ty_ctx, ty))
        } else {
            Err("Data type is not copyable.".to_string())
        }
    } else {
        Err("Place expression does not have correct type.".to_string())
    }
}

fn ty_check_place_without_deref(
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    pl_expr: &PlaceExpr,
) -> Result<(TyCtx, Ty), String> {
    let place = pl_expr.to_place().unwrap();
    // TODO think about:
    //  reintroduce Dead Type syntax for Frame Entries and return type of type_place.
    let pl_ty = ty_ctx.place_ty(&place)?;
    if !pl_ty.is_fully_alive() {
        return Err("Place was moved before.".to_string());
    }
    let res_ty_ctx = if pl_ty.copyable() {
        ownership_safe(
            kind_ctx,
            &ty_ctx,
            vec![].as_slice(),
            Ownership::Shrd,
            pl_expr,
        )?;
        // TODO check whether the shared type checking of a place expr will be needed
        ty_ctx
    } else {
        ownership_safe(
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

fn ty_check_ref(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    prv_val_name: &str,
    own: Ownership,
    pl_expr: &mut PlaceExpr,
) -> Result<(TyCtx, Ty), String> {
    if !ty_ctx.loans_for_prv(prv_val_name)?.is_empty() {
        return Err(
            "Trying to borrow with a provenance that is used in a different borrow.".to_string(),
        );
    }
    let loans = ownership_safe(kind_ctx, &ty_ctx, vec![].as_slice(), own, pl_expr)?;
    let ty = place_expr_ty_under_own(kind_ctx, &ty_ctx, own, pl_expr)?;
    if !ty.is_fully_alive() {
        return Err("The place was at least partially moved before.".to_string());
    }
    let (reffed_ty, mem) = match &ty {
        Ty::Dead(_) => panic!("Cannot happen because of the alive check."),
        Ty::At(inner_ty, m) => (inner_ty.deref().clone(), m.clone()),
        _ => (ty.clone(), Memory::CpuStack),
    };
    let res_ty = Ty::Ref(
        Provenance::Value(prv_val_name.to_string()),
        own,
        mem,
        Box::new(reffed_ty),
    );
    let res_ty_ctx = ty_ctx.extend_loans_for_prv(prv_val_name, loans)?;
    Ok((res_ty_ctx, res_ty))
}

// Δ; Γ ⊢ω p:τ
// p in an ω context has type τ under Δ and Γ
fn place_expr_ty_under_own<'a>(
    kind_ctx: &KindCtx,
    ty_ctx: &'a TyCtx,
    own: Ownership,
    pl_expr: &PlaceExpr,
) -> Result<&'a Ty, String> {
    let (ty, _) = place_expr_ty_and_passed_prvs_under_own(kind_ctx, ty_ctx, own, pl_expr)?;
    Ok(ty)
}

// Δ; Γ ⊢ω p:τ,{ρ}
// p in an ω context has type τ under Δ and Γ, passing through provenances in Vec<ρ>
fn place_expr_ty_and_passed_prvs_under_own<'a>(
    kind_ctx: &KindCtx,
    ty_ctx: &'a TyCtx,
    own: Ownership,
    pl_expr: &PlaceExpr,
) -> Result<(&'a Ty, Vec<&'a Provenance>), String> {
    match pl_expr {
        // TC-Var
        PlaceExpr::Var(ident) => var_expr_ty_and_empyt_prvs_under_own(ty_ctx, &ident),
        // TC-Proj
        PlaceExpr::Proj(tuple_expr, n) => {
            proj_expr_ty_and_passed_prvs_under_own(kind_ctx, ty_ctx, own, tuple_expr, n)
        }
        // TC-Deref
        // TODO respect memory
        PlaceExpr::Deref(ref_expr) => {
            deref_expr_ty_and_passed_prvs_under_own(kind_ctx, ty_ctx, own, ref_expr)
        }
    }
}

fn var_expr_ty_and_empyt_prvs_under_own<'a>(
    ty_ctx: &'a TyCtx,
    ident: &Ident,
) -> Result<(&'a Ty, Vec<&'a Provenance>), String> {
    let ty = ty_ctx.ident_ty(&ident)?;
    if !ty.is_fully_alive() {
        return Err("The value in this identifier has been moved out.".to_string());
    }
    Ok((ty, vec![]))
}

fn proj_expr_ty_and_passed_prvs_under_own<'a>(
    kind_ctx: &KindCtx,
    ty_ctx: &'a TyCtx,
    own: Ownership,
    tuple_expr: &PlaceExpr,
    n: &Nat,
) -> Result<(&'a Ty, Vec<&'a Provenance>), String> {
    let (pl_expr_ty, passed_prvs) =
        place_expr_ty_and_passed_prvs_under_own(kind_ctx, ty_ctx, own, tuple_expr)?;
    if let Ty::Tuple(elem_tys) = pl_expr_ty {
        if let Some(ty) = elem_tys.get(n.eval()) {
            Ok((ty, passed_prvs))
        } else {
            Err("Trying to access non existing tuple element.".to_string())
        }
    } else {
        Err("Trying to project from a non tuple type.".to_string())
    }
}

fn deref_expr_ty_and_passed_prvs_under_own<'a>(
    kind_ctx: &KindCtx,
    ty_ctx: &'a TyCtx,
    own: Ownership,
    ref_expr: &PlaceExpr,
) -> Result<(&'a Ty, Vec<&'a Provenance>), String> {
    let (pl_expr_ty, mut passed_prvs) =
        place_expr_ty_and_passed_prvs_under_own(kind_ctx, ty_ctx, own, ref_expr)?;
    if let Ty::Ref(prv, ref_own, mem, ty) = pl_expr_ty {
        if ref_own <= &own {
            return Err("Trying to dereference and mutably use a shrd reference.".to_string());
        }
        let outl_rels = passed_prvs.iter().map(|&passed_prv| (prv, passed_prv));
        multiple_outlives(kind_ctx, ty_ctx.clone(), outl_rels)?;
        passed_prvs.push(prv);
        Ok((ty, passed_prvs))
    } else {
        Err("Trying to dereference non reference type.".to_string())
    }
}
