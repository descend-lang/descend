mod borrow_check;
mod subty_check;

use crate::ast::Ownership;
use crate::ast::*;
use crate::nat::*;
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
        ExprKind::PlaceExpr(pl_expr) if pl_expr.is_place() => {
            let place = pl_expr.to_place().unwrap();
            let pl_ty = ty_ctx.type_place(&place)?;
            if let Ty::Data(pl_dty) = pl_ty {
                let (own, new_ty_ctx) = if pl_dty.copyable() {
                    // TODO check whether the shared type checking of a place expr will be needed
                    (Ownership::Shrd, ty_ctx.clone())
                } else {
                    (Ownership::Uniq, ty_ctx.kill_place(&place, &pl_dty))
                };
                borrowable(kind_ctx, ty_ctx, vec![].as_slice(), own, pl_expr)?;
                Ok((Ty::Data(pl_dty), new_ty_ctx))
            } else {
                Err(String::from("This place has been moved out before."))
            }
        }
        ExprKind::PlaceExpr(pl_expr) if !pl_expr.is_place() => {
            let own = Ownership::Shrd;
            borrowable(kind_ctx, ty_ctx, vec![].as_slice(), own, pl_expr)?;
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
            let ident_with_annotated_ty = IdentTyped::new(ident.clone(), Ty::Data(dty.clone()));
            let ty_ctx_with_ident = ty_ctx_sub.append_ident_typed(ident_with_annotated_ty);
            // TODO gc_loans
            // TODO check that x is dead,
            //  the derivation needs to call T-Drop in case of copy types then.
            //  Equivalent to saying that the variable must be used.
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
        ExprKind::Array(elems) => {
            assert!(elems.len() > 0);
            let mut tmp_ty_ctx = ty_ctx.clone();
            let mut elem_tys = vec![];
            for elem in elems {
                let (elem_ty, res_ty_ctx) = ty_check_expr(gl_ctx, kind_ctx, &tmp_ty_ctx, elem)?;
                tmp_ty_ctx = res_ty_ctx;
                elem_tys.push(elem_ty);
            }
            if let Ty::Data(arr_elem_dty) = elem_tys[0].clone() {
                if elem_tys.iter().any(|elem_ty| &elem_tys[0] != elem_ty) {
                    Err(String::from(
                        "Not all provided elements have the same type.",
                    ))
                } else {
                    Ok((
                        Ty::Data(DataTy::Array(
                            Nat::Lit(elem_tys.len()),
                            Box::new(arr_elem_dty),
                        )),
                        tmp_ty_ctx,
                    ))
                }
            } else {
                panic!("Array elements marked as dead")
            }
        }
        ExprKind::Tuple(elems) => {
            let mut tmp_ty_ctx = ty_ctx.clone();
            let mut elem_dtys = vec![];
            for elem in elems {
                if let (Ty::Data(elem_dty), res_ty_ctx) =
                    ty_check_expr(gl_ctx, kind_ctx, &tmp_ty_ctx, elem)?
                {
                    tmp_ty_ctx = res_ty_ctx;
                    elem_dtys.push(elem_dty);
                } else {
                    panic!("Unexpected.")
                }
            }
            Ok((Ty::Data(DataTy::Tuple(elem_dtys)), tmp_ty_ctx))
        }
        ExprKind::App(f, args) => {
            if let (Ty::Data(DataTy::Fn(param_dtys, _, _, out_dty)), f_ty_ctx) =
                ty_check_expr(gl_ctx, kind_ctx, ty_ctx, f)?
            {
                let mut tmp_ty_ctx = f_ty_ctx.clone();
                let mut arg_dtys = vec![];
                for (arg, f_arg_dty) in args.iter_mut().zip(param_dtys) {
                    if let (Ty::Data(arg_dty), args_ty_ctx) =
                        ty_check_expr(gl_ctx, kind_ctx, ty_ctx, arg)?
                    {
                        if arg_dty != f_arg_dty {
                            return Err(String::from("Argument types do not match."));
                        }
                        arg_dtys.push(arg_dty);
                        tmp_ty_ctx = args_ty_ctx;
                    } else {
                        panic!("Unexpected.")
                    }
                }
                Ok((Ty::Data(*out_dty), tmp_ty_ctx))
            } else {
                Err(String::from(
                    "The provided function expression does not have a function type.",
                ))
            }
        }
        ExprKind::DepApp(df, kv) => {
            match kv {
                KindValue::Provenance(prv) => panic!("todo"),
                KindValue::Data(dty) => {
                    // Check that kv is well kinded.
                    if let (Ty::Data(DataTy::GenFn(param, _, _, out_dty)), df_ty_ctx) =
                        ty_check_expr(gl_ctx, kind_ctx, ty_ctx, df)?
                    {
                        if param.kind != Kind::Data {
                            return Err(String::from("Trying to apply value of different kind."));
                        }
                        Ok((Ty::Data(*out_dty), df_ty_ctx))
                    } else {
                        panic!("Unexpected.")
                    }
                }
                KindValue::Nat(n) => panic!("todo"),
                KindValue::Memory(mem) => panic!("todo"),
                KindValue::Frame(frm) => panic!("todo"),
            }
        }
        e => panic!(format!("Impl missing for: {:?}", e)),
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
