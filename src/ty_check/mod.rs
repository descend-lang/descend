mod borrow_check;
// TODO remove pub from pub mod ctxs, only public because of basi_syntax tests
pub mod ctxs;
pub mod pre_decl;
mod subty;

use crate::ast::internal::{IdentTyped, Loan, PrvMapping};
use crate::ast::*;
use ctxs::{GlobalCtx, KindCtx, TyCtx};
use std::ops::Deref;

// ∀ε ∈ Σ. Σ ⊢ ε
// --------------
//      ⊢ Σ
pub fn ty_check(compil_unit: &mut CompilUnit) -> Result<(), String> {
    ty_check_with_pre_decl_funs(compil_unit, &pre_decl::fun_decls())
}

pub fn ty_check_with_pre_decl_funs(
    compil_unit: &mut CompilUnit,
    pre_decl_funs: &[(&str, DataTy)],
) -> Result<(), String> {
    let gl_ctx = GlobalCtx::new()
        .append_from_gl_fun_defs(compil_unit)
        .append_fun_decls(pre_decl_funs);
    let errs = compil_unit
        .iter_mut()
        .fold(
            Vec::<String>::new(),
            |mut err_msgs, fun| match ty_check_global_fun_def(&gl_ctx, fun) {
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
fn ty_check_global_fun_def(gl_ctx: &GlobalCtx, gf: &mut GlobalFunDef) -> Result<(), String> {
    let kind_ctx = KindCtx::from(gf.generic_params.clone(), gf.prv_rels.clone())?;

    // Build frame typing for this function
    let glf_frame = internal::append_idents_typed(
        &vec![],
        gf.params
            .iter()
            .map(|ParamDecl { ident, dty, .. }| IdentTyped {
                ident: ident.clone(),
                ty: Ty::Data(dty.clone()),
            })
            .collect(),
    );
    let ty_ctx = TyCtx::from(glf_frame);

    ty_check_expr(gl_ctx, &kind_ctx, ty_ctx, gf.exec, &mut gf.body_expr)?;

    // t <= t_f
    let empty_ty_ctx = subty::check(
        &kind_ctx,
        TyCtx::new(),
        gf.body_expr.ty.as_ref().unwrap().dty(),
        &gf.ret_dty,
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
}

// TODO find out if Gamma is always correct by construction (similarly to Delta), also all 3 combined
// e has type τ under Σ, Δ, and Γ, producing output context Γ'
// sideconditions: Global Function Context Σ, Kinding context Δ and typing context are well-formed and
//   type τ is well-formed under well-formed GlFunCtxt, kinding ctx, output context Γ'.
// Σ; Δ; Γ ⊢ e :^exec τ ⇒ Γ′, side conditions:  ⊢ Σ;Δ;Γ and Σ;Δ;Γ′ ⊢ τ
// This never returns a dead type, because typing an expression with a dead type is not possible.
fn ty_check_expr(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: ExecLoc,
    expr: &mut Expr,
) -> Result<TyCtx, String> {
    // TODO input contexts are well-formed
    //   well_formed_ctxs(gl_ctx, kind_ctx, &ty_ctx);
    let (res_ty_ctx, ty) = match &mut expr.expr {
        ExprKind::GlobalFunIdent(ident) => (
            ty_ctx,
            Ty::Data(gl_ctx.fun_ty_by_name(&ident.name)?.clone()),
        ),
        ExprKind::PlaceExpr(pl_expr) if pl_expr.is_place() => {
            ty_check_pl_expr_without_deref(kind_ctx, ty_ctx, exec, pl_expr)?
        }
        ExprKind::PlaceExpr(pl_expr) if !pl_expr.is_place() => {
            ty_check_pl_expr_with_deref(kind_ctx, ty_ctx, exec, pl_expr)?
        }
        ExprKind::LetProv(prvs, body) => {
            ty_check_letprov(gl_ctx, kind_ctx, ty_ctx, exec, prvs, body)?
        }
        // TODO respect mutability
        ExprKind::Let(mutable, ident, ty, ref mut e1, ref mut e2) => {
            ty_check_let(gl_ctx, kind_ctx, ty_ctx, exec, ident, ty, e1, e2)?
        }
        ExprKind::Seq(e1, e2) => ty_check_seq(gl_ctx, kind_ctx, ty_ctx, exec, e1, e2)?,
        ExprKind::Lit(l) => ty_check_literal(ty_ctx, l),
        ExprKind::Array(elems) => ty_check_array(gl_ctx, kind_ctx, ty_ctx, exec, elems)?,
        ExprKind::Tuple(elems) => ty_check_tuple(gl_ctx, kind_ctx, ty_ctx, exec, elems)?,
        ExprKind::App(ef, k_args, args) => {
            ty_check_app(gl_ctx, kind_ctx, ty_ctx, exec, ef, k_args, args)?
        }
        ExprKind::Ref(Provenance::Value(prv_val_name), own, pl_expr) => {
            ty_check_borrow(gl_ctx, kind_ctx, ty_ctx, exec, prv_val_name, *own, pl_expr)?
        }
        ExprKind::BinOp(bin_op, lhs, rhs) => {
            ty_check_binary_op(gl_ctx, kind_ctx, ty_ctx, exec, bin_op, lhs, rhs)?
        }
        ExprKind::Index(pl_expr, index) => {
            ty_check_index_copy(gl_ctx, kind_ctx, ty_ctx, exec, pl_expr, index)?
        }
        ExprKind::Assign(pl_expr, e) if pl_expr.is_place() => {
            ty_check_assign_place(gl_ctx, kind_ctx, ty_ctx, exec, pl_expr, e)?
        }
        ExprKind::Assign(pl_expr, e) if !pl_expr.is_place() => {
            ty_check_assign_deref(gl_ctx, kind_ctx, ty_ctx, exec, pl_expr, e)?
        }
        ExprKind::ParForSync(id, view_expr, parall_cfg, body) => ty_check_par_for_sync(
            gl_ctx, kind_ctx, ty_ctx, exec, id, view_expr, parall_cfg, body,
        )?,
        e => panic!(format!("Impl missing for: {:?}", e)),
    };

    // TODO type well formed under output contexts
    expr.ty = Some(ty);
    Ok(res_ty_ctx)
}

fn ty_check_par_for_sync(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: ExecLoc,
    ident: &Ident,
    view: &mut Expr,
    parall_cfg: &mut Expr,
    body: &mut Expr,
) -> Result<(TyCtx, Ty), String> {
    let view_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, ty_ctx, exec, view)?;
    if !matches!(view.ty, Some(Ty::View(ViewTy::Array(_, _)))) {
        return Err(format!(
            "Expected an expression of type ArrayView, found an expression of type {:?} instead.",
            view.ty
        ));
    }

    let parall_cfg_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, view_ty_ctx, exec, parall_cfg)?;
    if !matches!(parall_cfg.ty, Some(Ty::Data(DataTy::GridConfig(_, _)))) {
        return Err(format!(
            "Expected an expression of type GridConfig, found an expression of type {:?} instead.",
            parall_cfg.ty
        ));
    }

    if let (Ty::View(ViewTy::Array(elem_ty, m)), Ty::Data(DataTy::GridConfig(nb, nt))) =
        (view.ty.as_ref().unwrap(), parall_cfg.ty.as_ref().unwrap())
    {
        // TODO
        // if m != Nat::BinOp(BinOpNat::Mul, nb, nt) {
        //     return Err(
        //         "The amount of started threads is not equal to the amount of elements passed to the function."
        //             .to_string());
        // }
        println!(
            "Warning: Did not check equality of {} and {}",
            m,
            Nat::BinOp(BinOpNat::Mul, Box::new(nb.clone()), Box::new(nt.clone()))
        );

        // Use a new context to disable capturing variables.
        // In the long run, capturing places of copy data types and allowing shared borrowing
        // should probably be the goal.
        // TODO Danger this allows capturing of any values
        //  really needed: Keep prvonance mappings, identifiers with copyable types
        //  (maybe even non-copyable and therefore everything again in order to allow
        //  shared borrowing inside).
        let ctx_with_ident = parall_cfg_ty_ctx
            .clone()
            .append_ident_typed(IdentTyped::new(ident.clone(), elem_ty.deref().clone()));
        // TODO check that type of the identifier is dead? Meaning that it has been used in the loop.
        ty_check_expr(gl_ctx, kind_ctx, ctx_with_ident, ExecLoc::GpuThread, body)?;
        Ok((parall_cfg_ty_ctx, Ty::Data(DataTy::Scalar(ScalarTy::Unit))))
    } else {
        panic!("unreachable")
    }
}

fn ty_check_letprov(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: ExecLoc,
    prvs: &[String],
    body: &mut Expr,
) -> Result<(TyCtx, Ty), String> {
    let mut ty_ctx_with_prvs = ty_ctx;
    for prv in prvs {
        ty_ctx_with_prvs = ty_ctx_with_prvs.append_prv_mapping(PrvMapping {
            prv: prv.clone(),
            loans: std::collections::HashSet::new(),
        })
    }
    // TODO do we have to check that the prvs in res_ty_ctx have loans now?
    let res_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, ty_ctx_with_prvs, exec, body)?;
    Ok((res_ty_ctx, body.ty.as_ref().unwrap().clone()))
}

fn ty_check_assign_place(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: ExecLoc,
    pl_expr: &mut PlaceExpr,
    e: &mut Expr,
) -> Result<(TyCtx, Ty), String> {
    let assigned_val_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, ty_ctx, exec, e)?;
    let place = pl_expr.to_place().unwrap();
    let place_ty = assigned_val_ty_ctx.place_ty(&place)?;

    if matches!(place_ty, Ty::View(_)) {
        return Err(format!(
            "Assigning views is forbidden. Trying to assign view {:?}",
            e
        ));
    }

    // If the place is not dead, check that it is safe to use, otherwise it is safe to use anyway.
    if !matches!(place_ty, Ty::Data(DataTy::Dead(_))) {
        let pl_uniq_loans = borrow_check::ownership_safe(
            kind_ctx,
            &assigned_val_ty_ctx,
            &[],
            Ownership::Uniq,
            pl_expr,
        )?;
        // This block of code asserts that nothing unexpected happens.
        // May not necessarily be needed.
        assert_eq!(pl_uniq_loans.len(), 1);
        let place_loan = Loan {
            place_expr: pl_expr.clone(),
            own: Ownership::Uniq,
        };
        matches!(pl_uniq_loans.get(&place_loan), Some(_));
    }

    let after_subty_ctx = subty::check(
        kind_ctx,
        assigned_val_ty_ctx,
        e.ty.as_ref().unwrap().dty(),
        &place_ty.dty(),
    )?;
    let adjust_place_ty_ctx = after_subty_ctx.set_place_ty(&place, e.ty.as_ref().unwrap().clone());
    Ok((
        adjust_place_ty_ctx.without_reborrow_loans(pl_expr),
        Ty::Data(DataTy::Scalar(ScalarTy::Unit)),
    ))
}

fn ty_check_assign_deref(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: ExecLoc,
    deref_expr: &mut PlaceExpr,
    e: &mut Expr,
) -> Result<(TyCtx, Ty), String> {
    let assigned_val_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, ty_ctx, exec, e)?;
    let deref_ty =
        place_expr_ty_under_own(kind_ctx, &assigned_val_ty_ctx, Ownership::Uniq, deref_expr)?
            .clone();

    if !deref_ty.is_fully_alive() {
        return Err(
            "Trying to assign through reference, to a type which is not fully alive.".to_string(),
        );
    }

    borrow_check::ownership_safe(
        kind_ctx,
        &assigned_val_ty_ctx,
        &[],
        Ownership::Uniq,
        deref_expr,
    )?;

    let after_subty_ctx = subty::check(
        kind_ctx,
        assigned_val_ty_ctx,
        e.ty.as_ref().unwrap().dty(),
        &deref_ty,
    )?;
    Ok((
        after_subty_ctx.without_reborrow_loans(deref_expr),
        Ty::Data(DataTy::Scalar(ScalarTy::Unit)),
    ))
}

fn ty_check_index_copy(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: ExecLoc,
    pl_expr: &mut PlaceExpr,
    index: &mut Nat,
) -> Result<(TyCtx, Ty), String> {
    borrow_check::ownership_safe(kind_ctx, &ty_ctx, &[], Ownership::Shrd, pl_expr)?;
    let pl_expr_ty = place_expr_ty_under_own(kind_ctx, &ty_ctx, Ownership::Shrd, pl_expr)?;
    let elem_ty = match pl_expr_ty {
        DataTy::Array(elem_ty, n) => elem_ty,
        DataTy::At(arr_ty, _) => {
            if let DataTy::Array(elem_ty, n) = arr_ty.as_ref() {
                elem_ty
            } else {
                return Err("Trying to index into non array type.".to_string());
            }
        }
        _ => return Err("Trying to index into non array type.".to_string()),
    };
    // TODO check that index is smaller than n here!?
    if elem_ty.copyable() {
        let res_ty = *elem_ty.clone();
        Ok((ty_ctx, Ty::Data(res_ty)))
    } else {
        Err("Cannot move out of array type.".to_string())
    }
}

fn ty_check_binary_op(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: ExecLoc,
    bin_op: &BinOp,
    lhs: &mut Expr,
    rhs: &mut Expr,
) -> Result<(TyCtx, Ty), String> {
    let lhs_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, ty_ctx, exec, lhs)?;
    let rhs_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, lhs_ty_ctx, exec, rhs)?;

    let lhs_ty = lhs.ty.as_ref().unwrap();
    let rhs_ty = rhs.ty.as_ref().unwrap();
    match (lhs_ty, rhs_ty) {
        (Ty::Data(DataTy::Scalar(ScalarTy::F32)), Ty::Data(DataTy::Scalar(ScalarTy::F32)))
        | (Ty::Data(DataTy::Scalar(ScalarTy::I32)), Ty::Data(DataTy::Scalar(ScalarTy::I32))) => {
            Ok((rhs_ty_ctx, lhs_ty.clone()))
        }
        _ => Err(format!(
            "Expected the same number types for operator {}, instead got\n Lhs: {:?}\n Rhs: {:?}",
            bin_op, lhs, rhs
        )),
    }
}

fn ty_check_app(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: ExecLoc,
    ef: &mut Expr,
    k_args: &mut [ArgKinded],
    args: &mut [Expr],
) -> Result<(TyCtx, Ty), String> {
    fn check_arg_has_correct_kind(
        kind_ctx: &KindCtx,
        expected: &Kind,
        kv: &ArgKinded,
    ) -> Result<(), String> {
        match kv {
            ArgKinded::Provenance(_) if expected == &Kind::Provenance => Ok(()),
            ArgKinded::Ty(_) if expected == &Kind::Ty => Ok(()),
            ArgKinded::Nat(_) if expected == &Kind::Nat => Ok(()),
            ArgKinded::Memory(_) if expected == &Kind::Memory => Ok(()),
            // TODO?
            //  KindedArg::Frame(_) if expected == &Kind::Frame => Ok(()),
            ArgKinded::Ident(k_ident) if expected == kind_ctx.get_kind(k_ident)? => Ok(()),
            _ => Err(format!(
                "expected argument of kind {:?}, but the provided argument is {:?}",
                expected, kv
            )),
        }
    }

    // TODO check well-kinded: FrameTyping, Prv, Ty
    let mut res_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, ty_ctx, exec, ef)?;
    if let Ty::Data(DataTy::Fn(gen_params, param_tys, _, _, out_ty)) = ef.ty.as_ref().unwrap() {
        if gen_params.len() != k_args.len() {
            return Err(format!(
                "Wrong amount of generic arguments. Expected {}, found {}",
                gen_params.len(),
                k_args.len()
            ));
        }
        for (gp, kv) in gen_params.iter().zip(&*k_args) {
            check_arg_has_correct_kind(kind_ctx, &gp.kind, kv)?;
        }
        if args.len() != param_tys.len() {
            return Err(format!(
                "Wrong amount of arguments. Expected {}, found {}",
                param_tys.len(),
                args.len()
            ));
        }
        let subst_param_tys: Vec<_> = param_tys
            .iter()
            .map(|ty| {
                let mut subst_ty = ty.clone();
                for (gen_param, k_arg) in gen_params.iter().zip(&*k_args) {
                    subst_ty = subst_ty.subst_ident_kinded(gen_param, k_arg)
                }
                subst_ty
            })
            .collect();

        for (arg, param_ty) in args.iter_mut().zip(subst_param_tys) {
            res_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, res_ty_ctx, exec, arg)?;
            if arg.ty.as_ref().unwrap() != &param_ty {
                return Err(format!(
                    "Argument types do not match.\n Expected {:?}, but found {:?}.",
                    param_ty,
                    arg.ty.as_ref().unwrap()
                ));
            }
        }
        // TODO check provenance relations
        let subst_out_ty = {
            let mut subst_ty = out_ty.as_ref().clone();
            for (gen_param, k_arg) in gen_params.iter().zip(&*k_args) {
                subst_ty = subst_ty.subst_ident_kinded(gen_param, k_arg)
            }
            subst_ty
        };
        Ok((res_ty_ctx, subst_out_ty))
    } else {
        Err(format!(
            "The provided function expression\n {:?}\n does not have a function type.",
            ef
        ))
    }
}

fn ty_check_tuple(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: ExecLoc,
    elems: &mut [Expr],
) -> Result<(TyCtx, Ty), String> {
    let mut tmp_ty_ctx = ty_ctx;
    for elem in elems.iter_mut() {
        tmp_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, tmp_ty_ctx, exec, elem)?;
    }
    let elem_tys: Result<Vec<_>, _> = elems
        .iter()
        .map(|elem| match elem.ty.as_ref().unwrap() {
            Ty::Data(dty) => Ok(dty.clone()),
            Ty::View(_) => Err("Tuple elements cannot be views.".to_string()),
        })
        .collect();
    Ok((tmp_ty_ctx, Ty::Data(DataTy::Tuple(elem_tys?))))
}

fn ty_check_array(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: ExecLoc,
    elems: &mut Vec<Expr>,
) -> Result<(TyCtx, Ty), String> {
    assert!(!elems.is_empty());
    let mut tmp_ty_ctx = ty_ctx;
    for elem in elems.iter_mut() {
        tmp_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, tmp_ty_ctx, exec, elem)?;
    }
    let ty = elems.first().unwrap().ty.clone();
    if !matches!(ty, Some(Ty::Data(_))) {
        return Err("Array elements cannot be views.".to_string());
    }
    if elems.iter().any(|elem| ty != elem.ty) {
        Err("Not all provided elements have the same type.".to_string())
    } else {
        Ok((
            tmp_ty_ctx,
            Ty::Data(DataTy::Array(
                Box::new(ty.as_ref().unwrap().dty().clone()),
                Nat::Lit(elems.len()),
            )),
        ))
    }
}

fn ty_check_literal(ty_ctx: TyCtx, l: &mut Lit) -> (TyCtx, Ty) {
    let scalar_data = match l {
        Lit::Unit => ScalarTy::Unit,
        Lit::Bool(_) => ScalarTy::Bool,
        Lit::I32(_) => ScalarTy::I32,
        Lit::F32(_) => ScalarTy::F32,
    };
    (ty_ctx, Ty::Data(DataTy::Scalar(scalar_data)))
}

fn ty_check_let(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: ExecLoc,
    ident: &mut Ident,
    ty: &Option<Ty>,
    e1: &mut Expr,
    e2: &mut Expr,
) -> Result<(TyCtx, Ty), String> {
    let ty_ctx_e1 = ty_check_expr(gl_ctx, kind_ctx, ty_ctx, exec, e1)?;
    let e1_ty = e1.ty.as_ref().unwrap();
    let ty = if let Some(tty) = ty { tty } else { e1_ty };

    let ty_ctx_sub = match (ty, e1_ty) {
        (Ty::View(_), Ty::View(_)) => {
            if ty != e1_ty {
                return Err(format!(
                    "Trying to bind view expression of type {:?} to identifier of type {:?}",
                    e1_ty, ty
                ));
            }
            ty_ctx_e1
        }
        (Ty::Data(dty), Ty::Data(e1_dty)) => subty::check(kind_ctx, ty_ctx_e1, e1_dty, dty)?,
        _ => {
            return Err(format!(
                "Trying to bind expression of type {:?} to identifier of type {:?}",
                e1_ty, ty
            ))
        }
    };
    let ident_with_annotated_ty = IdentTyped::new(ident.clone(), ty.clone());
    let garbage_coll_ty_ctx_with_ident = ty_ctx_sub
        .append_ident_typed(ident_with_annotated_ty)
        .garbage_collect_loans();
    // TODO check that x is dead,
    //  the derivation needs to call T-Drop in case of copy types then.
    //  Equivalent to saying that the variable must be used.
    let ty_ctx_e2 = ty_check_expr(gl_ctx, kind_ctx, garbage_coll_ty_ctx_with_ident, exec, e2)?;
    let ty_ctx_e2_no_ident = ty_ctx_e2.drop_ident(ident).unwrap();
    Ok((ty_ctx_e2_no_ident, e2.ty.as_ref().unwrap().clone()))
}

fn ty_check_seq(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: ExecLoc,
    e1: &mut Expr,
    e2: &mut Expr,
) -> Result<(TyCtx, Ty), String> {
    let ty_ctx_e1 = ty_check_expr(gl_ctx, kind_ctx, ty_ctx, exec, e1)?;
    let ty_ctx_e2 = ty_check_expr(
        gl_ctx,
        kind_ctx,
        ty_ctx_e1.garbage_collect_loans(),
        exec,
        e2,
    )?;
    Ok((ty_ctx_e2, e2.ty.as_ref().unwrap().clone()))
}

fn ty_check_pl_expr_with_deref(
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: ExecLoc,
    pl_expr: &PlaceExpr,
) -> Result<(TyCtx, Ty), String> {
    let own = Ownership::Shrd;
    borrow_check::ownership_safe(kind_ctx, &ty_ctx, &[], own, pl_expr)?;
    if let Ok(ty) = place_expr_ty_under_own(kind_ctx, &ty_ctx, Ownership::Shrd, pl_expr) {
        if !ty.is_fully_alive() {
            return Err("Place was moved before.".to_string());
        }
        if ty.copyable() {
            // this line is a trick to release a life time that is connected to ty_ctx
            let ty = ty.clone();
            Ok((ty_ctx, Ty::Data(ty)))
        } else {
            Err("Data type is not copyable.".to_string())
        }
    } else {
        Err("Place expression does not have correct type.".to_string())
    }
}

fn ty_check_pl_expr_without_deref(
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: ExecLoc,
    pl_expr: &PlaceExpr,
) -> Result<(TyCtx, Ty), String> {
    let place = pl_expr.to_place().unwrap();
    let pl_ty = ty_ctx.place_ty(&place)?;
    if !pl_ty.is_fully_alive() {
        return Err("Place was moved before.".to_string());
    }
    let res_ty_ctx = if pl_ty.copyable() {
        borrow_check::ownership_safe(kind_ctx, &ty_ctx, &[], Ownership::Shrd, pl_expr)?;
        ty_ctx
    } else {
        borrow_check::ownership_safe(kind_ctx, &ty_ctx, &[], Ownership::Uniq, pl_expr)?;
        ty_ctx.kill_place(&place)
    };
    Ok((res_ty_ctx, pl_ty))
}

fn ty_check_borrow(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: ExecLoc,
    prv_val_name: &str,
    own: Ownership,
    pl_expr: &mut PlaceExpr,
) -> Result<(TyCtx, Ty), String> {
    if !ty_ctx.loans_for_prv(prv_val_name)?.is_empty() {
        return Err(
            "Trying to borrow with a provenance that is used in a different borrow.".to_string(),
        );
    }
    let loans = borrow_check::ownership_safe(kind_ctx, &ty_ctx, &[], own, pl_expr)?;
    let ty = place_expr_ty_under_own(kind_ctx, &ty_ctx, own, pl_expr)?;
    if !ty.is_fully_alive() {
        return Err("The place was at least partially moved before.".to_string());
    }
    let (reffed_ty, mem) = match &ty {
        DataTy::Dead(_) => panic!("Cannot happen because of the alive check."),
        DataTy::At(inner_ty, m) => (inner_ty.deref().clone(), m.clone()),
        _ => (ty.clone(), Memory::CpuStack),
    };
    let res_ty = DataTy::Ref(
        Provenance::Value(prv_val_name.to_string()),
        own,
        mem,
        Box::new(reffed_ty),
    );
    let res_ty_ctx = ty_ctx.extend_loans_for_prv(prv_val_name, loans)?;
    Ok((res_ty_ctx, Ty::Data(res_ty)))
}

// Δ; Γ ⊢ω p:τ
// p in an ω context has type τ under Δ and Γ
fn place_expr_ty_under_own<'a>(
    kind_ctx: &KindCtx,
    ty_ctx: &'a TyCtx,
    own: Ownership,
    pl_expr: &PlaceExpr,
) -> Result<&'a DataTy, String> {
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
) -> Result<(&'a DataTy, Vec<&'a Provenance>), String> {
    match pl_expr {
        // TC-Var
        PlaceExpr::Ident(ident) => var_expr_ty_and_empty_prvs_under_own(ty_ctx, &ident),
        // TC-Proj
        PlaceExpr::Proj(tuple_expr, n) => {
            proj_expr_ty_and_passed_prvs_under_own(kind_ctx, ty_ctx, own, tuple_expr, n)
        }
        // TC-Deref
        // TODO respect memory
        PlaceExpr::Deref(borr_expr) => {
            deref_expr_ty_and_passed_prvs_under_own(kind_ctx, ty_ctx, own, borr_expr)
        }
    }
}

fn var_expr_ty_and_empty_prvs_under_own<'a>(
    ty_ctx: &'a TyCtx,
    ident: &Ident,
) -> Result<(&'a DataTy, Vec<&'a Provenance>), String> {
    let ty = ty_ctx.ident_ty(&ident)?;
    if let Ty::Data(dty) = ty {
        if !dty.is_fully_alive() {
            return Err("The value in this identifier has been moved out.".to_string());
        }
        return Ok((dty, vec![]));
    }
    panic!("Trying to give type under ownership for view type. View types can never be borrowed.")
}

fn proj_expr_ty_and_passed_prvs_under_own<'a>(
    kind_ctx: &KindCtx,
    ty_ctx: &'a TyCtx,
    own: Ownership,
    tuple_expr: &PlaceExpr,
    n: &Nat,
) -> Result<(&'a DataTy, Vec<&'a Provenance>), String> {
    let (pl_expr_ty, passed_prvs) =
        place_expr_ty_and_passed_prvs_under_own(kind_ctx, ty_ctx, own, tuple_expr)?;
    if let DataTy::Tuple(elem_tys) = pl_expr_ty {
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
    borr_expr: &PlaceExpr,
) -> Result<(&'a DataTy, Vec<&'a Provenance>), String> {
    let (pl_expr_ty, mut passed_prvs) =
        place_expr_ty_and_passed_prvs_under_own(kind_ctx, ty_ctx, own, borr_expr)?;
    if let DataTy::Ref(prv, ref_own, mem, ty) = pl_expr_ty {
        if ref_own < &own {
            return Err("Trying to dereference and mutably use a shrd reference.".to_string());
        }
        let outl_rels = passed_prvs.iter().map(|&passed_prv| (prv, passed_prv));
        subty::multiple_outlives(kind_ctx, ty_ctx.clone(), outl_rels)?;
        passed_prvs.push(prv);
        Ok((ty, passed_prvs))
    } else {
        Err("Trying to dereference non reference type.".to_string())
    }
}

#[cfg(test)]
mod tests {
    use crate::ty_check::ty_check_global_fun_def;

    #[test]
    fn test_dummy_fun() -> Result<(), String> {
        let dummy_fun_src = r#"fn dummy_fun<a: prv>(
            h_array: &a uniq cpu.heap [i32; 4096]
        ) -[cpu.thread]-> [i32; 3] {
            let answer_to_everything = [1,2,42];
            answer_to_everything
        }"#;

        let dummy_fun = crate::parser::parse_global_fun_def(dummy_fun_src).unwrap();
        let mut compil_unit = vec![dummy_fun];
        super::ty_check(&mut compil_unit)?;
        print!("{:?}", compil_unit[0]);
        Ok(())
    }
}
