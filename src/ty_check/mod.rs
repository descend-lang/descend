mod borrow_check;
// TODO remove pub from pub mod ctxs, only public because of basi_syntax tests
pub mod ctxs;
pub mod pre_decl;
mod subty;

use crate::ast::internal::{IdentTyped, Loan, PrvMapping};
use crate::ast::DataTy::Scalar;
use crate::ast::*;
use ctxs::{GlobalCtx, KindCtx, TyCtx};
use std::collections::HashMap;
use std::ops::Deref;

// ∀ε ∈ Σ. Σ ⊢ ε
// --------------
//      ⊢ Σ
pub fn ty_check(compil_unit: &mut CompilUnit) -> Result<(), String> {
    ty_check_with_pre_decl_funs(compil_unit, &pre_decl::fun_decls())
}

pub fn ty_check_with_pre_decl_funs(
    compil_unit: &mut CompilUnit,
    pre_decl_funs: &[(&str, Ty)],
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
fn ty_check_global_fun_def(gl_ctx: &GlobalCtx, gf: &mut FunDef) -> Result<(), String> {
    let kind_ctx = KindCtx::from(gf.generic_params.clone(), gf.prv_rels.clone())?;

    // Build frame typing for this function
    let glf_frame = internal::append_idents_typed(
        &vec![],
        gf.params
            .iter()
            .map(|ParamDecl { ident, ty, .. }| IdentTyped {
                ident: ident.clone(),
                ty: ty.clone(),
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
    exec: Exec,
    expr: &mut Expr,
) -> Result<TyCtx, String> {
    // TODO input contexts are well-formed
    //   well_formed_ctxs(gl_ctx, kind_ctx, &ty_ctx);
    let (res_ty_ctx, ty) = match &mut expr.expr {
        ExprKind::PlaceExpr(pl_expr) => {
            if pl_expr.is_place() {
                ty_check_pl_expr_without_deref(gl_ctx, kind_ctx, ty_ctx, pl_expr)?
            } else {
                ty_check_pl_expr_with_deref(gl_ctx, kind_ctx, ty_ctx, exec, pl_expr)?
            }
        }
        ExprKind::LetProv(prvs, body) => {
            ty_check_letprov(gl_ctx, kind_ctx, ty_ctx, exec, prvs, body)?
        }
        // TODO respect mutability
        ExprKind::Let(mutable, ident, ty, ref mut e1, ref mut e2) => {
            ty_check_let(gl_ctx, kind_ctx, ty_ctx, exec, ident, ty, e1, e2)?
        }
        ExprKind::LetUninit(ident, ty, e) => {
            ty_check_let_uninit(gl_ctx, kind_ctx, ty_ctx, exec, ident, ty, e)?
        }
        ExprKind::Seq(e1, e2) => ty_check_seq(gl_ctx, kind_ctx, ty_ctx, exec, e1, e2)?,
        ExprKind::Lit(l) => ty_check_literal(ty_ctx, l),
        ExprKind::Array(elems) => ty_check_array(gl_ctx, kind_ctx, ty_ctx, exec, elems)?,
        ExprKind::Tuple(elems) => ty_check_tuple(gl_ctx, kind_ctx, ty_ctx, exec, elems)?,
        ExprKind::TupleView(elems) => ty_check_tuple_view(gl_ctx, kind_ctx, ty_ctx, exec, elems)?,
        ExprKind::Proj(e, i) => ty_check_proj(gl_ctx, kind_ctx, ty_ctx, exec, e, *i)?,
        ExprKind::App(ef, k_args, args) => {
            ty_check_app(gl_ctx, kind_ctx, ty_ctx, exec, ef, k_args, args)?
        }
        ExprKind::Ref(prv, own, pl_expr) => {
            ty_check_borrow(gl_ctx, kind_ctx, ty_ctx, exec, prv, *own, pl_expr)?
        }
        ExprKind::Index(pl_expr, index) => {
            //ty_check_index_copy(gl_ctx, kind_ctx, ty_ctx, exec, pl_expr, index)?
            unimplemented!()
        }
        ExprKind::Assign(pl_expr, e) => {
            if pl_expr.is_place() {
                ty_check_assign_place(gl_ctx, kind_ctx, ty_ctx, exec, pl_expr, e)?
            } else {
                ty_check_assign_deref(gl_ctx, kind_ctx, ty_ctx, exec, pl_expr, e)?
            }
        }
        ExprKind::ParFor(parall_collec, input, funs) => {
            ty_check_par_for(gl_ctx, kind_ctx, ty_ctx, exec, parall_collec, input, funs)?
        }
        ExprKind::ForNat(var, range, body) => {
            ty_check_for_nat(gl_ctx, kind_ctx, ty_ctx, exec, var, range, body)?
        }
        ExprKind::IfElse(cond, case_true, case_false) => {
            ty_check_ifelse(gl_ctx, kind_ctx, ty_ctx, exec, cond, case_true, case_false)?
        }
        ExprKind::For(ident, set, body) => {
            ty_check_for(gl_ctx, kind_ctx, ty_ctx, exec, ident, set, body)?
        }
        ExprKind::While(cond, body) => ty_check_while(gl_ctx, kind_ctx, ty_ctx, exec, cond, body)?,
        ExprKind::Lambda(params, exec, ret_ty, body) => {
            ty_check_lambda(gl_ctx, kind_ctx, ty_ctx, *exec, params, ret_ty, body)?
        }
        ExprKind::BinOp(bin_op, lhs, rhs) => {
            ty_check_binary_op(gl_ctx, kind_ctx, ty_ctx, exec, bin_op, lhs, rhs)?
        }
        ExprKind::UnOp(un_op, e) => ty_check_unary_op(gl_ctx, kind_ctx, ty_ctx, exec, un_op, e)?,
        ExprKind::BorrowIndex(_, _, _, _) => unimplemented!(),
    };

    // TODO type well formed under output contexts
    expr.ty = Some(ty);
    Ok(res_ty_ctx)
}
fn ty_check_for_nat(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: Exec,
    var: &Ident,
    range: &Nat,
    body: &mut Expr,
) -> Result<(TyCtx, Ty), String> {
    let scoped_kind_ctx: KindCtx = kind_ctx.clone().append_idents(vec![IdentKinded {
        ident: var.clone(),
        kind: Kind::Nat,
    }]);
    let ty_ctx_1 = ty_check_expr(gl_ctx, &scoped_kind_ctx, ty_ctx, exec, body)?;
    // let ty_ctx_2 = ty_check_expr(gl_ctx, &scoped_kind_ctx, ty_ctx_1.clone(), exec, body)?;
    // if &ty_ctx_1 != &ty_ctx_2 {
    //    return Err("Using a data type in loop that can only be used once.".to_string());
    // }
    Ok((ty_ctx_1, Ty::Data(DataTy::Scalar(ScalarTy::Unit))))
}

fn ty_check_for(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: Exec,
    ident: &Ident,
    set: &mut Expr,
    body: &mut Expr,
) -> Result<(TyCtx, Ty), String> {
    unimplemented!()
}

fn ty_check_while(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: Exec,
    cond: &mut Expr,
    body: &mut Expr,
) -> Result<(TyCtx, Ty), String> {
    let cond_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, ty_ctx, exec, cond)?;
    let body_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, cond_ty_ctx, exec, body)?;

    let cond_temp_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, body_ty_ctx.clone(), exec, cond)?;
    if body_ty_ctx != cond_temp_ty_ctx {
        return Err("Context should have stayed the same".to_string());
    }
    let body_temp_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, body_ty_ctx.clone(), exec, body)?;
    if body_ty_ctx != body_temp_ty_ctx {
        return Err("Context should have stayed the same".to_string());
    }

    let cond_ty = cond.ty.as_ref().unwrap();
    let body_ty = body.ty.as_ref().unwrap();

    if !matches!(Ty::Data(DataTy::Scalar(ScalarTy::Bool)), cond_ty) {
        return Err(format!(
            "Expected condition in while loop, instead got {:?}",
            cond_ty
        ));
    }
    if !matches!(Ty::Data(DataTy::Scalar(ScalarTy::Bool)), body_ty) {
        return Err(format!(
            "Body of while loop is not of unit type, instead got {:?}",
            body_ty
        ));
    }
    Ok((body_ty_ctx, Ty::Data(DataTy::Scalar(ScalarTy::Unit))))
}

fn ty_check_ifelse(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: Exec,
    cond: &mut Expr,
    case_true: &mut Expr,
    case_false: &mut Expr,
) -> Result<(TyCtx, Ty), String> {
    unimplemented!()
}

// TODO split up groupings, i.e., deal with TupleViews and require enough functions.
fn ty_check_par_for(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: Exec,
    parall_collec: &mut Expr,
    input: &mut Expr,
    funs: &mut Expr,
) -> Result<(TyCtx, Ty), String> {
    fn to_exec_and_size(parall_collec: &Expr) -> Exec {
        match parall_collec.ty.as_ref().unwrap() {
            Ty::Data(DataTy::Grid(_, _)) => Exec::GpuGrid,
            Ty::Data(DataTy::Block(_, _)) => Exec::GpuBlock,
            Ty::Data(DataTy::Scalar(ScalarTy::Warp)) => Exec::GpuWarp,
            _ => panic!("Expected a parallel collection: Grid or Block."),
        }
    }
    fn executable_over_parall_collec_and_input(
        fun: &Expr,
        parall_collec: &Expr,
        in_elem_tys: Vec<&Ty>,
    ) -> Result<(), String> {
        match fun.ty.as_ref().unwrap() {
            Ty::Fn(_, param_tys, fun_exec, ret_ty) => {
                let num_fun_params = in_elem_tys.len() + 1;
                if param_tys.len() != num_fun_params {
                    return Err(format!(
                        "Wrong amount of parameters in provided function. Expected {},\
                    one for parallelism expression and one for input.",
                        num_fun_params
                    ));
                }
                let fun_parall_elem_ty = &param_tys[0];
                let fun_input_elem_tys: Vec<_> = param_tys[1..].iter().map(|t| t).collect();
                let parall_elem_dty = match parall_collec.ty.as_ref().unwrap() {
                    Ty::Data(dty) => match dty {
                        DataTy::Grid(pe_dty, _) => pe_dty.as_ref().clone(),
                        DataTy::Block(pe_dty, _) => pe_dty.as_ref().clone(),
                        DataTy::Scalar(ScalarTy::Warp) => DataTy::Scalar(ScalarTy::Thread),
                        _ => {
                            return Err(
                                "Provided expression is not a parallel collection.".to_string()
                            )
                        }
                    },
                    _ => {
                        return Err("Provided expression is not a parallel collection.".to_string())
                    }
                };
                if fun_parall_elem_ty != &Ty::Data(parall_elem_dty.clone()) {
                    return Err(
                        "Function does not fit the provided parallel collection.".to_string()
                    );
                }
                if fun_input_elem_tys != in_elem_tys {
                    return Err("Function does not fit the provided input.".to_string());
                }
                let exec = match parall_elem_dty {
                    DataTy::Block(_, _) => Exec::GpuBlock,
                    DataTy::Scalar(ScalarTy::Thread) => Exec::GpuThread,
                    _ => unimplemented!(),
                };
                if fun_exec != &exec {
                    return Err("Execution resource does not fit.".to_string());
                }
                if ret_ty.as_ref() != &Ty::Data(Scalar(ScalarTy::Unit)) {
                    return Err("Function has wrong return type. Expected ().".to_string());
                }

                Ok(())
            }
            _ => Err("The provided expression is not a function.".to_string()),
        }
    }
    let parall_collec_ty_ctx =
        ty_check_expr(gl_ctx, kind_ctx, ty_ctx.clone(), exec, parall_collec)?;
    let allowed_exec = to_exec_and_size(parall_collec);
    if allowed_exec != exec {
        return Err(format!(
            "Trying to run a parallel for-loop over {:?} inside of {:?}",
            parall_collec, exec
        ));
    }
    let input_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, parall_collec_ty_ctx, exec, input)?;
    let in_param_tys: Vec<_> = match input.ty.as_ref().unwrap() {
        Ty::View(ViewTy::Tuple(input_tys)) => input_tys
            .iter()
            .map(|t| match t {
                Ty::View(ViewTy::Array(tty, n)) => tty.as_ref(),
                tty => tty,
            })
            .collect(),
        _ => return Err("Provided input expression is not a tuple view.".to_string()),
    };
    // Dismiss the resulting typing context. A par_for always synchronizes. Therefore everything
    // that is used for the par_for can safely be reused.
    let _funs_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, input_ty_ctx, exec, funs)?;
    executable_over_parall_collec_and_input(funs, parall_collec, in_param_tys)?;
    Ok((ty_ctx, Ty::Data(DataTy::Scalar(ScalarTy::Unit))))
}

fn ty_check_lambda(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: Exec,
    params: &mut [ParamDecl],
    ret_dty: &DataTy,
    body: &mut Expr,
) -> Result<(TyCtx, Ty), String> {
    // TODO WARNING: Currently allows capturing freely. There are not checks assoicated with this.
    //  This is clearly not correct.
    // Build frame typing for this function
    let fun_frame = internal::append_idents_typed(
        &vec![],
        params
            .iter()
            .map(|ParamDecl { ident, ty, .. }| IdentTyped {
                ident: ident.clone(),
                ty: ty.clone(),
            })
            .collect(),
    );
    let fun_ty_ctx = ty_ctx.clone().append_frm_ty(fun_frame);

    ty_check_expr(gl_ctx, &kind_ctx, fun_ty_ctx, exec, body)?;

    // t <= t_f
    let empty_ty_ctx = subty::check(
        &kind_ctx,
        TyCtx::new(),
        body.ty.as_ref().unwrap().dty(),
        &ret_dty,
    )?;

    assert!(
        empty_ty_ctx.is_empty(),
        format!(
            "Expected typing context to be empty. But TyCtx:\n {:?}",
            empty_ty_ctx
        )
    );

    let fun_ty = Ty::Fn(
        vec![],
        params.iter().map(|decl| decl.ty.clone()).collect(),
        exec,
        Box::new(Ty::Data(ret_dty.clone())),
    );

    Ok((ty_ctx, fun_ty))
}

fn ty_check_letprov(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: Exec,
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
    exec: Exec,
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
    exec: Exec,
    deref_expr: &mut PlaceExpr,
    e: &mut Expr,
) -> Result<(TyCtx, Ty), String> {
    let assigned_val_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, ty_ctx, exec, e)?;
    let deref_ty = place_expr_ty_under_exec_own(
        gl_ctx,
        kind_ctx,
        &assigned_val_ty_ctx,
        exec,
        Ownership::Uniq,
        deref_expr,
    )?
    .clone();

    if !deref_ty.is_fully_alive() {
        return Err(
            "Trying to assign through reference, to a type which is not fully alive.".to_string(),
        );
    }

    if let Ty::Data(deref_dty) = deref_ty {
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
            &deref_dty,
        )?;
        Ok((
            after_subty_ctx.without_reborrow_loans(deref_expr),
            Ty::Data(DataTy::Scalar(ScalarTy::Unit)),
        ))
    } else {
        Err("Trying to dereference view type which is not allowed.".to_string())
    }
}

fn ty_check_index_copy(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: Exec,
    pl_expr: &mut PlaceExpr,
    index: &mut Nat,
) -> Result<(TyCtx, Ty), String> {
    borrow_check::ownership_safe(kind_ctx, &ty_ctx, &[], Ownership::Shrd, pl_expr)?;
    let pl_expr_ty =
        place_expr_ty_under_exec_own(gl_ctx, kind_ctx, &ty_ctx, exec, Ownership::Shrd, pl_expr)?;
    let elem_ty = match pl_expr_ty {
        Ty::Data(DataTy::Array(elem_ty, n)) => *elem_ty,
        Ty::Data(DataTy::At(arr_ty, _)) => {
            if let DataTy::Array(elem_ty, n) = *arr_ty {
                *elem_ty
            } else {
                return Err("Trying to index into non array type.".to_string());
            }
        }
        Ty::View(_) => unimplemented!(),
        _ => return Err("Trying to index into non array type.".to_string()),
    };
    // TODO check that index is smaller than n here!?
    if elem_ty.copyable() {
        Ok((ty_ctx, Ty::Data(elem_ty)))
    } else {
        Err("Cannot move out of array type.".to_string())
    }
}

// FIXME currently assumes that binary operators exist only for f32 and i32 and that both
//  arguments have to be of the same type
fn ty_check_binary_op(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: Exec,
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

// FIXME currently assumes that binary operators exist only for f32 and i32
fn ty_check_unary_op(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: Exec,
    un_op: &UnOp,
    e: &mut Expr,
) -> Result<(TyCtx, Ty), String> {
    let res_ctx = ty_check_expr(gl_ctx, kind_ctx, ty_ctx, exec, e)?;
    let e_ty = e.ty.as_ref().unwrap();
    match e_ty {
        Ty::Data(DataTy::Scalar(ScalarTy::F32)) | Ty::Data(DataTy::Scalar(ScalarTy::I32)) => {
            Ok((res_ctx, e_ty.clone()))
        }
        _ => Err(format!(
            "Exected a number type (i.e., f32 or i32), but found {:?}",
            e_ty
        )),
    }
}

fn ty_check_app(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: Exec,
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
    if let Ty::Fn(gen_params, param_tys, exec_f, out_ty) = ef.ty.as_ref().unwrap() {
        if !exec_f.callable_in(exec) {
            return Err(format!(
                "Trying to apply function for execution resource `{}` \
                under execution resource `{}`",
                exec_f, exec
            ));
        }
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
    exec: Exec,
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
            Ty::Ident(_) => Err(
                "Tuple elements must be data types, but found general type identifier.".to_string(),
            ),
            Ty::Fn(_, _, _, _) => {
                Err("Tuple elements must be data types, but found function type.".to_string())
            }
        })
        .collect();
    Ok((tmp_ty_ctx, Ty::Data(DataTy::Tuple(elem_tys?))))
}

fn ty_check_proj(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: Exec,
    e: &mut Expr,
    i: usize,
) -> Result<(TyCtx, Ty), String> {
    if let ExprKind::PlaceExpr(_) = e.expr {
        panic!("Place expression should have been typechecked by a different rule.")
    }

    let tuple_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, ty_ctx, exec, e)?;
    let elem_ty = match e.ty.as_ref().unwrap() {
        Ty::Data(DataTy::Tuple(dtys)) => match dtys.get(i) {
            Some(dty) => Ty::Data(dty.clone()),
            None => {
                return Err(format!(
                    "Cannot project element `{}` from tuple with {} elements.",
                    i,
                    dtys.len()
                ))
            }
        },
        Ty::View(ViewTy::Tuple(tys)) => match tys.get(i) {
            Some(ty) => ty.clone(),
            None => {
                return Err(format!(
                    "Cannot project element `{}` from tuple with {} elements.",
                    i,
                    tys.len()
                ))
            }
        },
        _ => return Err("Cannot project from non tuple type.".to_string()),
    };

    Ok((tuple_ty_ctx, elem_ty))
}

fn ty_check_tuple_view(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: Exec,
    elems: &mut [Expr],
) -> Result<(TyCtx, Ty), String> {
    let mut tmp_ty_ctx = ty_ctx;
    for elem in elems.iter_mut() {
        tmp_ty_ctx = ty_check_expr(gl_ctx, kind_ctx, tmp_ty_ctx, exec, elem)?;
    }
    let elem_tys: Vec<_> = elems
        .iter()
        .map(|elem| elem.ty.as_ref().unwrap().clone())
        .collect();
    Ok((tmp_ty_ctx, Ty::View(ViewTy::Tuple(elem_tys))))
}

fn ty_check_array(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: Exec,
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
    exec: Exec,
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

// TODO respect mutability, uninit vars must always be mutable
fn ty_check_let_uninit(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: Exec,
    ident: &Ident,
    ty: &Ty,
    expr: &mut Expr,
) -> Result<(TyCtx, Ty), String> {
    if let Ty::Data(dty) = ty {
        let ident_with_ty =
            IdentTyped::new(ident.clone(), Ty::Data(DataTy::Dead(Box::new(dty.clone()))));
        let final_ty_ctx = ty_check_expr(
            gl_ctx,
            kind_ctx,
            ty_ctx.append_ident_typed(ident_with_ty),
            exec,
            expr,
        )?;
        Ok((final_ty_ctx, expr.ty.as_ref().unwrap().clone()))
    } else {
        Err("Cannot create mutable variable of non data type.".to_string())
    }
    // TODO check if ident is fully dead after e?
}

fn ty_check_seq(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: Exec,
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
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: Exec,
    pl_expr: &PlaceExpr,
) -> Result<(TyCtx, Ty), String> {
    borrow_check::ownership_safe(kind_ctx, &ty_ctx, &[], Ownership::Shrd, pl_expr)?;
    if let Ok(ty) =
        place_expr_ty_under_exec_own(gl_ctx, kind_ctx, &ty_ctx, exec, Ownership::Shrd, pl_expr)
    {
        if !ty.is_fully_alive() {
            return Err(format!("Part of Place {:?} was moved before.", pl_expr));
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

fn ty_check_pl_expr_without_deref(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    pl_expr: &PlaceExpr,
) -> Result<(TyCtx, Ty), String> {
    let place = pl_expr.to_place().unwrap();
    // If place is an identifier referring to a globally declared function
    let (res_ty_ctx, pl_ty) = if let Ok(fun_ty) = gl_ctx.fun_ty_by_name(&place.ident.name) {
        (ty_ctx, fun_ty.clone())
    } else {
        // If place is NOT referring to a globally declared function
        let pl_ty = ty_ctx.place_ty(&place)?;
        if !pl_ty.is_fully_alive() {
            return Err(format!("Part of Place {:?} was moved before.", pl_expr));
        }
        let res_ty_ctx = if pl_ty.copyable() {
            borrow_check::ownership_safe(kind_ctx, &ty_ctx, &[], Ownership::Shrd, pl_expr)?;
            ty_ctx
        } else {
            borrow_check::ownership_safe(kind_ctx, &ty_ctx, &[], Ownership::Uniq, pl_expr)?;
            ty_ctx.kill_place(&place)
        };
        (res_ty_ctx, pl_ty)
    };

    Ok((res_ty_ctx, pl_ty))
}

fn ty_check_borrow(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: TyCtx,
    exec: Exec,
    prv: &Provenance,
    own: Ownership,
    pl_expr: &mut PlaceExpr,
) -> Result<(TyCtx, Ty), String> {
    let prv_val_name = match prv {
        Provenance::Value(prv_val_name) => prv_val_name,
        Provenance::Ident(_) => {
            // return Err("Cannot borrow using a provenance variable.".to_string())
            return Err(
                format!("Cannot borrow using a provenance variable {:?}.", prv)
            )
        }
    };

    if !ty_ctx.loans_for_prv(prv_val_name)?.is_empty() {
        return Err(
            "Trying to borrow with a provenance that is used in a different borrow.".to_string(),
        );
    }
    let loans = borrow_check::ownership_safe(kind_ctx, &ty_ctx, &[], own, pl_expr)?;
    let (ty, mem) =
        place_expr_ty_mem_under_exec_own(gl_ctx, kind_ctx, &ty_ctx, exec, own, pl_expr)?;
    if !ty.is_fully_alive() {
        return Err("The place was at least partially moved before.".to_string());
    }
    let (reffed_ty, rmem) = match &ty {
        Ty::Data(DataTy::Dead(_)) => panic!("Cannot happen because of the alive check."),
        Ty::Data(DataTy::At(inner_ty, m)) => (inner_ty.deref().clone(), m.clone()),
        Ty::Data(dty) => (
            dty.clone(),
            match mem {
                Some(m) => m,
                None => {
                    return Err(
                        "Trying to borrow value that does not exist for the current \
            execution resource."
                            .to_string(),
                    )
                }
            },
        ),
        Ty::View(_) => return Err("Trying to borrow a view.".to_string()),
        Ty::Fn(_, _, _, _) => return Err("Trying to borrow a function.".to_string()),
        Ty::Ident(_) => {
            return Err(
                "Borrowing from value of unspecified type. This could be a view.\
            Therefore it is not allowed to borrow."
                    .to_string(),
            )
        }
    };
    let res_ty = DataTy::Ref(
        Provenance::Value(prv_val_name.to_string()),
        own,
        rmem,
        Box::new(reffed_ty),
    );
    let res_ty_ctx = ty_ctx.extend_loans_for_prv(prv_val_name, loans)?;
    Ok((res_ty_ctx, Ty::Data(res_ty)))
}

// Δ; Γ ⊢ω p:τ
// p in an ω context has type τ under Δ and Γ
fn place_expr_ty_under_exec_own(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: &TyCtx,
    exec: Exec,
    own: Ownership,
    pl_expr: &PlaceExpr,
) -> Result<Ty, String> {
    let (ty, _) = place_expr_ty_mem_under_exec_own(gl_ctx, kind_ctx, ty_ctx, exec, own, pl_expr)?;
    Ok(ty)
}

fn place_expr_ty_mem_under_exec_own(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: &TyCtx,
    exec: Exec,
    own: Ownership,
    pl_expr: &PlaceExpr,
) -> Result<(Ty, Option<Memory>), String> {
    let (ty, mem, _) =
        place_expr_ty_mem_passed_prvs_under_exec_own(gl_ctx, kind_ctx, ty_ctx, exec, own, pl_expr)?;
    Ok((ty, mem))
}

// Δ; Γ ⊢ω p:τ,{ρ}
// p in an ω context has type τ under Δ and Γ, passing through provenances in Vec<ρ>
fn place_expr_ty_mem_passed_prvs_under_exec_own(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: &TyCtx,
    exec: Exec,
    own: Ownership,
    pl_expr: &PlaceExpr,
) -> Result<(Ty, Option<Memory>, Vec<Provenance>), String> {
    match pl_expr {
        // TC-Var
        PlaceExpr::Ident(ident) => {
            var_expr_ty_mem_empty_prvs_under_exec_own(gl_ctx, ty_ctx, exec, &ident)
        }
        // TC-Proj
        PlaceExpr::Proj(tuple_expr, n) => proj_expr_ty_mem_passed_prvs_under_exec_own(
            gl_ctx, kind_ctx, ty_ctx, exec, own, tuple_expr, *n,
        ),
        // TC-Deref
        PlaceExpr::Deref(borr_expr) => deref_expr_ty_mem_passed_prvs_under_exec_own(
            gl_ctx, kind_ctx, ty_ctx, exec, own, borr_expr,
        ),
    }
}

fn var_expr_ty_mem_empty_prvs_under_exec_own(
    gl_ctx: &GlobalCtx,
    ty_ctx: &TyCtx,
    exec: Exec,
    ident: &Ident,
) -> Result<(Ty, Option<Memory>, Vec<Provenance>), String> {
    let ty = if let Ok(tty) = ty_ctx.ident_ty(&ident) {
        tty
    } else {
        gl_ctx.fun_ty_by_name(&ident.name)?
    };

    match ty {
        Ty::Data(dty) => {
            if !dty.is_fully_alive() {
                return Err(format!(
                    "The value in this identifier `{}` has been moved out.",
                    ident
                ));
            }
            let mem = default_mem_by_exec(exec);
            return Ok((ty.clone(), mem, vec![]));
        }
        Ty::View(vty) => {
            if !vty.is_fully_alive() {
                return Err("The value in this identifier has been moved out.".to_string());
            }
            return Ok((ty.clone(), None, vec![]));
        }
        fty @ Ty::Fn(_, _, _, _) => {
            if !fty.is_fully_alive() {
                panic!("This should never happen.")
            }
            return Ok((ty.clone(), None, vec![]));
        }
        // TODO this is probably wrong, should probably succeed instead
        //  but not in all cases. as long as these functions return the accessed memory region,
        //  the type MUST be known to do so.
        Ty::Ident(ident) => panic!("Identifier {} found. Expected instantiated type.", ident),
    }
}

fn default_mem_by_exec(exec: Exec) -> Option<Memory> {
    match exec {
        Exec::CpuThread => Some(Memory::CpuStack),
        Exec::GpuThread => Some(Memory::GpuLocal),
        Exec::GpuGrid | Exec::GpuBlock | Exec::GpuWarp | Exec::View => None,
    }
}

fn proj_expr_ty_mem_passed_prvs_under_exec_own(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: &TyCtx,
    exec: Exec,
    own: Ownership,
    tuple_expr: &PlaceExpr,
    n: usize,
) -> Result<(Ty, Option<Memory>, Vec<Provenance>), String> {
    let (pl_expr_ty, mem, passed_prvs) = place_expr_ty_mem_passed_prvs_under_exec_own(
        gl_ctx, kind_ctx, ty_ctx, exec, own, tuple_expr,
    )?;
    match pl_expr_ty {
        Ty::Data(DataTy::Tuple(elem_dtys)) => {
            if let Some(ty) = elem_dtys.get(n) {
                Ok((Ty::Data(ty.clone()), mem, passed_prvs))
            } else {
                Err("Trying to access non existing tuple element.".to_string())
            }
        }
        Ty::View(ViewTy::Tuple(elem_tys)) => {
            if let Some(ty) = elem_tys.get(n) {
                let mem = if let Ty::Data(_) = ty {
                    default_mem_by_exec(exec)
                } else {
                    None
                };
                Ok((ty.clone(), mem, passed_prvs))
            } else {
                Err("Trying to access non existing tuple element.".to_string())
            }
        }
        Ty::Ident(_) => {
            Err("Type unspecified. Cannot project from potentially non tuple type.".to_string())
        }
        _ => Err("Trying to project from non tuple value.".to_string()),
    }
}

fn deref_expr_ty_mem_passed_prvs_under_exec_own(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: &TyCtx,
    exec: Exec,
    own: Ownership,
    borr_expr: &PlaceExpr,
) -> Result<(Ty, Option<Memory>, Vec<Provenance>), String> {
    let (pl_expr_ty, _, mut passed_prvs) = place_expr_ty_mem_passed_prvs_under_exec_own(
        gl_ctx, kind_ctx, ty_ctx, exec, own, borr_expr,
    )?;
    if let Ty::Data(DataTy::Ref(prv, ref_own, mem, dty)) = pl_expr_ty {
        if ref_own < own {
            return Err("Trying to dereference and mutably use a shrd reference.".to_string());
        }
        let outl_rels = passed_prvs.iter().map(|passed_prv| (&prv, passed_prv));
        subty::multiple_outlives(kind_ctx, ty_ctx.clone(), outl_rels)?;
        accessible_memory(exec, &mem)?;
        passed_prvs.push(prv);
        Ok((Ty::Data(*dty), Some(mem), passed_prvs))
    } else {
        Err("Trying to dereference non reference type.".to_string())
    }
}

fn accessible_memory(exec: Exec, mem: &Memory) -> Result<(), String> {
    let gpu_exec_to_mem = vec![
        (Exec::CpuThread, Memory::CpuStack),
        (Exec::CpuThread, Memory::CpuHeap),
        (Exec::GpuThread, Memory::GpuGlobal),
        (Exec::GpuThread, Memory::GpuShared),
    ];

    if gpu_exec_to_mem.contains(&(exec, mem.clone())) {
        Ok(())
    } else {
        Err(format!(
            "Trying to dereference pointer to `{}` from execution resource `{}`",
            mem, exec
        ))
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_dummy_fun() -> Result<(), String> {
        let dummy_fun_src = r#"fn dummy_fun<a: prv>(
            h_array: &a uniq cpu.heap [i32; 4096]
        ) -[cpu.thread]-> [i32; 3] {
            let answer_to_everything = [1,2,42];
            answer_to_everything
        }"#;

        let mut compil_unit = crate::parser::parse_compil_unit(dummy_fun_src).unwrap();
        super::ty_check(&mut compil_unit)?;
        print!("{:?}", compil_unit[0]);
        Ok(())
    }
}
