mod cu_ast;
mod printer;

use  super::utils;
use crate::ast as desc;
use crate::ast::{CompilUnit, Ident, PlaceExprKind, ThreadHierchyTy};
use cu_ast as cu;
use std::collections::HashMap;
use std::iter;


// FIXME Indexing and genreation of view expressions is bugged. Mainly because it is hard to
//  recognize which part of a place expression is a view expression.

// Precondition. all function defitions are successfully typechecked and
// therefore every subexpression stores a type
pub fn gen(compil_unit: &CompilUnit) -> String {
    let preproc_fun_defs = compil_unit
        .fun_defs
        .to_vec()
        .into_iter()
        .map(replace_arg_kinded_idents)
        .map(|f| inline_par_for_funs(f, &compil_unit.fun_defs))
        // preprocessed fun defs must be collected before filtering, otherwise the lazy evaluation
        //  will not apply replace_arg_kinded_idents to the filtered out fun defs
        .collect::<Vec<desc::FunDef>>();
    let fun_defs_to_be_generated = preproc_fun_defs
        .iter()
        .filter(|f| {
            f.param_decls.iter().all(|p| {
                !matches!(&p.ty.ty, desc::TyKind::View(_))
                    && !matches!(&p.ty.ty, desc::TyKind::ThreadHierchy(_))
            })
        })
        .cloned()
        .collect::<Vec<desc::FunDef>>();
    let cu_program = std::iter::once(cu::Item::Include("descend.cuh".to_string()))
        .chain(
            fun_defs_to_be_generated
                .iter()
                .map(|fun_def| gen_fun_def(fun_def, &preproc_fun_defs)),
        )
        .collect::<cu::CuProgram>();
    printer::print(&cu_program)
}

enum CheckedStmt {
    Stmt(cu::Stmt),
    StmtIdxCheck(cu::Stmt, cu::Stmt),
}

enum CheckedExpr {
    Expr(cu::Expr),
    ExprIdxCheck(cu::Stmt, cu::Expr),
}

impl CheckedExpr {
    fn map<F>(&self, f: F) -> Self
    where
        F: Fn(cu::Expr) -> cu::Expr,
    {
        match self {
            Self::Expr(e) => Self::Expr(f(e.clone())),
            Self::ExprIdxCheck(c, e) => Self::ExprIdxCheck(c.clone(), f(e.clone())),
        }
    }
}

fn gen_fun_def(gl_fun: &desc::FunDef, comp_unit: &[desc::FunDef]) -> cu::Item {
    let desc::FunDef {
        name,
        generic_params: ty_idents,
        param_decls: params,
        ret_dty: ret_ty,
        exec,
        body_expr,
        ..
    } = gl_fun;

    cu::Item::FunDef {
        name: name.clone(),
        templ_params: gen_templ_params(ty_idents),
        params: gen_param_decls(params),
        ret_ty: gen_ty(&desc::TyKind::Data(ret_ty.clone()), desc::Mutability::Mut),
        body: match gen_stmt(
            body_expr,
            !matches!(ret_ty, desc::DataTy::Scalar(desc::ScalarTy::Unit)),
            &mut HashMap::new(),
            &mut HashMap::new(),
            comp_unit,
            None,
        ) {
            CheckedStmt::Stmt(s) => s,
            CheckedStmt::StmtIdxCheck(_, _) => panic!("here should not be checks needed anymore"),
        },
        is_dev_fun: is_dev_fun(*exec),
    }
}

// Generate CUDA code for Descend syntax that allows sequencing.
fn gen_stmt(
    expr: &desc::Expr,
    return_value: bool,
    parall_ctx: &mut HashMap<String, ParallelityCollec>,
    view_ctx: &mut HashMap<String, ViewExpr>,
    comp_unit: &[desc::FunDef],
    label: Option<String>,
) -> CheckedStmt {
    use desc::ExprKind::*;
    match &expr.expr {
        Let(mutbl, ident, _, e1, e2) => {
            // Let View
            if matches!(&e1.ty.as_ref().unwrap().ty, desc::TyKind::View(_)) {
                if let Some(old) =
                    view_ctx.insert(ident.name.clone(), ViewExpr::create_from(e1, view_ctx))
                {
                    panic!(
                        "Reassigning view expression variable from `{i} = {old:?}` to `{i} = {new:?}`",
                        i = ident.name,
                        old = old,
                        new = ViewExpr::create_from(e1, view_ctx)
                    )
                }
                gen_stmt(e2, return_value, parall_ctx, view_ctx, comp_unit, label)
            // Let Expression
            } else if is_parall_collec_ty(e1.ty.as_ref().unwrap()) {
                if let Some(old) = parall_ctx.insert(
                    ident.name.clone(),
                    ParallelityCollec::create_from(e1, parall_ctx),
                ) {
                    panic!(
                        "Reassigning parallel collection expression identifier from `{i} = {old:?}` to `{i} = {new:?}`",
                        i = ident.name,
                        old = old,
                        new = ParallelityCollec::create_from(e1, parall_ctx)
                    )
                }
                gen_stmt(e2, return_value, parall_ctx, view_ctx, comp_unit, label)
            } else if let desc::TyKind::Data(desc::DataTy::At(dty, desc::Memory::GpuShared)) =
                &e1.ty.as_ref().unwrap().ty
            {
                let cu_ty = if let desc::DataTy::Array(elem_dty, n) = dty.as_ref() {
                    cu::Ty::CArray(
                        Box::new(gen_ty(
                            &desc::TyKind::Data(elem_dty.as_ref().clone()),
                            *mutbl,
                        )),
                        n.clone(),
                    )
                } else {
                    gen_ty(&desc::TyKind::Data(dty.as_ref().clone()), *mutbl)
                };
                let var = cu::Stmt::VarDecl {
                    name: ident.name.clone(),
                    ty: cu_ty,
                    addr_space: Some(cu::GpuAddrSpace::Shared),
                    expr: None,
                };
                CheckedStmt::Stmt(cu::Stmt::Seq(
                    Box::new(var),
                    match gen_stmt(e2, return_value, parall_ctx, view_ctx, comp_unit, label) {
                        CheckedStmt::StmtIdxCheck(ch, st) => {
                            Box::new(cu::Stmt::Seq(Box::new(ch), Box::new(st)))
                        }
                        CheckedStmt::Stmt(st) => Box::new(st),
                    },
                ))
            } else {
                //if has_generatable_ty(e1) {
                let gened_ty = gen_ty(&e1.ty.as_ref().unwrap().ty, *mutbl);
                let (init_expr, cu_ty, checks) = match gened_ty {
                    cu::Ty::Array(_, _) => {
                        let (ex, ch) = match gen_expr(e1, parall_ctx, view_ctx, comp_unit, label.clone()) {
                            CheckedExpr::Expr(e) => (e, None),
                            CheckedExpr::ExprIdxCheck(c, e) => (e, Some(c)),
                        };
                        (ex, gened_ty, ch)
                    }
                    _ => {
                        let (ex, ch) = match gen_expr(e1, parall_ctx, view_ctx, comp_unit, label.clone()) {
                            CheckedExpr::Expr(e) => (e, None),
                            CheckedExpr::ExprIdxCheck(c, e) => (e, Some(c)),
                        };
                        (
                            ex,
                            if *mutbl == desc::Mutability::Mut {
                                cu::Ty::Scalar(cu::ScalarTy::Auto)
                            } else {
                                cu::Ty::Const(Box::new(cu::Ty::Scalar(cu::ScalarTy::Auto)))
                            },
                            ch,
                        )
                    }
                };
                let var = cu::Stmt::VarDecl {
                    name: ident.name.clone(),
                    ty: cu_ty,
                    addr_space: None,
                    expr: Some(init_expr),
                };
                match (
                    checks,
                    gen_stmt(e2, return_value, parall_ctx, view_ctx, comp_unit, label),
                ) {
                    (None, CheckedStmt::Stmt(st)) => {
                        CheckedStmt::Stmt(cu::Stmt::Seq(Box::new(var), Box::new(st)))
                    }
                    (Some(ch), CheckedStmt::Stmt(st)) => {
                        CheckedStmt::Stmt(build_seq(vec![ch, var, st]))
                    },
                    (None, CheckedStmt::StmtIdxCheck(ch, st)) => {
                        CheckedStmt::Stmt(build_seq(vec![var, ch, st]))
                    },
                    (Some(ch1), CheckedStmt::StmtIdxCheck(ch2, st)) => {
                        CheckedStmt::Stmt(build_seq(vec![ch1, var, ch2, st]))
                    }
                }
            } // else {
              //     gen_stmt(e2, return_value, parall_ctx, view_ctx, comp_unit)
              // }
        }
        LetUninit(ident, ty, e) => CheckedStmt::Stmt(cu::Stmt::Seq(
            Box::new(cu::Stmt::VarDecl {
                name: ident.name.clone(),
                ty: gen_ty(&ty.as_ref().ty, desc::Mutability::Mut),
                addr_space: None,
                expr: None,
            }),
            match gen_stmt(e, return_value, parall_ctx, view_ctx, comp_unit, label) {
                CheckedStmt::StmtIdxCheck(ch, st) => {
                    Box::new(cu::Stmt::Seq(Box::new(ch), Box::new(st)))
                }
                CheckedStmt::Stmt(st) => Box::new(st),
            }, // Box::new(gen_stmt(e, return_value, parall_ctx, view_ctx, comp_unit)),
        )),
        LetProv(_, expr) => gen_stmt(expr, return_value, parall_ctx, view_ctx, comp_unit, label),
        // e1 ; e2
        Seq(e1, e2) => {
            match (
                gen_stmt(e1, false, parall_ctx, view_ctx, comp_unit, label.clone()),
                gen_stmt(e2, return_value, parall_ctx, view_ctx, comp_unit, label),
            ) {
                (CheckedStmt::StmtIdxCheck(ch1, st1), CheckedStmt::StmtIdxCheck(ch2, st2)) => {
                    CheckedStmt::Stmt(build_seq(vec![ch1, st1, ch2, st2]))
                }
                (CheckedStmt::StmtIdxCheck(ch, st1), CheckedStmt::Stmt(st2)) => {
                    CheckedStmt::Stmt(build_seq(vec![ch, st1, st2]))
                }
                (CheckedStmt::Stmt(st1), CheckedStmt::StmtIdxCheck(ch, st2)) => {
                    CheckedStmt::Stmt(build_seq(vec![st1, ch, st2]))
                }
                (CheckedStmt::Stmt(st1), CheckedStmt::Stmt(st2)) => {
                    CheckedStmt::Stmt(cu::Stmt::Seq(Box::new(st1), Box::new(st2)))
                }
            }
        }
        ForNat(ident, range, body) => {
            let i = cu::Expr::Ident(ident.name.clone());
            let (init, cond, iter) = match range {
                desc::Nat::App(r_name, input) => {
                    let (init_decl, cond, iter) = match r_name.name.as_str() {
                        "halved_range" => {
                            let init_decl = cu::Stmt::VarDecl {
                                name: ident.name.clone(),
                                ty: cu::Ty::Scalar(cu::ScalarTy::I32),
                                addr_space: None,
                                expr: Some(cu::Expr::Nat(input[0].clone())),
                            };
                            let cond = cu::Expr::BinOp {
                                op: cu::BinOp::Gt,
                                lhs: Box::new(i.clone()),
                                rhs: Box::new(cu::Expr::Lit(cu::Lit::I32(0))),
                            };
                            let iter = cu::Expr::Assign {
                                lhs: Box::new(i.clone()),
                                rhs: Box::new(cu::Expr::BinOp {
                                    op: cu::BinOp::Div,
                                    lhs: Box::new(i),
                                    rhs: Box::new(cu::Expr::Lit(cu::Lit::I32(2))),
                                }),
                            };
                            (init_decl, cond, iter)
                        }
                        "doubled_range" => {
                            let init_decl = cu::Stmt::VarDecl {
                                name: ident.name.clone(),
                                ty: cu::Ty::Scalar(cu::ScalarTy::I32),
                                addr_space: None,
                                expr: Some(cu::Expr::Lit(cu::Lit::I32(1))),
                            };
                            let cond = cu::Expr::BinOp {
                                op: cu::BinOp::Le,
                                lhs: Box::new(i.clone()),
                                rhs: Box::new(cu::Expr::Nat(input[0].clone())),
                            };
                            let iter = cu::Expr::Assign {
                                lhs: Box::new(i.clone()),
                                rhs: Box::new(cu::Expr::BinOp {
                                    op: cu::BinOp::Mul,
                                    lhs: Box::new(i),
                                    rhs: Box::new(cu::Expr::Lit(cu::Lit::I32(2))),
                                }),
                            };
                            (init_decl, cond, iter)
                        }
                        _ => unimplemented!(),
                    };
                    (init_decl, cond, iter)
                }
                _ => panic!("Currently ranges are assumed to be predeclared functions."),
            };

            CheckedStmt::Stmt(cu::Stmt::ForLoop {
                init: Box::new(init),
                cond,   // TODO needs some kind of checking
                iter,
                stmt:match gen_stmt(
                    body, false, parall_ctx, view_ctx, comp_unit, label,
                ) {
                    CheckedStmt::Stmt(st) => Box::new(cu::Stmt::Block(Box::new(st))),
                    CheckedStmt::StmtIdxCheck(_, _) => panic!("body of for-loop should not have to be checked")
                }
                    // Box::new(cu::Stmt::Block(Box::new(gen_stmt(
                    //     body, false, parall_ctx, view_ctx, comp_unit,
                    // )))),
            })
        }
        While(cond, body) => CheckedStmt::Stmt(cu::Stmt::While {
            cond: match gen_expr(cond, parall_ctx, view_ctx, comp_unit, label.clone()) {
                CheckedExpr::Expr(expr) => expr,
                CheckedExpr::ExprIdxCheck(_, expr) => {
                    println!("found a condition in while-loop which needs checks!"); // TODO implement checks
                    expr
                }
            },
            stmt: match gen_stmt(body, false, parall_ctx, view_ctx, comp_unit, label) {
                CheckedStmt::Stmt(st) => Box::new(cu::Stmt::Block(Box::new(st))),
                CheckedStmt::StmtIdxCheck(_, _) => 
                    panic!("body of while-loop should not have to be checked")
            }
            // Box::new(cu::Stmt::Block(Box::new(gen_stmt(
            //     body, false, parall_ctx, view_ctx, comp_unit,
            // )))),
        }),
        For(ident, coll_expr, body) => CheckedStmt::Stmt(gen_for_each(
            ident, coll_expr, body, parall_ctx, view_ctx, comp_unit, label,
        )),
        ParFor(parall_collec, input, funs) => CheckedStmt::Stmt(gen_par_for(
            parall_collec,
            input,
            funs,
            parall_ctx,
            view_ctx,
            comp_unit,
            label,
        )),
        // FIXME this assumes that IfElse is not an Expression.
        IfElse(cond, e_tt, e_ff) => {
            match gen_expr(cond, parall_ctx, view_ctx, comp_unit, label.clone()) {
                CheckedExpr::ExprIdxCheck(check, con) => {
                    CheckedStmt::Stmt(cu::Stmt::Seq(
                        Box::new(check),
                        Box::new(gen_if_else(con, e_tt, e_ff, parall_ctx, view_ctx, comp_unit, label))
                    ))
                },
                CheckedExpr::Expr(con) => CheckedStmt::Stmt(
                    gen_if_else(con, e_tt, e_ff, parall_ctx, view_ctx, comp_unit, label)
                )
            }
        },
        //gen_if_else(cond, e_tt, e_ff, parall_ctx, view_ctx, comp_unit),
        _ => {
            if return_value {
                match gen_expr(&expr, parall_ctx, view_ctx, comp_unit, label) {
                    CheckedExpr::Expr(e) => CheckedStmt::Stmt(cu::Stmt::Return(Some(e))),
                    CheckedExpr::ExprIdxCheck(ch, e) => {
                        CheckedStmt::StmtIdxCheck(ch, cu::Stmt::Return(Some(e)))
                    }
                }
            } else {
                match gen_expr(&expr, parall_ctx, view_ctx, comp_unit, label) {
                    CheckedExpr::Expr(e) => CheckedStmt::Stmt(cu::Stmt::Expr(e)),
                    CheckedExpr::ExprIdxCheck(ch, e) => {
                        CheckedStmt::StmtIdxCheck(ch, cu::Stmt::Expr(e))
                    }
                }
            }
        }
    }
}

fn has_generatable_ty(e: &desc::Expr) -> bool {
    matches!(&e.ty.as_ref().unwrap().ty, desc::TyKind::Ident(_))
        || matches!(&e.ty.as_ref().unwrap().ty, desc::TyKind::Data(_))
}

fn gen_if_else(
    cond: cu_ast::Expr,
    e_tt: &desc::Expr,
    e_ff: &desc::Expr,
    parall_ctx: &mut HashMap<String, ParallelityCollec>,
    view_ctx: &mut HashMap<String, ViewExpr>,
    comp_unit: &[desc::FunDef],
    label: Option<String>
) -> cu::Stmt {
    cu::Stmt::IfElse{
        cond: cond,
        true_body: match gen_stmt(e_tt, false, parall_ctx, view_ctx, comp_unit, label.clone()) {
            CheckedStmt::Stmt(st) => Box::new(st),
            CheckedStmt::StmtIdxCheck(_, _) => {
                panic!("body of true-case of if-else should not need checks")
            }
        },
        false_body: match gen_stmt(e_ff, false, parall_ctx, view_ctx, comp_unit, label) {
            CheckedStmt::Stmt(st) => Box::new(st),
            CheckedStmt::StmtIdxCheck(_, _) => {
                panic!("body of false-case of if-else should not need checks")
            }
        },
    }
}

fn gen_for_each(
    ident: &Ident,
    coll_expr: &desc::Expr,
    body: &desc::Expr,
    parall_ctx: &mut HashMap<String, ParallelityCollec>,
    view_ctx: &mut HashMap<String, ViewExpr>,
    comp_unit: &[desc::FunDef],
    label: Option<String>
) -> cu::Stmt {
    let i_name = crate::utils::fresh_name("_i_");
    let i_decl = cu::Stmt::VarDecl {
        name: i_name.clone(),
        ty: cu::Ty::Scalar(cu::ScalarTy::SizeT),
        addr_space: None,
        expr: Some(cu::Expr::Lit(cu::Lit::I32(0))),
    };
    let i = cu::Expr::Ident(i_name.to_string());
    let mut scoped_view_ctx = view_ctx.clone();
    scoped_view_ctx.insert(
        ident.name.clone(),
        ViewExpr::Idx {
            idx: desc::Nat::Ident(Ident::new(&i_name)),
            view: Box::new(ViewExpr::ToView {
                ref_expr: Box::new(coll_expr.clone()),
            }),
        },
    );
    cu::Stmt::ForLoop {
        init: Box::new(i_decl),
        cond: cu::Expr::BinOp {
            op: cu::BinOp::Lt,
            lhs: Box::new(i.clone()),
            rhs: Box::new(cu::Expr::Nat(
                extract_size(coll_expr.ty.as_ref().unwrap()).unwrap(),
            )),
        },
        iter: cu::Expr::Assign {
            lhs: Box::new(i.clone()),
            rhs: Box::new(cu::Expr::BinOp {
                op: cu::BinOp::Add,
                lhs: Box::new(i),
                rhs: Box::new(cu::Expr::Lit(cu::Lit::I32(1))),
            }),
        },
        stmt: match gen_stmt(body, false, parall_ctx, &mut scoped_view_ctx, comp_unit, label) {
            CheckedStmt::Stmt(st) => Box::new(cu::Stmt::Block(Box::new(st))),
            CheckedStmt::StmtIdxCheck(_, _) => panic!("this should not happen"),
        },
        //  Box::new(cu::Stmt::Block(Box::new(gen_stmt(
        //     body,
        //     false,
        //     parall_ctx,
        //     &mut scoped_view_ctx,
        //     comp_unit,
        // )))),
    }
}

fn gen_exec(
    blocks: &desc::ArgKinded,
    threads: &desc::ArgKinded,
    gpu_expr: &desc::Expr,
    view_expr: &desc::Expr,
    fun: &desc::Expr,
    view_ctx: &mut HashMap<String, ViewExpr>,
    comp_unit: &[desc::FunDef],
    label: Option<String>,
) -> CheckedExpr {
    // Prepare parameter declarations for inputs
    let mut input_view_expr = ViewExpr::create_from(view_expr, view_ctx);
    let name_to_exprs = input_view_expr.collect_and_rename_input_exprs();
    let param_decls: Vec<_> = name_to_exprs
        .iter()
        .map(|(name, expr)| cu::ParamDecl {
            name: name.clone(),
            // TODO why Mutability::Const??!
            ty: gen_ty(&expr.ty.as_ref().unwrap().ty, desc::Mutability::Const),
        })
        .collect();

    // GPU argument
    let gpu = match gen_expr(
        gpu_expr,
        &mut HashMap::new(),
        &mut HashMap::new(),
        comp_unit,
        None,
    ) {
        CheckedExpr::Expr(e) => e,
        CheckedExpr::ExprIdxCheck(_, _) => {
            panic!("Did not expect to check a condition for GPU")
        }
    };

    // FIXME only allows Lambdas
    let dev_fun = if let desc::ExprKind::Lambda(params, _, _, body) = &fun.expr {
        let parall_collec = params[0].ident.clone();
        let mut scope_parall_ctx: HashMap<String, ParallelityCollec> = HashMap::new();
        scope_parall_ctx.insert(
            parall_collec.name.clone(),
            ParallelityCollec::Ident(parall_collec),
        );

        // Remember to inline input view expression
        let in_name = params[1].ident.name.clone();
        view_ctx.insert(in_name, input_view_expr);

        cu::Expr::Lambda {
            params: param_decls,
            body: match gen_stmt(&body, false, &mut scope_parall_ctx, view_ctx, comp_unit, label.clone()) {
                CheckedStmt::Stmt(st) => Box::new(st),
                CheckedStmt::StmtIdxCheck(_, _) => panic!("this should never happen"),
            },
            ret_ty: cu::Ty::Scalar(cu::ScalarTy::Void),
            is_dev_fun: true,
        }
    } else {
        panic!("Currently only lambdas can be passed.")
    };
    let mut checks: Vec<cu::Stmt> = vec![];
    let mut input: Vec<_> = name_to_exprs
        .iter()
        .map(|(_, pl_expr)| {
            match gen_expr(pl_expr, &mut HashMap::new(), &mut HashMap::new(), comp_unit, label.clone()) {
                CheckedExpr::Expr(expr) => expr,
                CheckedExpr::ExprIdxCheck(check, expr) => {
                    checks.push(check);
                    expr
                },
            }
        })
        .collect();
    let template_args = gen_args_kinded(vec![blocks.clone(), threads.clone()].as_slice());
    let mut args: Vec<cu::Expr> = vec![gpu, dev_fun];
    args.append(&mut input);

    if checks.is_empty() {
        CheckedExpr::Expr(
            cu::Expr::FunCall {
                fun: Box::new(cu::Expr::Ident("descend::exec".to_string())),
                template_args,
                args,
            }
        )
    } else if checks.len() == 1{
        CheckedExpr::ExprIdxCheck(
            checks.pop().unwrap(),
            cu::Expr::FunCall {
                fun: Box::new(cu::Expr::Ident("descend::exec".to_string())),
                template_args,
                args,
            }
        )
    } else {
        CheckedExpr::ExprIdxCheck(
            build_seq(checks),
            cu::Expr::FunCall {
                fun: Box::new(cu::Expr::Ident("descend::exec".to_string())),
                template_args,
                args,
            }
        )
    }
}

fn gen_par_for(
    parall_collec: &desc::Expr,
    input: &desc::Expr,
    funs: &desc::Expr,
    parall_ctx: &mut HashMap<String, ParallelityCollec>,
    view_ctx: &mut HashMap<String, ViewExpr>,
    comp_unit: &[desc::FunDef],
    label: Option<String>,
) -> cu::Stmt {
    fn gen_parall_section(
        has_th_hierchy_elem_ty: bool,
        params: &[desc::ParamDecl],
        body: &desc::Expr,
        input_expr: &desc::Expr,
        pid: &desc::Nat,
        view_ctx: &mut HashMap<String, ViewExpr>,
        comp_unit: &[desc::FunDef],
        label: Option<String>,
    ) -> cu::Stmt {
        let mut offset_begin_input_params = 0;
        let mut scope_parall_ctx: HashMap<String, ParallelityCollec> = HashMap::new();
        if has_th_hierchy_elem_ty {
            let parall_collec = params[0].ident.clone();
            scope_parall_ctx.insert(
                parall_collec.name.clone(),
                ParallelityCollec::Ident(parall_collec),
            );
            offset_begin_input_params += 1;
        }

        //        let mut new_body = body.clone();
        for (i, id) in params[offset_begin_input_params..]
            .iter()
            .map(|p| p.ident.name.clone())
            .enumerate()
        {
            let input_arg_view = ViewExpr::create_from(
                &desc::Expr::new(desc::ExprKind::Proj(Box::new(input_expr.clone()), i)),
                view_ctx,
            );

            if let desc::TyKind::View(desc::ViewTy::Tuple(elem_tys)) =
                &input_expr.ty.as_ref().unwrap().ty
            {
                if let desc::TyKind::View(_) = &elem_tys[i].ty {
                    view_ctx.insert(
                        id.clone(),
                        ViewExpr::Idx {
                            idx: pid.clone(),
                            view: Box::new(input_arg_view),
                        },
                    );
                } else {
                    // FIXME Leads to stackoverflow if the same names are used
                    //  as input elemenent (input_arg_view) and identifier (id)
                    view_ctx.insert(id, input_arg_view);
                }
            } else {
                panic!("Inputs to par_for are always tuple views.")
            }
        }

        let l = match label.clone() {
            None => {
                utils::fresh_name("label")
            },
            Some(l) => l,
        };
        match gen_stmt(
            body,
            false, 
            &mut scope_parall_ctx, 
            view_ctx, 
            comp_unit, 
            Some(l)
        ) {
            CheckedStmt::Stmt(st) => st,
            CheckedStmt::StmtIdxCheck(ch, st) => {
                cu::Stmt::Seq(
                    Box::new(ch),
                    Box::new(st),
                )
            },
        }
    }

    let (pid, sync_stmt, has_th_hierchy_elem) = match &parall_collec.ty.as_ref().unwrap().ty {
        // TODO Refactor
        //  The same things exists in ty_check where only threadHierchyTy for elem types is returned
        desc::TyKind::ThreadHierchy(th_hy) => match th_hy.as_ref() {
            desc::ThreadHierchyTy::BlockGrp(_, _, _, m1, m2, m3) => (
                desc::Nat::Ident(desc::Ident::new("blockIdx.x")),
                cu::Stmt::Expr(cu::Expr::Empty),
                true,
            ),
            desc::ThreadHierchyTy::ThreadGrp(_, _, _) => (
                desc::Nat::Ident(desc::Ident::new("threadIdx.x")),
                build_seq(vec![
                    cu::Stmt::Label(match label.clone() {
                        Some(l) => l,
                        None => panic!("exptected label!")
                    }),
                    cu::Stmt::Expr(cu::Expr::FunCall {
                        fun: Box::new(cu::Expr::Ident("__syncthreads".to_string())),
                        template_args: vec![],
                        args: vec![],
                    }),
                    cu::Stmt::If{
                        cond: cu::Expr::BinOp{
                            op: cu::BinOp::Neq,
                            lhs: Box::new(cu::Expr::Ident("global_failure".to_string())),
                            rhs: Box::new(cu::Expr::Lit(cu::Lit::I32(-1))),
                        },
                        body: Box::new(cu::Stmt::Block(
                            Box::new(cu::Stmt::Return(None)),
                        ))
                    },
                    cu::Stmt::Expr(cu::Expr::FunCall {
                        fun: Box::new(cu::Expr::Ident("__syncthreads".to_string())),
                        template_args: vec![],
                        args: vec![],
                    })
                ]),
                false,
            ),
            desc::ThreadHierchyTy::WarpGrp(_) => (
                desc::Nat::BinOp(
                    desc::BinOpNat::Div,
                    Box::new(desc::Nat::Ident(desc::Ident::new("threadIdx.x"))),
                    Box::new(desc::Nat::Lit(32)),
                ),
                cu::Stmt::Expr(cu::Expr::FunCall {
                    fun: Box::new(cu::Expr::Ident("__syncthreads".to_string())),
                    template_args: vec![],
                    args: vec![],
                }),
                true,
            ),
            desc::ThreadHierchyTy::Warp => (
                desc::Nat::BinOp(
                    desc::BinOpNat::Mod,
                    Box::new(desc::Nat::Ident(desc::Ident::new("threadIdx.x"))),
                    Box::new(desc::Nat::Lit(32)),
                ),
                cu::Stmt::Expr(cu::Expr::FunCall {
                    fun: Box::new(cu::Expr::Ident("__syncwarp()".to_string())),
                    template_args: vec![],
                    args: vec![],
                }),
                false,
            ),
        },
        _ => panic!("Not a parallel collection type."),
    };

    // FIXME this assumes that the only functions given are syntactically lambdas
    let par_section = match &funs.ty.as_ref().unwrap().ty {
        desc::TyKind::View(desc::ViewTy::Tuple(_)) => unimplemented!(),
        desc::TyKind::Fn(_, _, _, _) => match &funs.expr {
            desc::ExprKind::Lambda(params, _, _, body) => gen_parall_section(
                has_th_hierchy_elem,
                params,
                body,
                input,
                &pid,
                view_ctx,
                comp_unit,
                label,
            ),
            desc::ExprKind::DepApp(fun, gen_args) => {
                let ident = extract_ident(fun);
                let fun_def = comp_unit
                    .iter()
                    .find(|fun_def| fun_def.name == ident.name)
                    .expect("Cannot find function definition.");
                if let desc::ExprKind::Lambda(params, _, _, body) =
                    partial_app_gen_args(fun_def, gen_args).expr
                {
                    gen_parall_section(
                        has_th_hierchy_elem,
                        &params,
                        body.as_ref(),
                        input,
                        &pid,
                        view_ctx,
                        comp_unit,
                        label,
                    )
                } else {
                    panic!("instatiate_gen_fun did not return a lambda expression")
                }
            }
            _ => panic!("No function supplied."),
        },
        desc::TyKind::Data(_) => {
            panic!("Cannot generate function body from expression of data type.")
        }
        _ => panic!("Expected Lambda or tuple view of Lambda."),
    };

    let p = ParallelityCollec::create_from(parall_collec, parall_ctx);
    let body = if let Some((Some(parall_cond), _)) = gen_parall_cond(&pid, &p) {
        cu::Stmt::If {
            cond: parall_cond,
            body: Box::new(cu::Stmt::Block(Box::new(par_section))),
        }
    } else {
        par_section
    };

    cu::Stmt::Seq (
        Box::new(body),
        Box::new(sync_stmt),
    )
}

fn build_seq(mut stmts: Vec<cu::Stmt>) -> cu::Stmt {
    if stmts.len() <= 1 {
        panic!("needs at least two stmts");
    } else if stmts.len() == 2 {
        cu::Stmt::Seq(
            Box::new(stmts.remove(0)),
            Box::new(stmts.remove(0)),
        )
    } else {
        cu::Stmt::Seq(
            Box::new(stmts.remove(0)),
            Box::new(build_seq(stmts)),
        )
    }
}

fn gen_checked_stmt(
    expr: &desc::Expr,
    view_ctx: &mut HashMap<String, ViewExpr>,
    comp_unit: &[desc::FunDef],
    label: Option<String>,
) -> cu::Stmt {
    use desc::ExprKind::*;
    match &expr.expr {
        Let(_, _, _, expr1, expr2) => cu::Stmt::Seq(
            Box::new(gen_checked_stmt(expr1, view_ctx, comp_unit, label.clone())),
            Box::new(gen_checked_stmt(expr2, view_ctx, comp_unit, label)),
        ),
        //gen_checked_stmt(expr1, view_ctx, comp_unit, label), //TODO call on other expr of let
        Seq(e1, e2) => {
            cu::Stmt::Seq(
                Box::new(gen_checked_stmt(e1, view_ctx, comp_unit, label.clone())),
                Box::new(gen_checked_stmt(e2, view_ctx, comp_unit, label))
            )
        }
        Index(pl_expr, i) => {
            match label {
                Some(l) => {
                    let n = match &pl_expr.ty.as_ref().expect(&format!("{:?}", pl_expr)).ty {
                        TyKind::Data(DataTy::Array(_, m)) => m,
                        TyKind::Data(DataTy::Ref(_, _, _, a)) => if let DataTy::Array(_, m) = a.as_ref() {
                            m
                        } else {
                            panic!("cannot index into non array type!");
                        }, 
                        TyKind::View(ViewTy::Array(_, m)) => m,
                        t => panic!("cannot index into non array type!{:?}", t),
                    };
                    use crate::ast::*;
                    cu::Stmt::If{
                        cond: cu::Expr::BinOp{
                            op: cu::BinOp::Gt, 
                            lhs: Box::new(cu::Expr::Nat(i.clone())),
                            rhs: Box::new(cu::Expr::Nat(n.clone())),
                        } ,
                        body: Box::new(cu::Stmt::Block(Box::new(cu::Stmt::Expr(
                            cu::Expr::Ident(format!("goto {}", l))
                        )))) ,
                    }
                },
                None => {
                    cu::Stmt::Expr(cu::Expr::Empty)
                }
            }
           
        }
        Assign(_, expr) => gen_checked_stmt(expr, view_ctx, comp_unit, label),
        App(_, _, _) | ParFor(_, _, _) | PlaceExpr(_) | Lit(_) => cu::Stmt::Expr(cu::Expr::Empty),
        _ => panic!("Smth not yet implemented {:?}", &expr), // TODO not all cases implemented
    }
}

fn gen_expr(
    expr: &desc::Expr,
    parall_ctx: &mut HashMap<String, ParallelityCollec>,
    view_ctx: &mut HashMap<String, ViewExpr>,
    comp_unit: &[desc::FunDef],
    label: Option<String>,
) -> CheckedExpr {
    use desc::ExprKind::*;

    match &expr.expr {
        Lit(l) => CheckedExpr::Expr(gen_lit(*l)),
        PlaceExpr(pl_expr) => CheckedExpr::Expr(gen_pl_expr(pl_expr, view_ctx, comp_unit)),
        Proj(tuple, idx) => {
            if let desc::TyKind::View(_) = expr.ty.as_ref().unwrap().ty {
                CheckedExpr::Expr(gen_view(
                    &ViewExpr::create_from(expr, view_ctx),
                    vec![],
                    view_ctx,
                    comp_unit,
                ))
            } else {
                gen_expr(tuple, parall_ctx, view_ctx, comp_unit, label).map(|e| cu::Expr::Proj {
                    tuple: Box::new(e),
                    n: *idx,
                })
            }
        }
        BinOp(op, lhs, rhs) => gen_bin_op_expr(op, lhs, rhs, parall_ctx, view_ctx, comp_unit, label),
        UnOp(op, arg) => gen_expr(arg, parall_ctx, view_ctx, comp_unit, label).map(|e| cu::Expr::UnOp {
            op: match op {
                desc::UnOp::Deref => cu::UnOp::Deref,
                desc::UnOp::Not => cu::UnOp::Not,
                desc::UnOp::Neg => cu::UnOp::Neg,
            },
            arg: Box::new(e),
        }),
        Ref(_, _, pl_expr) => match &expr.ty.as_ref().unwrap().ty {
            desc::TyKind::Data(desc::DataTy::Ref(_, _, desc::Memory::GpuShared, _)) => {
                CheckedExpr::Expr(gen_pl_expr(pl_expr, view_ctx, comp_unit))
            }
            _ => CheckedExpr::Expr(cu::Expr::Ref(Box::new(gen_pl_expr(
                pl_expr, view_ctx, comp_unit,
            )))),
        },
        BorrowIndex(_, _, pl_expr, n) => {
            if contains_view_expr(pl_expr, view_ctx) {
                panic!("It should not be allowed to borrow from a view expression.")
            } else {
                CheckedExpr::Expr(cu::Expr::Ref(Box::new(cu::Expr::ArraySubscript {
                    array: Box::new(gen_pl_expr(pl_expr, view_ctx, comp_unit)),
                    index: n.clone(),
                })))
            }
        }
        Index(pl_expr, idx) => {
            if contains_view_expr(pl_expr, view_ctx) {
                CheckedExpr::ExprIdxCheck(
                    gen_checked_stmt(&expr, view_ctx, comp_unit, label), 
                    gen_idx_into_view(pl_expr, idx, view_ctx, comp_unit),
                )
            } else {
                CheckedExpr::ExprIdxCheck(
                    gen_checked_stmt(&expr, view_ctx, comp_unit, label), 
                    cu::Expr::ArraySubscript {
                        array: Box::new(gen_pl_expr(pl_expr, view_ctx, comp_unit)),
                        index: idx.clone(),
                    },
                )
            }
        }
        IdxAssign(pl_expr, idx, expr) => {
            gen_expr(expr, parall_ctx, view_ctx, comp_unit, label).map(|e| {
              cu::Expr::Assign {
                lhs: Box::new(if contains_view_expr(pl_expr, view_ctx) {
                    gen_idx_into_view(pl_expr, idx, &mut view_ctx.clone(), comp_unit)
                } else {
                    cu::Expr::ArraySubscript {
                        array: Box::new(gen_pl_expr(pl_expr, &mut view_ctx.clone(), comp_unit)),
                        index: idx.clone(),
                    }
                }),
                rhs: Box::new(e),
              }
            })
        }
        Assign(pl_expr, expr) => {
          gen_expr(expr, parall_ctx, view_ctx, comp_unit, label).map(
            |e| cu::Expr::Assign{
              lhs: Box::new(gen_pl_expr(pl_expr, &mut view_ctx.clone(), comp_unit)), 
              rhs: Box::new(e),
            }
          )
        },
        Lambda(params, exec, ty, expr) => CheckedExpr::Expr(cu::Expr::Lambda {
            params: gen_param_decls(params.as_slice()),
            body: match gen_stmt(
                expr,
                !matches!(ty.as_ref(), desc::DataTy::Scalar(desc::ScalarTy::Unit)),
                parall_ctx,
                view_ctx,
                comp_unit,
                label,
            ) {
                CheckedStmt::Stmt(st) => Box::new(st),
                CheckedStmt::StmtIdxCheck(_, _) => panic!("this should not happen!"),
            },
            ret_ty: gen_ty(
                &desc::TyKind::Data(ty.as_ref().clone()),
                desc::Mutability::Mut,
            ),
            is_dev_fun: is_dev_fun(*exec),
        }),
        App(fun, kinded_args, args) => match &fun.expr {
            desc::ExprKind::PlaceExpr(desc::PlaceExpr {
                kind: PlaceExprKind::Ident(name),
                ..
            }) if name.name == "exec" => gen_exec(
                &kinded_args[0],
                &kinded_args[1],
                &args[0],
                &args[1],
                &args[2],
                view_ctx,
                comp_unit,
                label,
            ),
            desc::ExprKind::PlaceExpr(desc::PlaceExpr {
                kind: PlaceExprKind::Ident(ident),
                ..
            }) if crate::ty_check::pre_decl::fun_decls()
                .iter()
                .any(|(name, _)| &ident.name == name) =>
            {
                let pre_decl_ident = desc::Ident::new(&format!("descend::{}", ident.name));
                CheckedExpr::Expr(cu::Expr::FunCall {
                    fun: Box::new(
                        match gen_expr(
                            &desc::Expr::with_type(
                                desc::ExprKind::PlaceExpr(desc::PlaceExpr::new(
                                    PlaceExprKind::Ident(pre_decl_ident),
                                )),
                                fun.ty.as_ref().unwrap().clone(),
                            ),
                            parall_ctx,
                            view_ctx,
                            comp_unit,
                            label.clone(),
                        ) {
                            CheckedExpr::Expr(expr) | CheckedExpr::ExprIdxCheck(_, expr) => expr,
                        },
                    ),
                    template_args: gen_args_kinded(kinded_args),
                    args: args
                        .iter()
                        .map(|e| match gen_expr(e, parall_ctx, view_ctx, comp_unit, label.clone()) {
                            CheckedExpr::Expr(expr) | CheckedExpr::ExprIdxCheck(_, expr) => expr,
                        })
                        .collect::<Vec<_>>(),
                })
            }
            _ => {
                let (reduced_fun, data_args, red_kinded_args) = match create_lambda_no_view_args(
                    fun.as_ref(),
                    kinded_args.as_slice(),
                    args.as_slice(),
                    parall_ctx,
                    view_ctx,
                    comp_unit,
                ) {
                    Some((reduced_fun, data_args)) => (reduced_fun, data_args, vec![]),
                    None => (*fun.clone(), args.clone(), kinded_args.clone()),
                };
                CheckedExpr::Expr(cu::Expr::FunCall {
                    fun: Box::new({
                        match gen_expr(&reduced_fun, parall_ctx, view_ctx, comp_unit, label.clone()) {
                            CheckedExpr::Expr(expr) | CheckedExpr::ExprIdxCheck(_, expr) => expr,
                        }
                    }),
                    template_args: gen_args_kinded(&red_kinded_args),
                    args: data_args
                        .iter()
                        .map(|e| match gen_expr(e, parall_ctx, view_ctx, comp_unit, label.clone()) {
                            CheckedExpr::Expr(expr) | CheckedExpr::ExprIdxCheck(_, expr) => expr,
                        })
                        .collect::<Vec<_>>(),
                })
            }
        },
        DepApp(fun, kinded_args) => {
            let ident = extract_ident(fun);
            let fun_def = comp_unit
                .iter()
                .find(|fun_def| fun_def.name == ident.name)
                .expect("Cannot find function definition.");
            let inst_fun = partial_app_gen_args(fun_def, &kinded_args);
            gen_expr(&inst_fun, parall_ctx, view_ctx, comp_unit, label)
        }
        Array(elems) => CheckedExpr::Expr(cu::Expr::InitializerList {
            elems: elems
                .iter()
                .map(|e| match gen_expr(e, parall_ctx, view_ctx, comp_unit, label.clone()) {
                    CheckedExpr::Expr(expr) => expr,
                    CheckedExpr::ExprIdxCheck(_, _) => {
                        panic!("Elements of an array should not have to be checked!")
                    }
                })
                .collect(),
        }),
        // cu::Expr::FunCall {
        //     fun: Box::new(cu::Expr::Ident("descend::create_array".to_string())),
        //     template_args: vec![],
        //     args: elems
        //         .iter()
        //         .map(|e| gen_expr(e, parall_ctx, view_ctx))
        //         .collect::<Vec<_>>(),
        // },
        Tuple(elems) => CheckedExpr::Expr(cu::Expr::Tuple(
            elems
                .iter()
                .map(|el| match gen_expr(el, parall_ctx, view_ctx, comp_unit, label.clone()) {
                    CheckedExpr::Expr(expr) => expr,
                    CheckedExpr::ExprIdxCheck(_, _) => {
                        panic!("Elements of a tuple should not have to be checked!")
                    }
                })
                .collect::<Vec<_>>(),
        )),
        Deref(e) => CheckedExpr::Expr(cu::Expr::Deref(Box::new(
            match gen_expr(e, parall_ctx, view_ctx, comp_unit, label) {
                CheckedExpr::Expr(expr) => expr,
                CheckedExpr::ExprIdxCheck(_, _) => {
                    panic!("did not expect a check after deref!")
                }
            },
        ))),
        Idx(e, i) => CheckedExpr::Expr(cu::Expr::ArraySubscript {
            array: Box::new(match gen_expr(e, parall_ctx, view_ctx, comp_unit, label) {
                CheckedExpr::Expr(expr) => expr,
                CheckedExpr::ExprIdxCheck(_, _) => panic!("should never happen"), // ?ONLY for codegen, so no check needed? 
            }),
            index: i.clone(),
        }),
        Let(_, _, _, _, _)
        | LetUninit(_, _, _)
        | LetProv(_, _)
        | IfElse(_, _, _)
        | Seq(_, _)
        | While(_, _)
        | For(_, _, _)
        | ForNat(_, _, _)
        | ParFor(_, _, _) => panic!(
            "Trying to generate a statement where an expression is expected:\n{:?}",
            &expr
        ),
        TupleView(_) => {
            panic!("All tuple views should have been deconstructed using projections by now.")
        }
    }
}

fn gen_bin_op_expr(
  op: &desc::BinOp,
  lhs: &desc::Expr,
  rhs: &desc::Expr,
  parall_ctx: &mut HashMap<String, ParallelityCollec>,
  view_ctx: &mut HashMap<String, ViewExpr>,
  comp_unit: &[desc::FunDef],
  label: Option<String>,
) -> CheckedExpr {
  {
    let op = match op {
        desc::BinOp::Add => cu::BinOp::Add,
        desc::BinOp::Sub => cu::BinOp::Sub,
        desc::BinOp::Mul => cu::BinOp::Mul,
        desc::BinOp::Div => cu::BinOp::Div,
        desc::BinOp::Mod => cu::BinOp::Mod,
        desc::BinOp::And => cu::BinOp::And,
        desc::BinOp::Or => cu::BinOp::Or,
        desc::BinOp::Eq => cu::BinOp::Eq,
        desc::BinOp::Lt => cu::BinOp::Lt,
        desc::BinOp::Le => cu::BinOp::Le,
        desc::BinOp::Gt => cu::BinOp::Gt,
        desc::BinOp::Ge => cu::BinOp::Ge,
        desc::BinOp::Neq => cu::BinOp::Neq,
    };
    use CheckedExpr as ce;
    match (
        gen_expr(lhs, parall_ctx, view_ctx, comp_unit, label.clone()),
        gen_expr(rhs, parall_ctx, view_ctx, comp_unit, label),
    ) {
        (ce::ExprIdxCheck(ch1, e1), ce::ExprIdxCheck(ch2, e2)) => {
            CheckedExpr::ExprIdxCheck(
                cu::Stmt::Seq(Box::new(ch1), Box::new(ch2)),
                cu::Expr::BinOp {
                    op: op,
                    lhs: Box::new(e1),
                    rhs: Box::new(e2),
                },
            )
        }
        (ce::Expr(e1), ce::ExprIdxCheck(ch, e2))
        | (ce::ExprIdxCheck(ch, e1), ce::Expr(e2)) => CheckedExpr::ExprIdxCheck(
            ch,
            cu::Expr::BinOp {
                op: op,
                lhs: Box::new(e1),
                rhs: Box::new(e2),
            },
        ),
        (ce::Expr(e1), ce::Expr(e2)) => CheckedExpr::Expr(cu::Expr::BinOp {
            op: op,
            lhs: Box::new(e1),
            rhs: Box::new(e2),
        }),
    }
}

}

fn extract_ident(ident: &desc::Expr) -> Ident {
    if let desc::ExprKind::PlaceExpr(desc::PlaceExpr {
        kind: PlaceExprKind::Ident(ident),
        ..
    }) = &ident.expr
    {
        ident.clone()
    } else {
        panic!("Generic functions must be global functions.")
    }
}

fn contains_view_expr(pl_expr: &desc::PlaceExpr, view_ctx: &HashMap<String, ViewExpr>) -> bool {
    let (_, pl) = pl_expr.to_pl_ctx_and_most_specif_pl();
    view_ctx.contains_key(&pl.ident.name)
}

fn gen_idx_into_view(
    pl_expr: &desc::PlaceExpr,
    idx: &desc::Nat,
    view_ctx: &mut HashMap<String, ViewExpr>,
    comp_unit: &[desc::FunDef],
) -> cu::Expr {
    let collec_view = ViewExpr::create_from(
        &desc::Expr::new(desc::ExprKind::PlaceExpr(pl_expr.clone())),
        view_ctx,
    );
    gen_view(
        &ViewExpr::Idx {
            idx: idx.clone(),
            view: Box::new(collec_view),
        },
        vec![],
        view_ctx,
        comp_unit,
    )
}

fn create_lambda_no_view_args(
    fun: &desc::Expr,
    generic_args: &[desc::ArgKinded],
    args: &[desc::Expr],
    // TODO remove parallel collections as well as views
    parall_ctx: &mut HashMap<String, ParallelityCollec>,
    view_ctx: &mut HashMap<String, ViewExpr>,
    comp_unit: &[desc::FunDef],
) -> Option<(desc::Expr, Vec<desc::Expr>)> {
    // FIXME doesn't work for predeclared functions which expect a view type argument
    match &fun.expr {
        desc::ExprKind::Lambda(param_decls, exec, ret_dty, body) => {
            Some(create_lambda_and_args_only_dtys(
                fun,
                param_decls,
                args,
                body,
                *exec,
                ret_dty,
                parall_ctx,
                view_ctx,
            ))
        }
        desc::ExprKind::PlaceExpr(desc::PlaceExpr {
            kind: PlaceExprKind::Ident(f),
            ..
        }) => {
            let fun_def = comp_unit
                .iter()
                .find(|fun_def| fun_def.name == f.name)
                .expect("Cannot find function definition.");
            if !contains_view_or_th_hierchy_params(&fun_def.param_decls) {
                return None;
            }
            let partial_app_fun = partial_app_gen_args(fun_def, generic_args);
            let (param_decls, new_body) =
                if let desc::ExprKind::Lambda(param_decls, _, _, body) = &partial_app_fun.expr {
                    (param_decls, body.as_ref())
                } else {
                    panic!("Expected a lambda.")
                };
            Some(create_lambda_and_args_only_dtys(
                fun,
                param_decls,
                args,
                new_body,
                fun_def.exec,
                &fun_def.ret_dty,
                parall_ctx,
                view_ctx,
            ))
        }
        _ => panic!(
            "Functions cannot be created dynamically, so they have to either be\
                        global function definitions or lambdas. This should never happen."
        ),
    }
}

fn create_lambda_and_args_only_dtys(
    fun: &desc::Expr,
    param_decls: &[desc::ParamDecl],
    args: &[desc::Expr],
    body: &desc::Expr,
    exec: desc::Exec,
    ret_dty: &desc::DataTy,
    parall_ctx: &mut HashMap<String, ParallelityCollec>,
    view_ctx: &mut HashMap<String, ViewExpr>,
) -> (desc::Expr, Vec<desc::Expr>) {
    let (data_param_decls, data_args) = separate_param_decls_from_args(
        filter_and_map_view_th_hierchy_params(param_decls, args, parall_ctx, view_ctx),
    );
    let partial_app_fun_ty =
        create_fun_ty_of_purely_data_tys(get_data_param_tys(fun), exec, ret_dty);
    let partial_app_fun = desc::Expr::with_type(
        desc::ExprKind::Lambda(
            data_param_decls,
            exec,
            Box::new(ret_dty.clone()),
            Box::new(body.clone()),
        ),
        partial_app_fun_ty,
    );
    (partial_app_fun, data_args)
}

fn separate_param_decls_from_args(
    param_decls_to_args: Vec<(&desc::ParamDecl, &desc::Expr)>,
) -> (Vec<desc::ParamDecl>, Vec<desc::Expr>) {
    let data_param_decls: Vec<desc::ParamDecl> = param_decls_to_args
        .iter()
        .map(|(param_decl, _)| *param_decl)
        .cloned()
        .collect();
    let data_args: Vec<desc::Expr> = param_decls_to_args
        .iter()
        .map(|(_, arg)| *arg)
        .cloned()
        .collect();

    (data_param_decls, data_args)
}

fn get_data_param_tys(fun: &desc::Expr) -> Vec<desc::Ty> {
    if let desc::TyKind::Fn(_, param_tys, _, _) = &fun.ty.as_ref().unwrap().ty {
        param_tys
            .iter()
            .filter(|p_ty| !matches!(&p_ty.ty, desc::TyKind::View(_)))
            .cloned()
            .collect()
    } else {
        panic!("A function must have a function type.")
    }
}

fn create_fun_ty_of_purely_data_tys(
    data_param_tys: Vec<desc::Ty>,
    exec: desc::Exec,
    ret_dty: &desc::DataTy,
) -> desc::Ty {
    desc::Ty::new(desc::TyKind::Fn(
        vec![],
        data_param_tys,
        exec,
        Box::new(desc::Ty::new(desc::TyKind::Data(ret_dty.clone()))),
    ))
}

fn partial_app_gen_args(fun: &desc::FunDef, gen_args: &[desc::ArgKinded]) -> desc::Expr {
    let subst_map_kinded_idents: HashMap<&str, &desc::ArgKinded> = fun
        .generic_params
        .iter()
        .map(|id_kinded| id_kinded.ident.name.as_str())
        .zip(gen_args)
        .collect();
    if let desc::TyKind::Fn(_, param_tys, exec, ret_ty) = &fun.ty().ty {
        let fun_ty = desc::Ty::new(desc::TyKind::Fn(
            vec![],
            param_tys.clone(),
            *exec,
            ret_ty.clone(),
        ));
        let mut fun = desc::Expr::with_type(
            desc::ExprKind::Lambda(
                fun.param_decls.clone(),
                *exec,
                Box::new(fun.ret_dty.clone()),
                Box::new(fun.body_expr.clone()),
            ),
            fun_ty,
        );
        fun.subst_kinded_idents(subst_map_kinded_idents);
        fun
    } else {
        panic!("A function must have a function type.")
    }
}

fn contains_view_or_th_hierchy_params(param_decls: &[desc::ParamDecl]) -> bool {
    param_decls.iter().any(|p| {
        matches!(&p.ty.ty, desc::TyKind::View(_))
            || matches!(&p.ty.ty, desc::TyKind::ThreadHierchy(_))
    })
}

fn filter_and_map_view_th_hierchy_params<'a>(
    param_decls: &'a [desc::ParamDecl],
    args: &'a [desc::Expr],
    parall_ctx: &mut HashMap<String, ParallelityCollec>,
    view_ctx: &mut HashMap<String, ViewExpr>,
) -> Vec<(&'a desc::ParamDecl, &'a desc::Expr)> {
    let (reducable_parms_with_args, data_params_with_args): (Vec<_>, Vec<_>) =
        param_decls.iter().zip(args.iter()).partition(|&(p, _)| {
            matches!(&p.ty.ty, desc::TyKind::View(_))
                || matches!(&p.ty.ty, desc::TyKind::ThreadHierchy(_))
        });
    let (view_params_with_args, th_hierchy_params_with_args): (Vec<_>, Vec<_>) =
        reducable_parms_with_args
            .iter()
            .partition(|&(p, _)| matches!(&p.ty.ty, desc::TyKind::View(_)));
    for (p, arg) in view_params_with_args {
        view_ctx.insert(p.ident.name.clone(), ViewExpr::create_from(arg, view_ctx));
    }
    for (p, arg) in th_hierchy_params_with_args {
        parall_ctx.insert(
            p.ident.name.clone(),
            ParallelityCollec::create_from(arg, parall_ctx),
        );
    }

    data_params_with_args
}

fn gen_lit(l: desc::Lit) -> cu::Expr {
    match l {
        desc::Lit::Bool(b) => cu::Expr::Lit(cu::Lit::Bool(b)),
        desc::Lit::I32(i) => cu::Expr::Lit(cu::Lit::I32(i)),
        desc::Lit::U32(u) => cu::Expr::Lit(cu::Lit::U32(u)),
        desc::Lit::F32(f) => cu::Expr::Lit(cu::Lit::F32(f)),
        desc::Lit::Unit => cu::Expr::Empty,
    }
}

fn gen_pl_expr(
    pl_expr: &desc::PlaceExpr,
    view_ctx: &mut HashMap<String, ViewExpr>,
    comp_unit: &[desc::FunDef],
) -> cu::Expr {
    match &pl_expr {
        desc::PlaceExpr {
            kind: PlaceExprKind::Ident(ident),
            ..
        } => {
            if view_ctx.contains_key(&ident.name) {
                gen_view(
                    &view_ctx.get(&ident.name).unwrap().clone(),
                    vec![],
                    view_ctx,
                    comp_unit,
                )
            } else {
                let is_pre_decl_fun = crate::ty_check::pre_decl::fun_decls()
                    .iter()
                    .any(|(name, _)| &ident.name == name);
                let name = if is_pre_decl_fun {
                    format!("descend::{}", ident.name)
                } else {
                    ident.name.clone()
                };
                cu::Expr::Ident(name)
            }
        }
        desc::PlaceExpr {
            kind: PlaceExprKind::Proj(pl, n),
            ..
        } => match pl_expr.to_place() {
            // FIXME this does not work when there are tuples inside of view tuples
            Some(p) if view_ctx.contains_key(&p.ident.name) => gen_view(
                &view_ctx.get(&p.ident.name).unwrap().clone(),
                p.path.iter().map(|n| desc::Nat::Lit(*n)).collect(),
                view_ctx,
                comp_unit,
            ),
            _ => cu::Expr::Proj {
                tuple: Box::new(gen_pl_expr(pl.as_ref(), view_ctx, comp_unit)),
                n: *n,
            },
        },
        desc::PlaceExpr {
            kind: PlaceExprKind::Deref(ple),
            ..
        } => {
            // If an identifier that refers to an unwrapped view expression is being dereferenced,
            // just generate from the view expression and omit generating the dereferencing.
            // The dereferencing will happen through indexing.
            match ple.to_place() {
                Some(pl) if view_ctx.contains_key(&pl.ident.name) => gen_view(
                    &view_ctx.get(&pl.ident.name).unwrap().clone(),
                    pl.path.iter().map(|n| desc::Nat::Lit(*n)).collect(),
                    view_ctx,
                    comp_unit,
                ),
                _ => cu::Expr::Deref(Box::new(gen_pl_expr(ple.as_ref(), view_ctx, comp_unit))),
            }
        }
    }
}

enum ParallRange {
    Range(desc::Nat, desc::Nat),
    SplitRange(desc::Nat, desc::Nat, desc::Nat),
}

// FIXME this currently assumes that there is only one branch, i.e., some threads work (those which
//  fullfill the condition) and the rest is idle.
fn gen_parall_cond(
    pid: &desc::Nat,
    parall_collec: &ParallelityCollec,
) -> Option<(Option<cu::Expr>, ParallRange)> {
    match parall_collec {
        ParallelityCollec::Ident(_) => None,
        ParallelityCollec::Proj { parall_expr, i } => {
            if let Some((cond, ParallRange::SplitRange(l, m, u))) =
                gen_parall_cond(pid, parall_expr)
            {
                let (cond_stmt, range) = if *i == 0 {
                    (
                        cu::Expr::BinOp {
                            op: cu::BinOp::Lt,
                            lhs: Box::new(cu::Expr::Nat(pid.clone())),
                            rhs: Box::new(cu::Expr::Nat(m.clone())),
                        },
                        ParallRange::Range(l, m),
                    )
                } else if *i == 1 {
                    (
                        cu::Expr::BinOp {
                            op: cu::BinOp::Ge,
                            lhs: Box::new(cu::Expr::Nat(m.clone())),
                            rhs: Box::new(cu::Expr::Nat(pid.clone())),
                        },
                        ParallRange::Range(m, u),
                    )
                } else {
                    panic!("Split can only create a 2-tuple.")
                };

                if let Some(c) = cond {
                    Some((
                        Some(cu::Expr::BinOp {
                            op: cu::BinOp::And,
                            lhs: Box::new(cond_stmt),
                            rhs: Box::new(c),
                        }),
                        range,
                    ))
                } else {
                    Some((Some(cond_stmt), range))
                }
            } else {
                panic!()
            }
        }
        ParallelityCollec::Split {
            pos,
            coll_size,
            parall_expr,
        } => {
            if let Some((cond, ParallRange::Range(l, u))) = gen_parall_cond(pid, parall_expr) {
                Some((
                    cond,
                    ParallRange::SplitRange(
                        l.clone(),
                        desc::Nat::BinOp(desc::BinOpNat::Add, Box::new(l), Box::new(pos.clone())),
                        u,
                    ),
                ))
            } else {
                Some((
                    None,
                    ParallRange::SplitRange(desc::Nat::Lit(0), pos.clone(), coll_size.clone()),
                ))
            }
        }
    }
}

fn gen_view(
    view_expr: &ViewExpr,
    mut path: Vec<desc::Nat>,
    view_ctx: &mut HashMap<String, ViewExpr>,
    comp_unit: &[desc::FunDef],
) -> cu::Expr {
    fn gen_indexing(expr: cu::Expr, path: &[desc::Nat]) -> cu::Expr {
        let index = if path.is_empty() {
            return expr;
        } else if path.len() == 1 {
            path[0].clone()
        } else {
            let fst = path[0].clone();
            let snd = path[1].clone();
            let mut idx_nat = desc::Nat::BinOp(desc::BinOpNat::Add, Box::new(fst), Box::new(snd));
            for i in &path[2..] {
                idx_nat =
                    desc::Nat::BinOp(desc::BinOpNat::Add, Box::new(idx_nat), Box::new(i.clone()));
            }
            idx_nat
        };

        cu::Expr::ArraySubscript {
            array: Box::new(expr),
            index: index,
        }
    }

    match (view_expr, path.as_slice()) {
        (ViewExpr::ToView { ref_expr, .. }, _) => {
            path.reverse();
            gen_indexing(
                match gen_expr(ref_expr, &mut HashMap::new(), view_ctx, comp_unit, None) { //? \/ this, too?
                    CheckedExpr::Expr(e) => e,
                    CheckedExpr::ExprIdxCheck(_, _) => panic!("should never happen"), //? am I right?
                },
                &path,
            )
        }
        (ViewExpr::Tuple { views }, [path @ .., prj]) => match prj.eval() {
            Ok(i) => match &views[i] {
                ViewOrExpr::V(view_expr) => gen_view(view_expr, path.to_vec(), view_ctx, comp_unit),
                ViewOrExpr::E(expr) => gen_view(
                    &ViewExpr::ToView {
                        ref_expr: Box::new(expr.clone()),
                    },
                    path.to_vec(),
                    view_ctx,
                    comp_unit,
                ), // gen_expr(expr, &mut HashMap::new(), view_ctx, comp_unit),
            },
            Err(e) => panic!(e),
        },
        (ViewExpr::Idx { idx, view }, _) => {
            path.push(idx.clone());
            gen_view(view, path, view_ctx, comp_unit)
        }
        (ViewExpr::Proj { view, i }, _) => {
            path.push(desc::Nat::Lit(*i));
            gen_view(view, path, view_ctx, comp_unit)
        }
        (ViewExpr::SplitAt { pos, view }, _) => {
            let proj = path.pop();
            let idx = path.pop();
            match (proj, idx) {
                (Some(pr), Some(i)) => match pr.eval() {
                    Ok(v) => {
                        if v == 0 {
                            path.push(i);
                            gen_view(view, path, view_ctx, comp_unit)
                        } else if v == 1 {
                            path.push(desc::Nat::BinOp(
                                desc::BinOpNat::Add,
                                Box::new(i),
                                Box::new(pos.clone()),
                            ));
                            gen_view(view, path, view_ctx, comp_unit)
                        } else {
                            panic!("split_at can only generate a 2-tuple view.")
                        }
                    }
                    Err(m) => panic!(m),
                },
                _ => panic!("Cannot create SplitAt view. Index or projection missing."),
            }
        }
        (ViewExpr::Group { size, n, view }, _) => {
            let i = path.pop();
            let j = path.pop();
            match (i, j) {
                (Some(i), Some(j)) => {
                    path.push(desc::Nat::BinOp(
                        desc::BinOpNat::Add,
                        Box::new(desc::Nat::BinOp(
                            desc::BinOpNat::Mul,
                            Box::new(i),
                            Box::new(size.clone()),
                        )),
                        Box::new(j),
                    ));
                    gen_view(view, path, view_ctx, comp_unit)
                }
                (Some(i), None) => {
                    path.push(desc::Nat::BinOp(
                        desc::BinOpNat::Mul,
                        Box::new(i),
                        Box::new(size.clone()),
                    ));
                    gen_view(view, path, view_ctx, comp_unit)
                }
                _ => panic!("Cannot generate Group view. One or more indices missing."),
            }
        }
        (ViewExpr::Zip { n, views }, _) => {
            let idx = path.pop();
            let proj = path.pop();
            match (idx, proj) {
                (Some(i), Some(pr)) => match pr.eval() {
                    Ok(v) => {
                        let inner_view = &views[v];
                        path.push(i);
                        gen_view(inner_view, path, view_ctx, comp_unit)
                    }
                    Err(m) => panic!(m),
                },
                _ => panic!("Cannot generate Zip View. Index or projection missing."),
            }
        }
        (ViewExpr::Join { m, n, view }, _) => unimplemented!(),
        (ViewExpr::Transpose { m, n, view }, _) => unimplemented!(),
        ve => panic!("unexpected, found: {:?}", ve),
    }
}

fn gen_templ_params(ty_idents: &[desc::IdentKinded]) -> Vec<cu::TemplParam> {
    ty_idents
        .iter()
        .filter_map(|ty_ident| {
            if !matches!(ty_ident.kind, desc::Kind::Provenance) {
                Some(gen_templ_param(ty_ident))
            } else {
                None
            }
        })
        .collect()
}

fn gen_templ_param(ty_ident: &desc::IdentKinded) -> cu::TemplParam {
    let name = ty_ident.ident.name.clone();
    match ty_ident.kind {
        desc::Kind::Nat => cu::TemplParam::Value {
            param_name: name,
            ty: cu::Ty::Scalar(cu::ScalarTy::SizeT),
        },
        desc::Kind::Memory => cu::TemplParam::Value {
            param_name: name,
            ty: cu::Ty::Scalar(cu::ScalarTy::Memory),
        },
        desc::Kind::Ty => cu::TemplParam::TyName { name },
        _ => panic!("Cannot generate template parameter for {:?}", ty_ident.kind),
    }
}

fn gen_param_decls(param_decls: &[desc::ParamDecl]) -> Vec<cu::ParamDecl> {
    param_decls.iter().map(gen_param_decl).collect()
}

fn gen_param_decl(param_decl: &desc::ParamDecl) -> cu::ParamDecl {
    let desc::ParamDecl { ident, ty, mutbl } = param_decl;
    cu::ParamDecl {
        name: ident.name.clone(),
        ty: gen_ty(&ty.ty, *mutbl),
    }
}

fn gen_args_kinded(templ_args: &[desc::ArgKinded]) -> Vec<cu::TemplateArg> {
    templ_args.iter().filter_map(gen_arg_kinded).collect()
}

fn gen_arg_kinded(templ_arg: &desc::ArgKinded) -> Option<cu::TemplateArg> {
    match templ_arg {
        desc::ArgKinded::Nat(n) => Some(cu::TemplateArg::Expr(cu::Expr::Nat(n.clone()))),
        desc::ArgKinded::Ty(desc::Ty {
            ty: ty @ desc::TyKind::Data(_),
            ..
        }) => Some(cu::TemplateArg::Ty(gen_ty(&ty, desc::Mutability::Mut))),
        desc::ArgKinded::Ty(desc::Ty {
            ty: desc::TyKind::Ident(_),
            ..
        }) => unimplemented!(),
        desc::ArgKinded::Ty(desc::Ty {
            ty: desc::TyKind::View(_),
            ..
        }) => None,
        desc::ArgKinded::Ty(desc::Ty {
            ty: desc::TyKind::ThreadHierchy(_),
            ..
        }) => None,
        desc::ArgKinded::Ty(desc::Ty {
            ty: desc::TyKind::Fn(_, _, _, _),
            ..
        }) => unimplemented!("needed?"),
        desc::ArgKinded::Memory(_) | desc::ArgKinded::Provenance(_) | desc::ArgKinded::Ident(_) => {
            None
        }
    }
}

// Param mutbl is not strictly necessary because every const type can just be wrapped
// in cu::Ty::Const. However, the formalism uses this, because it shows the generated code
// as opposed to a Cuda-AST and there, the order of the const is different
// when it comes to pointers (C things).
fn gen_ty(ty: &desc::TyKind, mutbl: desc::Mutability) -> cu::Ty {
    use desc::DataTy as d;
    use desc::TyKind::*;

    let m = desc::Mutability::Mut;
    let cu_ty = match ty {
        Ident(ident) => cu::Ty::Ident(ident.name.clone()),
        Fn(_, _, _, _) => unimplemented!("needed?"),
        Data(d::Atomic(a)) => match a {
            desc::ScalarTy::Unit => cu::Ty::Atomic(cu::ScalarTy::Void),
            desc::ScalarTy::I32 => cu::Ty::Atomic(cu::ScalarTy::I32),
            desc::ScalarTy::U32 => cu::Ty::Atomic(cu::ScalarTy::U32),
            desc::ScalarTy::F32 => cu::Ty::Atomic(cu::ScalarTy::F32),
            desc::ScalarTy::Bool => cu::Ty::Atomic(cu::ScalarTy::Bool),
            desc::ScalarTy::Gpu => cu::Ty::Atomic(cu::ScalarTy::Gpu),
        }
        Data(d::Scalar(s)) => match s {
            desc::ScalarTy::Unit => cu::Ty::Scalar(cu::ScalarTy::Void),
            desc::ScalarTy::I32 => cu::Ty::Scalar(cu::ScalarTy::I32),
            desc::ScalarTy::U32 => cu::Ty::Scalar(cu::ScalarTy::U32),
            desc::ScalarTy::F32 => cu::Ty::Scalar(cu::ScalarTy::F32),
            desc::ScalarTy::Bool => cu::Ty::Scalar(cu::ScalarTy::Bool),
            desc::ScalarTy::Gpu => cu::Ty::Scalar(cu::ScalarTy::Gpu),
        },
        Data(d::Tuple(tys)) => {
            cu::Ty::Tuple(tys.iter().map(|ty| gen_ty(&Data(ty.clone()), m)).collect())
        }
        Data(d::Array(ty, n)) => {
            cu::Ty::Array(Box::new(gen_ty(&Data(ty.as_ref().clone()), m)), n.clone())
        }
        Data(d::At(ty, mem)) => {
            if let desc::Memory::GpuShared = mem {
                let dty = match ty.as_ref() {
                    d::Array(dty, _) => dty.as_ref().clone(),
                    _ => ty.as_ref().clone(),
                };
                cu::Ty::Ptr(
                    Box::new(gen_ty(&desc::TyKind::Data(dty), mutbl)),
                    Some(cu::GpuAddrSpace::Shared),
                )
            } else {
                let buff_kind = match mem {
                    desc::Memory::CpuHeap => cu::BufferKind::CpuHeap,
                    desc::Memory::GpuGlobal => cu::BufferKind::GpuGlobal,
                    desc::Memory::Ident(ident) => cu::BufferKind::Ident(ident.name.clone()),
                    desc::Memory::GpuShared => unimplemented!(),
                    desc::Memory::None => {
                        panic!("No memory is not valid for At types. should never appear here.")
                    }
                    desc::Memory::GpuLocal => {
                        panic!("GpuLocal is not valid for At types. Should never appear here.")
                    }
                    desc::Memory::CpuStack => {
                        panic!("CpuStack is not valid for At types. Should never appear here.")
                    }
                };
                cu::Ty::Buffer(Box::new(gen_ty(&Data(ty.as_ref().clone()), m)), buff_kind)
            }
        }
        Data(d::Ref(_, own, _, ty)) => {
            let tty = Box::new(gen_ty(
                &Data(match ty.as_ref() {
                    // Pointers to arrays point to the element type.
                    desc::DataTy::Array(elem_ty, _) => elem_ty.as_ref().clone(),
                    _ => ty.as_ref().clone(),
                }),
                m,
            ));
            if matches!(own, desc::Ownership::Uniq) {
                cu::Ty::Ptr(tty, None)
            } else {
                cu::Ty::PtrConst(tty, None)
            }
        }
        // TODO is this correct. I guess we want to generate type identifiers in generic functions.
        Data(d::Ident(ident)) => cu::Ty::Ident(ident.name.clone()),
        Data(d::Dead(_)) => {
            panic!("Dead types are only for type checking and cannot be generated.")
        }
        View(_) => panic!(
            "Cannot generate view types. Anything with this type should have been compiled away."
        ),
        ThreadHierchy(t) => panic!(
            "Cannot generate thread hierarchy types. \
        Anything with this type should ave been compiled away."
        ),
    };

    if matches!(mutbl, desc::Mutability::Mut) {
        cu_ty
    } else {
        cu::Ty::Const(Box::new(cu_ty))
    }
}

fn is_dev_fun(exec: desc::Exec) -> bool {
    match exec {
        desc::Exec::GpuGrid
        | desc::Exec::GpuBlock
        | desc::Exec::GpuWarp
        | desc::Exec::GpuThread => true,
        desc::Exec::CpuThread | desc::Exec::View => false,
    }
}

fn extract_size(ty: &desc::Ty) -> Option<desc::Nat> {
    match &ty.ty {
        desc::TyKind::Data(desc::DataTy::Array(_, n)) => Some(n.clone()),
        desc::TyKind::Data(desc::DataTy::Ref(_, _, _, arr)) => match arr.as_ref() {
            desc::DataTy::Array(_, n) => Some(n.clone()),
            _ => None,
        },
        _ => None,
    }
}

#[derive(Debug, Clone)]
enum ParallelityCollec {
    Ident(Ident),
    Proj {
        parall_expr: Box<ParallelityCollec>,
        i: usize,
    },
    Split {
        pos: desc::Nat,
        coll_size: desc::Nat,
        parall_expr: Box<ParallelityCollec>,
    },
}

impl ParallelityCollec {
    fn create_from(
        expr: &desc::Expr,
        parall_ctx: &HashMap<String, ParallelityCollec>,
    ) -> ParallelityCollec {
        match &expr.expr {
            desc::ExprKind::App(f, gen_args, args) => {
                if let desc::ExprKind::PlaceExpr(desc::PlaceExpr {
                    kind: PlaceExprKind::Ident(ident),
                    ..
                }) = &f.expr
                {
                    if ident.name == crate::ty_check::pre_decl::SPLIT_THREAD_GRP {
                        if let (desc::ArgKinded::Nat(k), desc::ArgKinded::Nat(n), Some(p)) =
                            (&gen_args[0], &gen_args[1], args.first())
                        {
                            return ParallelityCollec::Split {
                                pos: k.clone(),
                                coll_size: n.clone(),
                                parall_expr: Box::new(ParallelityCollec::create_from(
                                    p, parall_ctx,
                                )),
                            };
                        }
                        panic!("Cannot create `split` from the provided arguments.");
                    } else if ident.name == crate::ty_check::pre_decl::SPLIT_WARP {
                        if let (desc::ArgKinded::Nat(k), Some(p)) = (&gen_args[0], args.first()) {
                            return ParallelityCollec::Split {
                                pos: k.clone(),
                                coll_size: desc::Nat::Lit(32),
                                parall_expr: Box::new(ParallelityCollec::create_from(
                                    p, parall_ctx,
                                )),
                            };
                        }
                        panic!("Cannot create `split` from the provided arguments.");
                    } else {
                        unimplemented!()
                    }
                } else {
                    panic!(
                        "Non-globally defined functions that can transform parallel collections \
                     do not exist."
                    )
                }
            }
            desc::ExprKind::PlaceExpr(pl_expr) => {
                ParallelityCollec::create_parall_pl_expr(pl_expr, parall_ctx)
            }
            desc::ExprKind::Proj(expr, i) => ParallelityCollec::Proj {
                parall_expr: Box::new(ParallelityCollec::create_from(expr, parall_ctx)),
                i: *i,
            },
            _ => panic!(
                "Expected a function application, identifer or projection, but found {:?}",
                expr.expr
            ),
        }
    }

    fn create_parall_pl_expr(
        parall_expr: &desc::PlaceExpr,
        parall_ctx: &HashMap<String, ParallelityCollec>,
    ) -> ParallelityCollec {
        match parall_expr {
            desc::PlaceExpr {
                kind: PlaceExprKind::Ident(ident),
                ..
            } => parall_ctx.get(&ident.name).unwrap().clone(),
            desc::PlaceExpr {
                kind: PlaceExprKind::Proj(pp, i),
                ..
            } => ParallelityCollec::Proj {
                parall_expr: Box::new(ParallelityCollec::create_parall_pl_expr(pp, parall_ctx)),
                i: *i,
            },
            desc::PlaceExpr {
                kind: PlaceExprKind::Deref(_),
                ..
            } => panic!(
                "It is not possible to take references of Grids or Blocks.\
                This should never happen."
            ),
        }
    }
}

fn is_parall_collec_ty(ty: &desc::Ty) -> bool {
    matches!(ty.ty, desc::TyKind::ThreadHierchy(_))
}

#[derive(Debug, Clone)]
enum ViewOrExpr {
    V(ViewExpr),
    E(desc::Expr),
}
impl ViewOrExpr {
    fn expr(&self) -> desc::Expr {
        if let ViewOrExpr::E(expr) = self {
            expr.clone()
        } else {
            panic!("Not an expression.")
        }
    }
}

// Views are parsed as normal predeclared functions so that it is possible to infer types.
// During code generation view function applications are converted to View Variants and used
// to generate Indices.
#[derive(Debug, Clone)]
enum ViewExpr {
    ToView {
        ref_expr: Box<desc::Expr>,
    },
    Tuple {
        views: Vec<ViewOrExpr>,
    },
    Idx {
        idx: desc::Nat,
        view: Box<ViewExpr>,
    },
    Proj {
        view: Box<ViewExpr>,
        i: usize,
    },
    SplitAt {
        pos: desc::Nat,
        view: Box<ViewExpr>,
    },
    Group {
        size: desc::Nat,
        n: desc::Nat,
        view: Box<ViewExpr>,
    },
    Join {
        m: desc::Nat,
        n: desc::Nat,
        view: Box<ViewExpr>,
    },

    Zip {
        n: desc::Nat,
        views: Vec<ViewExpr>,
    },
    Transpose {
        m: desc::Nat,
        n: desc::Nat,
        view: Box<ViewExpr>,
    },
}

impl ViewExpr {
    // Precondition: Expression is a fully typed function application and has type ArrayView.
    fn create_from(expr: &desc::Expr, view_ctx: &HashMap<String, ViewExpr>) -> ViewExpr {
        match &expr.expr {
            // TODO this is assuming that f is an identifier
            desc::ExprKind::App(f, gen_args, args) => {
                if let desc::ExprKind::PlaceExpr(desc::PlaceExpr {
                    kind: PlaceExprKind::Ident(ident),
                    ..
                }) = &f.expr
                {
                    if ident.name == crate::ty_check::pre_decl::TO_VIEW
                        || ident.name == crate::ty_check::pre_decl::TO_VIEW_MUT
                    {
                        ViewExpr::create_to_view_view(args)
                    } else if ident.name == crate::ty_check::pre_decl::SPLIT_AT {
                        ViewExpr::create_split_at_view(gen_args, args, view_ctx)
                    } else if ident.name == crate::ty_check::pre_decl::GROUP {
                        ViewExpr::create_group_view(gen_args, args, view_ctx)
                    } else if ident.name == crate::ty_check::pre_decl::JOIN {
                        ViewExpr::create_join_view(gen_args, args, view_ctx)
                    } else if ident.name == crate::ty_check::pre_decl::ZIP {
                        ViewExpr::create_zip_view(gen_args, args, view_ctx)
                    } else if ident.name == crate::ty_check::pre_decl::TRANSPOSE {
                        ViewExpr::create_transpose_view(gen_args, args, view_ctx)
                    } else {
                        unimplemented!()
                    }
                } else {
                    panic!("Non-globally defined view functions do not exist.")
                }
            }
            desc::ExprKind::PlaceExpr(pl_expr) => ViewExpr::create_pl_expr_view(pl_expr, view_ctx),
            desc::ExprKind::TupleView(elems) => ViewExpr::create_tuple_view(elems, view_ctx),
            desc::ExprKind::Proj(expr, i) => ViewExpr::Proj {
                view: Box::new(ViewExpr::create_from(expr, view_ctx)),
                i: *i,
            },
            _ => panic!(
                "Expected a function application, identifer or projection, but found {:?}",
                expr.expr
            ),
        }
    }

    fn create_to_view_view(args: &[desc::Expr]) -> ViewExpr {
        match args.first() {
            Some(e) =>
            // e cannot contain views, so the view_ctx can be empty
            {
                ViewExpr::ToView {
                    ref_expr: Box::new(e.clone()),
                }
            }
            _ => panic!("Place expression argument for to view does not exist."),
        }
    }

    fn create_pl_expr_view(
        view: &desc::PlaceExpr,
        view_ctx: &HashMap<String, ViewExpr>,
    ) -> ViewExpr {
        match view {
            desc::PlaceExpr {
                kind: PlaceExprKind::Ident(ident),
                ..
            } => view_ctx.get(&ident.name).unwrap().clone(),
            desc::PlaceExpr {
                kind: PlaceExprKind::Proj(vv, i),
                ..
            } => ViewExpr::Proj {
                view: Box::new(ViewExpr::create_pl_expr_view(vv, view_ctx)),
                i: *i,
            },
            desc::PlaceExpr {
                kind: PlaceExprKind::Deref(_),
                ..
            } => {
                panic!("It is not possible to take references of views. This should never happen.")
            }
        }
    }

    fn create_tuple_view(elems: &[desc::Expr], view_ctx: &HashMap<String, ViewExpr>) -> ViewExpr {
        ViewExpr::Tuple {
            views: elems
                .iter()
                .map(|e| match &e.ty.as_ref().unwrap().ty {
                    desc::TyKind::View(_) => ViewOrExpr::V(ViewExpr::create_from(e, view_ctx)),
                    _ => ViewOrExpr::E(e.clone()),
                })
                .collect(),
        }
    }

    fn create_split_at_view(
        gen_args: &[desc::ArgKinded],
        args: &[desc::Expr],
        view_ctx: &HashMap<String, ViewExpr>,
    ) -> ViewExpr {
        if let (desc::ArgKinded::Nat(s), Some(v)) = (&gen_args[0], args.first()) {
            return ViewExpr::SplitAt {
                pos: s.clone(),
                view: Box::new(ViewExpr::create_from(v, view_ctx)),
            };
        }
        panic!("Cannot create `split_at` from the provided arguments.");
    }

    fn create_group_view(
        gen_args: &[desc::ArgKinded],
        args: &[desc::Expr],
        view_ctx: &HashMap<String, ViewExpr>,
    ) -> ViewExpr {
        if let (desc::ArgKinded::Nat(s), desc::ArgKinded::Nat(n), Some(v)) =
            (&gen_args[0], &gen_args[1], args.first())
        {
            return ViewExpr::Group {
                size: s.clone(),
                n: n.clone(),
                view: Box::new(ViewExpr::create_from(v, view_ctx)),
            };
        }
        panic!("Cannot create `group` from the provided arguments.");
    }

    fn create_join_view(
        gen_args: &[desc::ArgKinded],
        args: &[desc::Expr],
        view_ctx: &HashMap<String, ViewExpr>,
    ) -> ViewExpr {
        if let (desc::ArgKinded::Nat(m), desc::ArgKinded::Nat(n), Some(v)) =
            (&gen_args[0], &gen_args[1], args.first())
        {
            return ViewExpr::Join {
                m: m.clone(),
                n: n.clone(),
                view: Box::new(ViewExpr::create_from(v, view_ctx)),
            };
        }
        panic!("Cannot create `to_view` from the provided arguments.");
    }

    fn create_zip_view(
        gen_args: &[desc::ArgKinded],
        args: &[desc::Expr],
        view_ctx: &HashMap<String, ViewExpr>,
    ) -> ViewExpr {
        if let (desc::ArgKinded::Nat(n), desc::ArgKinded::Ty(t1), desc::ArgKinded::Ty(t2), v1, v2) =
            (&gen_args[0], &gen_args[1], &gen_args[2], &args[0], &args[1])
        {
            return ViewExpr::Zip {
                n: n.clone(),
                views: vec![
                    ViewExpr::create_from(v1, view_ctx),
                    ViewExpr::create_from(v2, view_ctx),
                ],
            };
        }
        panic!(
            "Cannot create `zip` from the provided arguments:\n{:?},\n{:?},\n{:?}",
            &gen_args[0], &gen_args[1], &gen_args[2]
        );
    }

    fn create_transpose_view(
        gen_args: &[desc::ArgKinded],
        args: &[desc::Expr],
        view_ctx: &HashMap<String, ViewExpr>,
    ) -> ViewExpr {
        if let (
            desc::ArgKinded::Nat(m),
            desc::ArgKinded::Nat(n),
            desc::ArgKinded::Ty(ty),
            Some(v),
        ) = (&gen_args[0], &gen_args[1], &gen_args[2], args.first())
        {
            return ViewExpr::Transpose {
                m: m.clone(),
                n: n.clone(),
                view: Box::new(ViewExpr::create_from(v, view_ctx)),
            };
        }
        panic!("Cannot create `to_view` from the provided arguments.");
    }

    fn collect_and_rename_input_exprs(&mut self) -> Vec<(String, desc::Expr)> {
        fn collect_and_rename_input_exprs_rec(
            v: &mut ViewExpr,
            count: &mut u32,
            mut vec: Vec<(String, desc::Expr)>,
        ) -> Vec<(String, desc::Expr)> {
            match v {
                ViewExpr::ToView { ref_expr } => {
                    let new_name = format!("p{}", *count);
                    vec.push((new_name.clone(), ref_expr.as_ref().clone()));
                    ref_expr.expr = desc::ExprKind::PlaceExpr(desc::PlaceExpr::new(
                        PlaceExprKind::Ident(desc::Ident::new(&new_name)),
                    ));
                    *count += 1;
                    vec
                }
                ViewExpr::SplitAt { view, .. } => {
                    collect_and_rename_input_exprs_rec(view, count, vec)
                }
                ViewExpr::Group { view, .. } => {
                    collect_and_rename_input_exprs_rec(view, count, vec)
                }
                ViewExpr::Join { view, .. } => collect_and_rename_input_exprs_rec(view, count, vec),
                ViewExpr::Transpose { view, .. } => {
                    collect_and_rename_input_exprs_rec(view, count, vec)
                }
                ViewExpr::Zip { views, .. } => {
                    let mut renamed = vec;
                    for v in views {
                        renamed = collect_and_rename_input_exprs_rec(v, count, renamed);
                    }
                    renamed
                }
                ViewExpr::Tuple { views: elems } => {
                    let mut renamed = vec;
                    for e in elems {
                        match e {
                            ViewOrExpr::V(v) => {
                                renamed = collect_and_rename_input_exprs_rec(v, count, renamed);
                            }
                            ViewOrExpr::E(expr) => {
                                let new_name = format!("p{}", *count);
                                renamed.push((new_name.clone(), expr.clone()));
                                expr.expr = desc::ExprKind::PlaceExpr(desc::PlaceExpr::new(
                                    PlaceExprKind::Ident(desc::Ident::new(&new_name)),
                                ));
                                *count += 1;
                            }
                        }
                    }
                    renamed
                }
                ViewExpr::Idx { view, .. } => collect_and_rename_input_exprs_rec(view, count, vec),
                ViewExpr::Proj { view, .. } => collect_and_rename_input_exprs_rec(view, count, vec),
            }
        }
        let vec = vec![];
        let mut count = 0;
        collect_and_rename_input_exprs_rec(self, &mut count, vec)
    }
}

fn replace_arg_kinded_idents(mut fun_def: desc::FunDef) -> desc::FunDef {
    use crate::ast::visit;
    use crate::ast::visit::Visitor;
    use desc::*;
    struct ReplaceArgKindedIdents {
        ident_names_to_kinds: HashMap<String, Kind>,
    }
    impl Visitor for ReplaceArgKindedIdents {
        fn visit_expr(&mut self, expr: &mut Expr) {
            match &mut expr.expr {
                ExprKind::LetProv(prvs, body) => {
                    self.ident_names_to_kinds
                        .extend(prvs.iter().map(|prv| (prv.clone(), Kind::Provenance)));
                    self.visit_expr(body)
                }
                ExprKind::App(f, gen_args, args) => {
                    self.visit_expr(f);
                    for gen_arg in gen_args {
                        if let ArgKinded::Ident(ident) = gen_arg {
                            let to_be_kinded = ident.clone();
                            match self.ident_names_to_kinds.get(&ident.name).unwrap() {
                                Kind::Provenance => {
                                    *gen_arg =
                                        ArgKinded::Provenance(Provenance::Ident(to_be_kinded))
                                }
                                Kind::Memory => {
                                    *gen_arg = ArgKinded::Memory(Memory::Ident(to_be_kinded))
                                }
                                Kind::Nat => *gen_arg = ArgKinded::Nat(Nat::Ident(to_be_kinded)),
                                Kind::Ty => {
                                    // TODO how to deal with View??!! This is a problem!
                                    //  Ident only for Ty but not for DataTy or ViewTy?
                                    *gen_arg = ArgKinded::Ty(Ty::new(desc::TyKind::Data(
                                        DataTy::Ident(to_be_kinded),
                                    )))
                                }
                                _ => panic!("This kind can not be referred to with an identifier."),
                            }
                        }
                    }
                    walk_list!(self, visit_expr, args)
                }
                ExprKind::ForNat(ident, _, body) => {
                    self.ident_names_to_kinds
                        .extend(iter::once((ident.name.clone(), Kind::Nat)));
                    self.visit_expr(body)
                }
                _ => visit::walk_expr(self, expr),
            }
        }

        fn visit_fun_def(&mut self, fun_def: &mut FunDef) {
            self.ident_names_to_kinds = fun_def
                .generic_params
                .iter()
                .map(|desc::IdentKinded { ident, kind }| (ident.name.clone(), *kind))
                .collect();
            visit::walk_fun_def(self, fun_def)
        }
    }
    let mut replace = ReplaceArgKindedIdents {
        ident_names_to_kinds: HashMap::new(),
    };
    replace.visit_fun_def(&mut fun_def);
    fun_def
}

// Precondition: Views are inlined in every function definition.
fn inline_par_for_funs(mut fun_def: desc::FunDef, comp_unit: &[desc::FunDef]) -> desc::FunDef {
    use crate::ast::visit;
    use crate::ast::visit::Visitor;
    use desc::*;

    struct InlineParForFuns<'a> {
        comp_unit: &'a [FunDef],
    }
    impl InlineParForFuns<'_> {
        fn create_lambda_from_fun_def(&self, fun_def_name: &str) -> ExprKind {
            match self
                .comp_unit
                .iter()
                .find(|fun_def| fun_def.name == fun_def_name)
            {
                Some(FunDef {
                    param_decls: params,
                    ret_dty,
                    exec,
                    body_expr,
                    ..
                }) => ExprKind::Lambda(
                    params.clone(),
                    *exec,
                    Box::new(ret_dty.clone()),
                    Box::new(body_expr.clone()),
                ),
                None => {
                    panic!("The referenced function cannot be found in the given compilation unit.")
                }
            }
        }
    }

    impl Visitor for InlineParForFuns<'_> {
        fn visit_expr(&mut self, expr: &mut Expr) {
            match &mut expr.expr {
                ExprKind::ParFor(_, _, efs) => match &mut efs.expr {
                    ExprKind::TupleView(t) => {
                        for f in t {
                            match &mut f.expr {
                                ExprKind::PlaceExpr(PlaceExpr {
                                    kind: PlaceExprKind::Ident(x),
                                    ..
                                }) => f.expr = self.create_lambda_from_fun_def(&x.name),
                                _ => visit::walk_expr(self, f),
                            }
                        }
                    }
                    ExprKind::PlaceExpr(PlaceExpr {
                        kind: PlaceExprKind::Ident(x),
                        ..
                    }) => efs.expr = self.create_lambda_from_fun_def(&x.name),
                    _ => visit::walk_expr(self, efs),
                },
                _ => visit::walk_expr(self, expr),
            }
        }
    }

    let mut inliner = InlineParForFuns { comp_unit };
    inliner.visit_fun_def(&mut fun_def);
    fun_def
}
