mod cu_ast;
mod printer;

use crate::ast as desc;
use crate::ast::{BinOpNat, Ident, PlaceExpr};
use cu_ast as cu;
use std::collections::HashMap;
use std::iter;

// Precondition. all function defitions are successfully typechecked and
// therefore every subexpression stores a type
pub fn gen(comp_unit: &[desc::FunDef]) -> String {
    let all_kinds_known = comp_unit
        .iter()
        .map(replace_arg_kinded_idents)
        .collect::<Vec<desc::FunDef>>();
    let cu_program = all_kinds_known
        .iter()
        .map(gen_fun_def)
        .collect::<cu::CuProgram>();
    printer::print(&cu_program)
}

fn gen_fun_def(gl_fun: &desc::FunDef) -> cu::Item {
    let desc::FunDef {
        name,
        generic_params: ty_idents,
        params,
        ret_dty: ret_ty,
        exec,
        body_expr,
        ..
    } = gl_fun;

    cu::Item::FunDef {
        name: name.clone(),
        templ_params: gen_templ_params(ty_idents),
        params: gen_param_decls(params),
        ret_ty: gen_ty(&desc::Ty::Data(ret_ty.clone()), desc::Mutability::Mut).unwrap(),
        body: gen_stmt(
            body_expr,
            !matches!(ret_ty, desc::DataTy::Scalar(desc::ScalarTy::Unit)),
            &mut HashMap::new(),
            &mut HashMap::new(),
        ),
        is_dev_fun: is_dev_fun(*exec),
    }
}

fn gen_stmt(
    expr: &desc::Expr,
    return_value: bool,
    parall_ctx: &mut HashMap<String, ParallelityCollec>,
    view_ctx: &mut HashMap<String, ViewExpr>,
) -> cu::Stmt {
    use desc::ExprKind::*;
    match &expr.expr {
        Let(mutbl, ident, _, e1, e2) => {
            // Let View
            if matches!(e1.ty.as_ref().unwrap(), desc::Ty::View(_)) {
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
                gen_stmt(e2, return_value, parall_ctx, view_ctx)
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
                gen_stmt(e2, return_value, parall_ctx, view_ctx)
            } else if let Some(tty) = gen_ty(e1.ty.as_ref().unwrap(), mutbl.clone()) {
                cu::Stmt::Seq(
                    Box::new(cu::Stmt::VarDecl {
                        name: ident.name.clone(),
                        ty: tty,
                        expr: Some(gen_expr(e1, parall_ctx, view_ctx)),
                    }),
                    Box::new(gen_stmt(e2, return_value, parall_ctx, view_ctx)),
                )
            } else {
                gen_stmt(e2, return_value, parall_ctx, view_ctx)
            }
        }
        LetProv(prv_idents, expr) => {
            // let mut inner_kind_ctx = kind_ctx.clone();
            // inner_kind_ctx.extend(
            //     prv_idents
            //         .iter()
            //         .map(|id| (id.clone(), desc::Kind::Provenance)),
            // );
            gen_stmt(expr, return_value, parall_ctx, view_ctx)
        }
        // e1 ; e2
        Seq(e1, e2) => cu::Stmt::Seq(
            Box::new(gen_stmt(e1, false, parall_ctx, view_ctx)),
            Box::new(gen_stmt(e2, return_value, parall_ctx, view_ctx)),
        ),
        ForNat(ident, range, body) => {
            if return_value {
                panic!("A descend loop cannot return a value.");
            }
            let i = cu::Expr::Ident(ident.name.clone());
            let (init, cond, iter) = match range {
                desc::Nat::App(r_name, input) => {
                    let init_decl = cu::Stmt::VarDecl {
                        name: ident.name.clone(),
                        ty: cu::Ty::Scalar(cu::ScalarTy::I32),
                        expr: Some(cu::Expr::Nat(input[0].clone())),
                    };
                    let (cond, iter) = match r_name.name.as_str() {
                        "halved_range" => {
                            let cond = cu::Expr::BinOp {
                                op: cu::BinOp::Ge,
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
                            (cond, iter)
                        }
                        _ => unimplemented!(),
                    };
                    (init_decl, cond, iter)
                }
                _ => panic!("Currently ranges are assumed to be predeclared functions."),
            };

            cu::Stmt::ForLoop {
                init: Box::new(init),
                cond,
                iter,
                stmt: Box::new(cu::Stmt::Block(Box::new(gen_stmt(
                    body, false, parall_ctx, view_ctx,
                )))),
            }
        }
        For(ident, coll_expr, body) => {
            if return_value {
                panic!("Cannot return a value from for-loop.");
            }
            let i_name = crate::utils::fresh_name("_i_");
            let i_decl = cu::Stmt::VarDecl {
                name: i_name.clone(),
                ty: cu::Ty::Scalar(cu::ScalarTy::SizeT),
                expr: Some(cu::Expr::Lit(cu::Lit::I32(0))),
            };
            let i = cu::Expr::Ident(i_name);
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
                stmt: Box::new(gen_stmt(body, false, parall_ctx, view_ctx)),
            }
        }
        ParFor(parall_collec, input, funs) => {
            gen_par_for(parall_collec, input, funs, parall_ctx, view_ctx)
        }
        App(fun, kinded_args, args) => match &fun.expr {
            desc::ExprKind::PlaceExpr(desc::PlaceExpr::Ident(name)) if name.name == "exec" => {
                gen_exec(
                    &kinded_args[0],
                    &kinded_args[1],
                    &kinded_args[5],
                    &args[0],
                    &args[1],
                    &args[2],
                    parall_ctx,
                    view_ctx,
                )
            }
            _ => cu::Stmt::Expr(gen_expr(&expr, parall_ctx, view_ctx)),
        },
        _ if return_value => cu::Stmt::Return(Some(gen_expr(&expr, parall_ctx, view_ctx))),
        _ => cu::Stmt::Expr(gen_expr(&expr, parall_ctx, view_ctx)),
    }
}

fn gen_exec(
    blocks: &desc::ArgKinded,
    threads: &desc::ArgKinded,
    view_size: &desc::ArgKinded,
    gpu_expr: &desc::Expr,
    view_expr: &desc::Expr,
    body: &desc::Expr,
    parall_ctx: &mut HashMap<String, ParallelityCollec>,
    view_ctx: &mut HashMap<String, ViewExpr>,
) -> cu::Stmt {
    let mut v = ViewExpr::create_from(view_expr, view_ctx);
    let name_to_pl_exprs = v.collect_and_rename_pl_exprs();
    let param_decls: Vec<_> = name_to_pl_exprs
        .iter()
        .map(|(name, pl_expr)| cu::ParamDecl {
            name: name.clone(),
            ty: gen_ty(pl_expr.ty.as_ref().unwrap(), desc::Mutability::Const).unwrap(),
        })
        .collect();

    let gpu = gen_expr(gpu_expr, &mut HashMap::new(), &mut HashMap::new());

    let dev_fun = if let desc::ExprKind::Lambda(params, _, _, b) = &body.expr {
        let parall_collec = params[0].ident.clone();
        let mut scope_parall_ctx: HashMap<String, ParallelityCollec> = HashMap::new();
        scope_parall_ctx.insert(
            parall_collec.name.clone(),
            ParallelityCollec::Ident(parall_collec),
        );
        let in_name = params[1].ident.name.clone();
        let mut scope_view_ctx: HashMap<String, ViewExpr> = HashMap::new();
        scope_view_ctx.insert(in_name, v);
        let dev_fun = cu::Expr::Lambda {
            params: param_decls,
            body: Box::new(gen_stmt(
                b,
                false,
                &mut scope_parall_ctx,
                &mut scope_view_ctx,
            )),
            ret_ty: cu::Ty::Scalar(cu::ScalarTy::Void),
            is_dev_fun: true,
        };
        dev_fun
    } else {
        panic!("Currently only lambdas can be passed.")
    };

    let mut input: Vec<_> = name_to_pl_exprs
        .iter()
        .map(|(_, pl_expr)| gen_expr(pl_expr, &mut HashMap::new(), &mut HashMap::new()))
        .collect();
    let template_args =
        gen_args_kinded(vec![blocks.clone(), threads.clone(), view_size.clone()].as_slice());
    let mut args: Vec<cu::Expr> = vec![gpu, dev_fun];
    args.append(&mut input);
    cu::Stmt::Expr(cu::Expr::FunCall {
        fun: Box::new(cu::Expr::Ident("descend::exec".to_string())),
        template_args,
        args,
    })
}

fn gen_par_for(
    parall_collec: &desc::Expr,
    input_view: &desc::Expr,
    funs: &desc::Expr,
    parall_ctx: &mut HashMap<String, ParallelityCollec>,
    view_ctx: &mut HashMap<String, ViewExpr>,
) -> cu::Stmt {
    let mut v = ViewExpr::create_from(input_view, view_ctx);
    let (pid, sync_stmt) = match parall_collec.ty.as_ref().unwrap() {
        desc::Ty::Data(desc::DataTy::Grid(_, _)) => (
            desc::Nat::Ident(desc::Ident::new("blockIdx.x")),
            cu::Stmt::Expr(cu::Expr::Empty),
        ),
        desc::Ty::Data(desc::DataTy::Block(_, _)) => (
            desc::Nat::Ident(desc::Ident::new("threadIdx.x")),
            cu::Stmt::Expr(cu::Expr::FunCall {
                fun: Box::new(cu::Expr::Ident("__syncthreads".to_string())),
                template_args: vec![],
                args: vec![],
            }),
        ),
        _ => panic!("Not a parallel collection type."),
    };

    // FIXME this assumes that the only functions given are syntactically lambdas
    let fun_bodies = match funs.ty.as_ref().unwrap() {
        desc::Ty::View(desc::ViewTy::Tuple(_)) => unimplemented!(),
        desc::Ty::Data(_) => panic!("Cannot generate function body from expression of data type."),
        desc::Ty::Fn(_, _, _, _) => {
            if let desc::ExprKind::Lambda(params, _, _, body) = &funs.expr {
                let parall_collec = params[0].ident.clone();
                let mut scope_parall_ctx: HashMap<String, ParallelityCollec> = HashMap::new();
                scope_parall_ctx.insert(
                    parall_collec.name.clone(),
                    ParallelityCollec::Ident(parall_collec),
                );
                let input_ident = &params[1].ident;
                let mut scope_view_ctx: HashMap<String, ViewExpr> = HashMap::new();
                let res = scope_view_ctx.insert(
                    input_ident.name.clone(),
                    ViewExpr::Idx {
                        idx: pid.clone(),
                        view: Box::new(v),
                    },
                );
                if res.is_some() {
                    panic!(
                        "Conflicting names. View variable `{}` used twice.",
                        input_ident.name
                    )
                }
                gen_stmt(body, false, &mut scope_parall_ctx, &mut scope_view_ctx)
            } else {
                panic!("Did not find a lambda as argument to par_for.")
            }
        }
        _ => panic!("Expected Lambda or tuple view of Lambda."),
    };

    let p = ParallelityCollec::create_from(parall_collec, parall_ctx);
    let body = if let Some((Some(parall_cond), _)) = gen_parall_cond(&pid, &p) {
        cu::Stmt::If {
            cond: parall_cond,
            body: Box::new(cu::Stmt::Block(Box::new(fun_bodies))),
        }
    } else {
        fun_bodies
    };

    cu::Stmt::Seq(Box::new(body), Box::new(sync_stmt))
}

fn gen_expr(
    expr: &desc::Expr,
    parall_ctx: &mut HashMap<String, ParallelityCollec>,
    view_ctx: &mut HashMap<String, ViewExpr>,
) -> cu::Expr {
    use desc::ExprKind::*;
    match &expr.expr {
        Lit(l) => gen_lit(*l),
        PlaceExpr(pl_expr) => gen_pl_expr(pl_expr, view_ctx),
        BinOp(op, lhs, rhs) => cu::Expr::BinOp {
            op: match op {
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
            },
            lhs: Box::new(gen_expr(lhs, parall_ctx, view_ctx)),
            rhs: Box::new(gen_expr(rhs, parall_ctx, view_ctx)),
        },
        UnOp(op, arg) => cu::Expr::UnOp {
            op: match op {
                desc::UnOp::Deref => cu::UnOp::Deref,
                desc::UnOp::Not => cu::UnOp::Not,
                desc::UnOp::Neg => cu::UnOp::Neg,
            },
            arg: Box::new(gen_expr(arg, parall_ctx, view_ctx)),
        },
        Index(pl_expr, i) => cu::Expr::ArraySubscript {
            array: Box::new(gen_pl_expr(pl_expr, view_ctx)),
            index: i.clone(),
        },
        Ref(_, _, pl_expr) => cu::Expr::Ref(Box::new(gen_pl_expr(pl_expr, view_ctx))),
        BorrowIndex(_, _, pl_expr, n) => cu::Expr::Ref(Box::new(cu::Expr::ArraySubscript {
            array: Box::new(gen_pl_expr(pl_expr, view_ctx)),
            index: n.clone(),
        })),
        Assign(pl_expr, expr) => cu::Expr::Assign {
            lhs: Box::new(gen_pl_expr(pl_expr, view_ctx)),
            rhs: Box::new(gen_expr(expr, parall_ctx, view_ctx)),
        },
        Lambda(params, exec, ty, expr) => cu::Expr::Lambda {
            params: gen_param_decls(params.as_slice()),
            body: Box::new(gen_stmt(
                expr,
                !matches!(ty.as_ref(), desc::DataTy::Scalar(desc::ScalarTy::Unit)),
                parall_ctx,
                view_ctx,
            )),
            ret_ty: gen_ty(&desc::Ty::Data(ty.as_ref().clone()), desc::Mutability::Mut).unwrap(),
            is_dev_fun: is_dev_fun(*exec),
        },
        App(fun, kinded_args, args) => cu::Expr::FunCall {
            fun: Box::new(gen_expr(fun, parall_ctx, view_ctx)),
            template_args: gen_args_kinded(kinded_args),
            args: args
                .iter()
                .map(|e| gen_expr(e, parall_ctx, view_ctx))
                .collect::<Vec<_>>(),
        },
        IfElse(cond, e_tt, e_ff) => unimplemented!(),
        Array(elems) => cu::Expr::FunCall {
            fun: Box::new(cu::Expr::Ident("descend::create_array".to_string())),
            template_args: vec![],
            args: elems
                .iter()
                .map(|e| gen_expr(e, parall_ctx, view_ctx))
                .collect::<Vec<_>>(),
        },
        Tuple(elems) => cu::Expr::Tuple(
            elems
                .iter()
                .map(|el| gen_expr(el, parall_ctx, view_ctx))
                .collect::<Vec<_>>(),
        ),
        _ => panic!(
            "Trying to generate expression from what can only be generated to a statement:\n{:?}",
            &expr
        ),
    }
}

fn gen_lit(l: desc::Lit) -> cu::Expr {
    match l {
        desc::Lit::Bool(b) => cu::Expr::Lit(cu::Lit::Bool(b)),
        desc::Lit::I32(i) => cu::Expr::Lit(cu::Lit::I32(i)),
        desc::Lit::F32(f) => cu::Expr::Lit(cu::Lit::F32(f)),
        desc::Lit::Unit => cu::Expr::Empty,
    }
}

fn gen_pl_expr(pl_expr: &desc::PlaceExpr, view_ctx: &HashMap<String, ViewExpr>) -> cu::Expr {
    match &pl_expr {
        desc::PlaceExpr::Ident(ident) => {
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
        desc::PlaceExpr::Proj(pl, n) => cu::Expr::Proj {
            tuple: Box::new(gen_pl_expr(pl.as_ref(), view_ctx)),
            n: *n,
        },
        desc::PlaceExpr::Deref(ple) => {
            // If an identifier that refers to an unwrapped view expression is being dereferenced,
            // just generate from the view expression and omit generating the dereferencing.
            // The dereferencing will happen through indexing.
            match ple.to_place() {
                Some(pl) if view_ctx.contains_key(&pl.ident.name) => gen_view(
                    view_ctx.get(&pl.ident.name).unwrap(),
                    pl.path.iter().map(|n| desc::Nat::Lit(*n)).collect(),
                ),
                _ => cu::Expr::Deref(Box::new(gen_pl_expr(ple.as_ref(), view_ctx))),
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

fn gen_view(view_expr: &ViewExpr, mut path: Vec<desc::Nat>) -> cu::Expr {
    fn gen_indexing(expr: cu::Expr, path: &[desc::Nat]) -> cu::Expr {
        path.iter().fold(expr, |e, idx| cu::Expr::ArraySubscript {
            array: Box::new(e),
            index: idx.clone(),
        })
    }

    match (view_expr, path.as_slice()) {
        (ViewExpr::ToView { ref_expr, .. }, _) => {
            path.reverse();
            gen_indexing(
                gen_expr(ref_expr, &mut HashMap::new(), &mut HashMap::new()),
                &path,
            )
        }
        (ViewExpr::Idx { idx, view }, _) => {
            path.push(idx.clone());
            gen_view(view, path)
        }
        (ViewExpr::Proj { view, i }, _) => {
            path.push(desc::Nat::Lit(*i));
            gen_view(view, path)
        }
        (ViewExpr::SplitAt { pos, view }, _) => {
            let proj = path.pop();
            let idx = path.pop();
            match (proj, idx) {
                (Some(pr), Some(i)) => match pr.eval() {
                    Ok(v) => {
                        if v == 0 {
                            path.push(i);
                            gen_view(view, path)
                        } else if v == 1 {
                            path.push(desc::Nat::BinOp(
                                desc::BinOpNat::Add,
                                Box::new(i),
                                Box::new(pos.clone()),
                            ));
                            gen_view(view, path)
                        } else {
                            panic!("split_at can only generate a 2-tuple view.")
                        }
                    }
                    Err(m) => panic!(m),
                },
                _ => panic!("Cannot create SplitAt view. Index or projection missing."),
            }
        }
        (ViewExpr::Join { m, n, view }, _) => unimplemented!(),
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
                    gen_view(view, path)
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
                        gen_view(inner_view, path)
                    }
                    Err(m) => panic!(m),
                },
                _ => panic!("Cannot generate Zip View. Index or projection missing."),
            }
        }
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
    param_decls.iter().filter_map(gen_param_decl).collect()
}

fn gen_param_decl(param_decl: &desc::ParamDecl) -> Option<cu::ParamDecl> {
    let desc::ParamDecl { ident, ty, mutbl } = param_decl;
    let ty = gen_ty(ty, *mutbl);
    if let Some(tty) = ty {
        Some(cu::ParamDecl {
            name: ident.name.clone(),
            ty: tty,
        })
    } else {
        None
    }
}

fn gen_args_kinded(templ_args: &[desc::ArgKinded]) -> Vec<cu::TemplateArg> {
    templ_args.iter().filter_map(gen_arg_kinded).collect()
}

fn gen_arg_kinded(templ_arg: &desc::ArgKinded) -> Option<cu::TemplateArg> {
    match templ_arg {
        // desc::ArgKinded::Ident(ident) => match kind_ctx.get(&ident.name).unwrap() {
        //     desc::Kind::Ty => Some(cu::TemplateArg::Ty(cu::Ty::Ident(ident.name.clone()))),
        //     desc::Kind::Nat => Some(cu::TemplateArg::Expr(cu::Expr::Nat(desc::Nat::Ident(
        //         ident.clone(),
        //     )))),
        //     desc::Kind::Memory | desc::Kind::Provenance | desc::Kind::Frame | desc::Kind::Exec => {
        //         None
        //     }
        // },
        desc::ArgKinded::Nat(n) => Some(cu::TemplateArg::Expr(cu::Expr::Nat(n.clone()))),
        desc::ArgKinded::Ty(ty @ desc::Ty::Data(_)) => {
            if let Some(tty) = gen_ty(ty, desc::Mutability::Mut) {
                Some(cu::TemplateArg::Ty(tty))
            } else {
                None
            }
        }
        desc::ArgKinded::Ty(desc::Ty::Ident(_)) => unimplemented!("This will require inlining all view types \
         such that we know that the only identifiers left are data types. This will enable simply passing the \
         identifiers around in C."),
        desc::ArgKinded::Ty(desc::Ty::View(_)) => None,
        desc::ArgKinded::Ty(desc::Ty::Fn(_, _, _, _)) => unimplemented!("needed?"),
        desc::ArgKinded::Memory(_)
        | desc::ArgKinded::Provenance(_)
        | desc::ArgKinded::Ident(_) => None,
    }
}

// Param mutbl is not strictly necessary because every const type can just be wrapped
// in cu::Ty::Const. However, the formalism uses this, because it shows the generated code
// as opposed to a Cuda-AST and there, the order of the const is different
// when it comes to pointers (C things).
fn gen_ty(ty: &desc::Ty, mutbl: desc::Mutability) -> Option<cu::Ty> {
    use desc::DataTy as d;
    use desc::Ty::*;

    let m = desc::Mutability::Mut;
    let cu_ty = match ty {
        Ident(ident) => Some(cu::Ty::Ident(ident.name.clone())),
        Fn(_, _, _, _) => unimplemented!("needed?"),
        Data(d::Scalar(s)) => Some(match s {
            desc::ScalarTy::Unit => cu::Ty::Scalar(cu::ScalarTy::Void),
            desc::ScalarTy::I32 => cu::Ty::Scalar(cu::ScalarTy::I32),
            desc::ScalarTy::F32 => cu::Ty::Scalar(cu::ScalarTy::I32),
            desc::ScalarTy::Bool => cu::Ty::Scalar(cu::ScalarTy::Bool),
            desc::ScalarTy::Gpu => cu::Ty::Scalar(cu::ScalarTy::Gpu),
            desc::ScalarTy::Thread => panic!("This should only exist for type checking."),
        }),
        Data(d::Tuple(tys)) => {
            let gened_tys: Vec<_> = tys
                .iter()
                .filter_map(|ty| gen_ty(&Data(ty.clone()), m))
                .collect();
            if gened_tys.len() == 0 {
                None
            } else {
                Some(cu::Ty::Tuple(gened_tys))
            }
        }
        Data(d::Array(ty, n)) => Some(cu::Ty::Array(
            Box::new(gen_ty(&Data(ty.as_ref().clone()), m).unwrap()),
            n.clone(),
        )),
        Data(d::At(ty, mem)) => {
            let buff_kind = match mem {
                desc::Memory::CpuHeap => cu::BufferKind::Heap,
                desc::Memory::GpuGlobal => cu::BufferKind::Gpu,
                desc::Memory::Ident(ident) => cu::BufferKind::Ident(ident.name.clone()),
                desc::Memory::GpuShared => unimplemented!("big TODO!"),
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
            Some(cu::Ty::Buffer(
                Box::new(gen_ty(&Data(ty.as_ref().clone()), m).unwrap()),
                buff_kind,
            ))
        }
        Data(d::Dead(_)) => {
            panic!("Dead types are only for type checking and cannot be generated.")
        }
        Data(d::Ref(_, own, _, ty)) => {
            let tty = Box::new(
                gen_ty(
                    &Data(match ty.as_ref() {
                        // Pointers to arrays point to the element type.
                        desc::DataTy::Array(elem_ty, _) => elem_ty.as_ref().clone(),
                        _ => ty.as_ref().clone(),
                    }),
                    m,
                )
                .unwrap(),
            );
            Some(if matches!(own, desc::Ownership::Uniq) {
                cu::Ty::Ptr(tty)
            } else {
                cu::Ty::PtrConst(tty)
            })
        }
        // TODO is this correct. I guess we want to generate type identifiers in generic functions.
        Data(d::Ident(ident)) => Some(cu::Ty::Ident(ident.name.clone())),
        Data(d::GridConfig(num_blocks, num_threads)) => {
            //cu::Ty::GridConfig(num_blocks.clone(), num_threads.clone())
            unimplemented!()
        }
        Data(d::Grid(_, _)) | Data(d::Block(_, _)) => None,
        Data(d::DistribBorrow(_, _)) => unimplemented!(),
        View(_) => None,
        //     panic!(
        //     "Cannot generate view types. Anything with this type should have been compiled away."
        // ),
    };

    if matches!(mutbl, desc::Mutability::Mut) {
        cu_ty
    } else {
        if let Some(cu_tty) = cu_ty {
            Some(cu::Ty::Const(Box::new(cu_tty)))
        } else {
            None
        }
    }
}

// TODO correct?
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
    match ty {
        desc::Ty::Data(desc::DataTy::Array(_, n)) => Some(n.clone()),
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
                if let desc::ExprKind::PlaceExpr(PlaceExpr::Ident(ident)) = &f.expr {
                    if ident.name == crate::ty_check::pre_decl::SPLIT {
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
                        panic!("Cannot create `group` from the provided arguments.");
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
            desc::PlaceExpr::Ident(ident) => parall_ctx.get(&ident.name).unwrap().clone(),
            desc::PlaceExpr::Proj(pp, i) => ParallelityCollec::Proj {
                parall_expr: Box::new(ParallelityCollec::create_parall_pl_expr(pp, parall_ctx)),
                i: *i,
            },
            desc::PlaceExpr::Deref(_) => panic!(
                "It is not possible to take references of Grids or Blocks.\
                This should never happen."
            ),
        }
    }
}

fn is_parall_collec_ty(ty: &desc::Ty) -> bool {
    match ty {
        desc::Ty::Data(desc::DataTy::Grid(_, _)) | desc::Ty::Data(desc::DataTy::Block(_, _)) => {
            true
        }
        desc::Ty::Data(desc::DataTy::Tuple(vec)) => vec
            .iter()
            .all(|dty| is_parall_collec_ty(&desc::Ty::Data(dty.clone()))),
        _ => false,
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
        if !matches!(expr.ty, Some(desc::Ty::View(_))) {
            panic!(
                "Expected expression of type ArrayView, but found {:?}",
                expr.ty
            );
        }

        match &expr.expr {
            // TODO this is assuming that f is an identifier
            //  We have to redesign Views to not be data types...
            desc::ExprKind::App(f, gen_args, args) => {
                if let desc::ExprKind::PlaceExpr(PlaceExpr::Ident(ident)) = &f.expr {
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
            desc::PlaceExpr::Ident(ident) => view_ctx.get(&ident.name).unwrap().clone(),
            desc::PlaceExpr::Proj(vv, i) => ViewExpr::Proj {
                view: Box::new(ViewExpr::create_pl_expr_view(vv, view_ctx)),
                i: *i,
            },
            desc::PlaceExpr::Deref(_) => {
                panic!("It is not possible to take references of views. This should never happen.")
            }
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

    fn collect_and_rename_pl_exprs(&mut self) -> Vec<(String, desc::Expr)> {
        fn collect_and_rename_pl_exprs_rec(
            v: &mut ViewExpr,
            count: &mut u32,
            mut vec: Vec<(String, desc::Expr)>,
        ) -> Vec<(String, desc::Expr)> {
            match v {
                ViewExpr::ToView { ref_expr: pl_expr } => {
                    let new_name = format!("p{}", *count);
                    vec.push((new_name.clone(), pl_expr.as_ref().clone()));
                    pl_expr.expr = desc::ExprKind::PlaceExpr(desc::PlaceExpr::Ident(
                        desc::Ident::new(&new_name),
                    ));
                    *count = *count + 1;
                    vec
                }
                ViewExpr::Group { view, .. } => collect_and_rename_pl_exprs_rec(view, count, vec),
                ViewExpr::Join { view, .. } => collect_and_rename_pl_exprs_rec(view, count, vec),
                ViewExpr::Transpose { view, .. } => {
                    collect_and_rename_pl_exprs_rec(view, count, vec)
                }
                ViewExpr::Zip { views, .. } => {
                    let mut renamed = vec;
                    for v in views {
                        renamed = collect_and_rename_pl_exprs_rec(v, count, renamed);
                    }
                    renamed
                }
                _ => unimplemented!(),
            }
        }
        let vec = vec![];
        let mut count = 0;
        collect_and_rename_pl_exprs_rec(self, &mut count, vec)
    }
}

fn replace_arg_kinded_idents(fun_def: &desc::FunDef) -> desc::FunDef {
    use crate::ast::visit;
    use crate::ast::visit::Visitor;
    use desc::*;
    struct ReplaceArgKindedIdents {
        kinds: HashMap<String, Kind>,
    };
    impl Visitor for ReplaceArgKindedIdents {
        fn visit_fun_def(&mut self, fun_def: &mut FunDef) {
            self.kinds = fun_def
                .generic_params
                .iter()
                .map(|desc::IdentKinded { ident, kind }| (ident.name.clone(), kind.clone()))
                .collect();
            visit::walk_fun_def(self, fun_def)
        }

        fn visit_expr(&mut self, expr: &mut Expr) {
            match &mut expr.expr {
                ExprKind::LetProv(prvs, body) => {
                    self.kinds
                        .extend(prvs.iter().map(|prv| (prv.clone(), Kind::Provenance)));
                    self.visit_expr(body)
                }
                ExprKind::App(f, gen_args, args) => {
                    self.visit_expr(f);
                    for gen_arg in gen_args {
                        if let ArgKinded::Ident(ident) = gen_arg {
                            let to_be_kinded = ident.clone();
                            match self.kinds.get(&ident.name).unwrap() {
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
                                    *gen_arg = ArgKinded::Ty(Ty::Data(DataTy::Ident(to_be_kinded)))
                                }
                                _ => panic!("This kind can not be referred to with an identifier."),
                            }
                        }
                    }
                    walk_list!(self, visit_expr, args)
                }
                ExprKind::ForNat(ident, _, body) => {
                    self.kinds
                        .extend(iter::once((ident.name.clone(), Kind::Nat)));
                    self.visit_expr(body)
                }
                _ => visit::walk_expr(self, expr),
            }
        }
    }
    let mut replace = ReplaceArgKindedIdents {
        kinds: HashMap::new(),
    };
    let mut replaced_fun = fun_def.clone();
    replace.visit_fun_def(&mut replaced_fun);
    replaced_fun
}

#[cfg(test)]
mod tests {
    use crate::codegen::gen_fun_def;

    #[test]
    fn test_scalar_mult() {
        let sclar_mult_fun = r#"fn scalar_mult<a: prv>(
            h_array: &a uniq cpu.heap [i32; 4096]
        ) -[cpu.thread]-> i32 {
            let answer_to_everything: i32 = 42;
            answer_to_everything
        }"#;

        let res = crate::parser::parse_global_fun_def(sclar_mult_fun).unwrap();
        print!("{}", gen_fun_def(&res));
    }
}
