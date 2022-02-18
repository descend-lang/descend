mod cu_ast;
mod printer;

use crate::ast as desc;
use crate::ast::visit_mut::VisitMut;
use crate::ast::{CompilUnit, DataTy, DataTyKind, Ident, PlaceExprKind, ThreadHierchyTy, TyKind};
use cu_ast as cu;
use std::collections::HashMap;
use std::fmt::Debug;
use std::iter;
use std::sync::atomic::{AtomicI32, Ordering};

// Precondition. all function definitions are successfully typechecked and
// therefore every subexpression stores a type
pub fn gen(compil_unit: &CompilUnit, idx_checks: bool) -> String {
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
                !is_shape_ty(p.ty.as_ref().unwrap())
                    && !matches!(
                        &p.ty.as_ref().unwrap().ty,
                        desc::TyKind::Data(DataTy {
                            dty: DataTyKind::ThreadHierchy(_),
                            ..
                        })
                    )
            })
        })
        .cloned()
        .collect::<Vec<desc::FunDef>>();
    let cu_program = std::iter::once(cu::Item::Include("descend.cuh".to_string()))
        .chain(
            fun_defs_to_be_generated
                .iter()
                .map(|fun_def| gen_fun_def(fun_def, &preproc_fun_defs, idx_checks)),
        )
        .collect::<cu::CuProgram>();
    printer::print(&cu_program)
}

// TODO extract into own module, hide ScopeCtx, and ParallCtx and provide wrapper functions in CodegenCtx
struct CodegenCtx {
    parall_ctx: ParallCtx,
    shape_ctx: ShapeCtx,
}

impl CodegenCtx {
    fn new() -> Self {
        CodegenCtx {
            parall_ctx: ParallCtx::new(),
            shape_ctx: ShapeCtx::new(),
        }
    }

    fn push_scope(&mut self) {
        self.parall_ctx.push_scope();
        self.shape_ctx.push_scope();
    }

    fn drop_scope(&mut self) {
        self.parall_ctx.drop_scope();
        self.shape_ctx.drop_scope();
    }
}

type ParallCtx = ScopeCtx<ParallelityCollec>;
type ShapeCtx = ScopeCtx<ShapeExpr>;

#[derive(Default, Clone, Debug)]
struct ScopeCtx<T: Debug + Clone> {
    map: Vec<HashMap<String, T>>,
}

impl<T: Debug + Clone> ScopeCtx<T> {
    fn new() -> Self {
        ScopeCtx {
            map: vec![HashMap::new()],
        }
    }

    fn insert(&mut self, ident: &str, key: T) {
        match self.map.last_mut() {
            Some(map) => {
                if let Some(old) = map.insert(ident.to_string(), key.clone()) {
                    panic!(
                        "Reassigning variable from `{i} = {old:?}` to `{i} = {new:?}`",
                        i = ident,
                        old = old,
                        new = key
                    )
                }
            }
            None => panic!("No scoped mapping found."),
        }
    }

    fn get(&self, ident: &str) -> &T {
        for scope in self.map.iter().rev() {
            if let Some(key) = scope.get(ident) {
                return key;
            }
        }
        panic!("Identifier `{}` not in context.", ident)
    }

    fn contains_key(&self, ident: &str) -> bool {
        self.map.iter().rev().any(|scope| scope.contains_key(ident))
    }

    fn push_scope(&mut self) {
        self.map.push(HashMap::new())
    }

    fn drop_scope(&mut self) {
        if let None = self.map.pop() {
            panic!("There is no scope to remove.")
        }
    }
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

    fn expr(&self) -> &cu::Expr {
        match self {
            Self::Expr(e) => e,
            Self::ExprIdxCheck(c, e) => panic!("expected expr, found idxCheck"),
        }
    }
}

fn gen_fun_def(gl_fun: &desc::FunDef, comp_unit: &[desc::FunDef], idx_checks: bool) -> cu::Item {
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
        body: gen_stmt(
            body_expr,
            !matches!(
                ret_ty,
                desc::DataTy {
                    dty: DataTyKind::Scalar(desc::ScalarTy::Unit),
                    ..
                }
            ),
            &mut CodegenCtx::new(),
            comp_unit,
            false,
            idx_checks,
        ),
        is_dev_fun: is_dev_fun(*exec),
    }
}

// Generate CUDA code for Descend syntax that allows sequencing.
fn gen_stmt(
    expr: &desc::Expr,
    return_value: bool,
    codegen_ctx: &mut CodegenCtx,
    comp_unit: &[desc::FunDef],
    dev_fun: bool,
    idx_checks: bool,
) -> cu::Stmt {
    use desc::DataTyKind::*;
    use desc::ExprKind::*;
    match &expr.expr {
        Let(mutbl, ident, _, e) => {
            // Let View
            if is_shape_ty(e.ty.as_ref().unwrap()) {
                codegen_ctx.shape_ctx.insert(
                    &ident.name,
                    ShapeExpr::create_from(e, &codegen_ctx.shape_ctx),
                );
                cu::Stmt::Skip
            // Let Expression
            } else if is_parall_collec_ty(e.ty.as_ref().unwrap()) {
                codegen_ctx.parall_ctx.insert(
                    &ident.name,
                    ParallelityCollec::create_from(e, &codegen_ctx.parall_ctx),
                );
                cu::Stmt::Skip
            } else if let desc::TyKind::Data(desc::DataTy {
                dty: At(dty, desc::Memory::GpuShared),
                ..
            }) = &e.ty.as_ref().unwrap().ty
            {
                let cu_ty = if let desc::DataTy {
                    dty: DataTyKind::Array(elem_dty, n),
                    ..
                } = dty.as_ref()
                {
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
                cu::Stmt::VarDecl {
                    name: ident.name.clone(),
                    ty: cu_ty,
                    addr_space: Some(cu::GpuAddrSpace::Shared),
                    expr: None,
                }
            } else {
                let gened_ty = gen_ty(&e.ty.as_ref().unwrap().ty, *mutbl);
                let (init_expr, cu_ty, checks) = match gened_ty {
                    cu::Ty::Array(_, _) => {
                        let (ex, ch) =
                            match gen_expr(e, codegen_ctx, comp_unit, dev_fun, idx_checks) {
                                CheckedExpr::Expr(e) => (e, None),
                                CheckedExpr::ExprIdxCheck(c, e) => (e, Some(c)),
                            };
                        (ex, gened_ty, ch)
                    }
                    _ => {
                        let (ex, ch) =
                            match gen_expr(e, codegen_ctx, comp_unit, dev_fun, idx_checks) {
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
                let var_decl = cu::Stmt::VarDecl {
                    name: ident.name.clone(),
                    ty: cu_ty,
                    addr_space: None,
                    expr: Some(init_expr),
                };
                if !idx_checks || checks.is_none() {
                    var_decl
                } else {
                    cu::Stmt::Seq(vec![checks.unwrap(), var_decl])
                }
            }
        }
        LetUninit(ident, ty) => cu::Stmt::VarDecl {
            name: ident.name.clone(),
            ty: gen_ty(&ty.as_ref().ty, desc::Mutability::Mut),
            addr_space: None,
            expr: None,
        },
        Block(_, expr) => {
            codegen_ctx.push_scope();
            let block_stmt = gen_stmt(
                expr,
                return_value,
                codegen_ctx,
                comp_unit,
                dev_fun,
                idx_checks,
            );
            codegen_ctx.drop_scope();
            cu::Stmt::Block(Box::new(block_stmt))
        }
        // e1 ; e2
        Seq(s) => {
            let (last, leading) = s.split_last().unwrap();
            let mut stmts = leading
                .iter()
                .map(|stmt| gen_stmt(stmt, false, codegen_ctx, comp_unit, dev_fun, idx_checks))
                .collect::<Vec<_>>();
            stmts.append(&mut vec![gen_stmt(
                last,
                return_value,
                codegen_ctx,
                comp_unit,
                dev_fun,
                idx_checks,
            )]);
            let mut stmts_seq = vec![];
            for stmt in stmts {
                stmts_seq.push(stmt);
            }
            cu::Stmt::Seq(stmts_seq)
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

            cu::Stmt::ForLoop {
                init: Box::new(init),
                cond, // TODO needs some kind of checking
                iter,
                stmt: Box::new(gen_stmt(
                    body,
                    false,
                    codegen_ctx,
                    comp_unit,
                    dev_fun,
                    idx_checks,
                )),
            }
        }
        While(cond, body) => cu::Stmt::While {
            cond: match gen_expr(cond, codegen_ctx, comp_unit, dev_fun, idx_checks) {
                CheckedExpr::Expr(expr) => expr,
                CheckedExpr::ExprIdxCheck(_, expr) => {
                    println!("found a condition in while-loop which needs checks!"); // TODO implement checks
                    expr
                }
            },
            stmt: Box::new(gen_stmt(
                body,
                false,
                codegen_ctx,
                comp_unit,
                dev_fun,
                idx_checks,
            )),
        },
        For(ident, coll_expr, body) => {
            if matches!(
                coll_expr.ty.as_ref().unwrap().ty,
                desc::TyKind::Data(desc::DataTy {
                    dty: DataTyKind::Range,
                    ..
                })
            ) {
                gen_for_range(
                    ident,
                    coll_expr,
                    body,
                    codegen_ctx,
                    comp_unit,
                    dev_fun,
                    idx_checks,
                )
            } else {
                gen_for_each(
                    ident,
                    coll_expr,
                    body,
                    codegen_ctx,
                    comp_unit,
                    dev_fun,
                    idx_checks,
                )
            }
        }
        ParForWith(decls, parall_ident, parall_collec, input_idents, input_exprs, body) => {
            gen_par_for(
                decls,
                parall_ident,
                parall_collec,
                input_idents,
                input_exprs,
                body,
                codegen_ctx,
                comp_unit,
                idx_checks,
            )
        }
        // FIXME this assumes that IfElse is not an Expression.
        IfElse(cond, e_tt, e_ff) => {
            match gen_expr(cond, codegen_ctx, comp_unit, dev_fun, idx_checks) {
                CheckedExpr::ExprIdxCheck(check, con) => cu::Stmt::Seq(vec![
                    check,
                    gen_if_else(con, e_tt, e_ff, codegen_ctx, comp_unit, dev_fun, idx_checks),
                ]),
                CheckedExpr::Expr(con) => {
                    gen_if_else(con, e_tt, e_ff, codegen_ctx, comp_unit, dev_fun, idx_checks)
                }
            }
        }
        _ => {
            if return_value {
                match gen_expr(&expr, codegen_ctx, comp_unit, dev_fun, idx_checks) {
                    CheckedExpr::ExprIdxCheck(ch, e) if idx_checks => {
                        cu::Stmt::Seq(vec![ch, cu::Stmt::Return(Some(e))])
                    }
                    CheckedExpr::ExprIdxCheck(_, e) => cu::Stmt::Return(Some(e)),
                    CheckedExpr::Expr(e) => cu::Stmt::Return(Some(e)),
                }
            } else {
                match gen_expr(&expr, codegen_ctx, comp_unit, dev_fun, idx_checks) {
                    CheckedExpr::ExprIdxCheck(ch, e) if idx_checks => {
                        cu::Stmt::Seq(vec![ch, cu::Stmt::Return(Some(e))])
                    }
                    CheckedExpr::ExprIdxCheck(_, e) => cu::Stmt::Return(Some(e)),
                    CheckedExpr::Expr(e) => cu::Stmt::Expr(e),
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
    codegen_ctx: &mut CodegenCtx,
    comp_unit: &[desc::FunDef],
    dev_fun: bool,
    idx_checks: bool,
) -> cu::Stmt {
    cu::Stmt::IfElse {
        cond: cond,
        true_body: Box::new(gen_stmt(
            e_tt,
            false,
            codegen_ctx,
            comp_unit,
            dev_fun,
            idx_checks,
        )),
        false_body: Box::new(gen_stmt(
            e_ff,
            false,
            codegen_ctx,
            comp_unit,
            dev_fun,
            idx_checks,
        )),
    }
}

fn gen_for_each(
    ident: &Ident,
    coll_expr: &desc::Expr,
    body: &desc::Expr,
    codegen_ctx: &mut CodegenCtx,
    comp_unit: &[desc::FunDef],
    dev_fun: bool,
    idx_checks: bool,
) -> cu::Stmt {
    let i_name = crate::ast::utils::fresh_name("i__");
    let i_decl = cu::Stmt::VarDecl {
        name: i_name.clone(),
        ty: cu::Ty::Scalar(cu::ScalarTy::SizeT),
        addr_space: None,
        expr: Some(cu::Expr::Lit(cu::Lit::I32(0))),
    };
    let i = cu::Expr::Ident(i_name.to_string());
    codegen_ctx.shape_ctx.push_scope();
    codegen_ctx.shape_ctx.insert(
        &ident.name,
        ShapeExpr::Idx {
            idx: desc::Nat::Ident(Ident::new(&i_name)),
            shape: Box::new(if is_shape_ty(coll_expr.ty.as_ref().unwrap()) {
                ShapeExpr::create_from(coll_expr, &codegen_ctx.shape_ctx)
            } else {
                ShapeExpr::ToView {
                    ref_expr: Box::new(coll_expr.clone()),
                }
            }),
        },
    );

    let for_loop = cu::Stmt::ForLoop {
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
        stmt: Box::new(gen_stmt(
            body,
            false,
            codegen_ctx,
            comp_unit,
            dev_fun,
            idx_checks,
        )),
    };

    codegen_ctx.shape_ctx.drop_scope();
    for_loop
}

fn gen_for_range(
    ident: &Ident,
    range: &desc::Expr,
    body: &desc::Expr,
    codegen_ctx: &mut CodegenCtx,
    comp_unit: &[desc::FunDef],
    dev_fun: bool,
    idx_checks: bool,
) -> cu::Stmt {
    if let desc::ExprKind::Range(l, u) = &range.expr {
        let lower = gen_expr(l, codegen_ctx, comp_unit, dev_fun, idx_checks);
        let upper = gen_expr(u, codegen_ctx, comp_unit, dev_fun, idx_checks);

        let i_name = ident.name.clone();
        let i_decl = cu::Stmt::VarDecl {
            name: i_name.clone(),
            ty: cu::Ty::Scalar(cu::ScalarTy::SizeT),
            addr_space: None,
            expr: Some(lower.expr().clone()),
        };
        let i = cu::Expr::Ident(i_name.to_string());

        cu::Stmt::ForLoop {
            init: Box::new(i_decl),
            cond: cu::Expr::BinOp {
                op: cu::BinOp::Lt,
                lhs: Box::new(i.clone()),
                rhs: Box::new(upper.expr().clone()),
            },
            iter: cu::Expr::Assign {
                lhs: Box::new(i.clone()),
                rhs: Box::new(cu::Expr::BinOp {
                    op: cu::BinOp::Add,
                    lhs: Box::new(i),
                    rhs: Box::new(cu::Expr::Lit(cu::Lit::I32(1))),
                }),
            },
            stmt: Box::new(gen_stmt(
                body,
                false,
                codegen_ctx,
                comp_unit,
                dev_fun,
                idx_checks,
            )),
        }
    } else {
        panic!("Expected range expression")
    }
}

fn gen_exec(
    blocks: &desc::ArgKinded,
    threads: &desc::ArgKinded,
    gpu_expr: &desc::Expr,
    shape_expr: &desc::Expr,
    fun: &desc::Expr,
    codegen_ctx: &mut CodegenCtx,
    comp_unit: &[desc::FunDef],
    idx_checks: bool,
) -> CheckedExpr {
    // Prepare parameter declarations for inputs
    let mut input_shape_expr = ShapeExpr::create_from(shape_expr, &codegen_ctx.shape_ctx);
    let name_to_exprs = input_shape_expr.collect_and_rename_input_exprs();
    let mut param_decls: Vec<_> = name_to_exprs
        .iter()
        .map(|(name, expr)| cu::ParamDecl {
            name: name.clone(),
            // TODO why Mutability::Const??!
            ty: gen_ty(&expr.ty.as_ref().unwrap().ty, desc::Mutability::Const),
        })
        .collect();

    if idx_checks {
        param_decls.insert(
            0,
            cu::ParamDecl {
                name: "global_failure".to_string(),
                ty: cu::Ty::Ptr(
                    Box::new(cu::Ty::Scalar(cu::ScalarTy::I32)),
                    Some(cu::GpuAddrSpace::Global),
                ),
            },
        );
    }
    // GPU argument
    let gpu = match gen_expr(gpu_expr, codegen_ctx, comp_unit, true, idx_checks) {
        CheckedExpr::Expr(e) => e,
        CheckedExpr::ExprIdxCheck(_, _) => {
            panic!("Did not expect to check a condition for GPU")
        }
    };

    // FIXME only allows Lambdas
    let dev_fun = if let desc::ExprKind::Lambda(params, _, _, body) = &fun.expr {
        let parall_collec = params[0].ident.clone();
        let mut fresh_parall_codegen_ctx = CodegenCtx {
            parall_ctx: ParallCtx::new(),
            shape_ctx: codegen_ctx.shape_ctx.clone(),
        };
        codegen_ctx.shape_ctx.push_scope();
        fresh_parall_codegen_ctx.parall_ctx.insert(
            &parall_collec.name.clone(),
            ParallelityCollec::Ident(parall_collec),
        );

        // Remember to inline input shape expression
        let in_name = &params[1].ident.name.clone();
        fresh_parall_codegen_ctx
            .shape_ctx
            .insert(in_name, input_shape_expr);

        let gpu_fun_body = gen_stmt(
            body,
            false,
            &mut fresh_parall_codegen_ctx,
            comp_unit,
            true,
            idx_checks,
        );
        let mut global_failure_init = vec![
            cu::Stmt::If {
                cond: cu::Expr::BinOp {
                    lhs: Box::new(cu::Expr::Deref(Box::new(cu::Expr::Ident(
                        "global_failure".to_string(),
                    )))),
                    op: cu::BinOp::Neq,
                    rhs: Box::new(cu::Expr::Lit(cu::Lit::I32(-1))),
                },
                body: Box::new(cu::Stmt::Block(Box::new(cu::Stmt::Return(None)))),
            },
            cu::Stmt::Expr(cu::Expr::FunCall {
                fun: Box::new(cu::Expr::Ident("__syncthreads".to_string())),
                template_args: vec![],
                args: vec![],
            }),
        ];
        let lambda = cu::Expr::Lambda {
            params: param_decls,
            body: Box::new(if idx_checks {
                global_failure_init.push(gpu_fun_body);
                cu::Stmt::Seq(global_failure_init)
            } else {
                gpu_fun_body
            }),
            ret_ty: cu::Ty::Scalar(cu::ScalarTy::Void),
            is_dev_fun: true,
        };

        lambda
    } else {
        panic!("Currently only lambdas can be passed.")
    };
    let mut checks: Vec<cu::Stmt> = vec![];
    let mut input: Vec<_> = name_to_exprs
        .iter()
        .map(
            |(_, pl_expr)| match gen_expr(pl_expr, codegen_ctx, comp_unit, true, idx_checks) {
                CheckedExpr::ExprIdxCheck(check, expr) if idx_checks => {
                    checks.push(check);
                    expr
                }
                CheckedExpr::ExprIdxCheck(_, expr) => expr,
                CheckedExpr::Expr(expr) => expr,
            },
        )
        .collect();
    let template_args = gen_args_kinded(vec![blocks.clone(), threads.clone()].as_slice());
    let mut args: Vec<cu::Expr> = vec![gpu, dev_fun];
    args.append(&mut input);

    if checks.is_empty() {
        CheckedExpr::Expr(cu::Expr::FunCall {
            fun: Box::new(cu::Expr::Ident("descend::exec".to_string())),
            template_args,
            args,
        })
    } else {
        CheckedExpr::ExprIdxCheck(
            cu::Stmt::Seq(checks),
            cu::Expr::FunCall {
                fun: Box::new(cu::Expr::Ident("descend::exec".to_string())),
                template_args,
                args,
            },
        )
    }
}

fn gen_par_for(
    decls: &Option<Vec<desc::Expr>>,
    parall_ident: &Option<desc::Ident>,
    parall_collec: &desc::Expr,
    input_idents: &[Ident],
    inputs: &[desc::Expr],
    body: &desc::Expr,
    codegen_ctx: &mut CodegenCtx,
    comp_unit: &[desc::FunDef],
    idx_checks: bool,
) -> cu::Stmt {
    fn gen_parall_section(
        parall_ident: &Option<desc::Ident>,
        input_idents: &[desc::Ident],
        input_exprs: &[desc::Expr],
        body: &desc::Expr,
        pindex: &desc::Nat,
        codegen_ctx: &mut CodegenCtx,
        comp_unit: &[desc::FunDef],
        idx_checks: bool,
    ) -> cu::Stmt {
        codegen_ctx.push_scope();

        if parall_ident.is_some() {
            let parall_ident = parall_ident.as_ref().unwrap().clone();
            codegen_ctx.parall_ctx.insert(
                &parall_ident.name.clone(),
                ParallelityCollec::Ident(parall_ident),
            );
        }

        for (ident, input_expr) in input_idents
            .iter()
            .map(|ident| ident.name.clone())
            .zip(input_exprs)
        {
            let input_arg_shape = ShapeExpr::create_from(input_expr, &codegen_ctx.shape_ctx);

            codegen_ctx.shape_ctx.insert(
                &ident,
                ShapeExpr::Idx {
                    idx: pindex.clone(),
                    shape: Box::new(input_arg_shape),
                },
            );
        }
        let stmt = gen_stmt(body, false, codegen_ctx, comp_unit, true, idx_checks);

        codegen_ctx.drop_scope();
        stmt
    }

    let (pindex, sync_stmt) = match &parall_collec.ty.as_ref().unwrap().ty {
        // TODO Refactor
        //  The same things exists in ty_check where only threadHierchyTy for elem types is returned
        desc::TyKind::Data(DataTy {
            dty: DataTyKind::ThreadHierchy(th_hy),
            ..
        }) => match th_hy.as_ref() {
            desc::ThreadHierchyTy::BlockGrp(_, _, _, m1, m2, m3) => {
                (desc::Nat::Ident(desc::Ident::new("blockIdx.x")), None)
            }
            desc::ThreadHierchyTy::ThreadGrp(_, _, _) => (
                desc::Nat::Ident(desc::Ident::new("threadIdx.x")),
                Some(cu::Stmt::Expr(cu::Expr::FunCall {
                    fun: Box::new(cu::Expr::Ident("__syncthreads".to_string())),
                    template_args: vec![],
                    args: vec![],
                })),
            ),
            desc::ThreadHierchyTy::WarpGrp(_) => (
                desc::Nat::BinOp(
                    desc::BinOpNat::Div,
                    Box::new(desc::Nat::Ident(desc::Ident::new("threadIdx.x"))),
                    Box::new(desc::Nat::Lit(32)),
                ),
                Some(cu::Stmt::Expr(cu::Expr::FunCall {
                    fun: Box::new(cu::Expr::Ident("__syncthreads".to_string())),
                    template_args: vec![],
                    args: vec![],
                })),
            ),
            desc::ThreadHierchyTy::Warp => (
                desc::Nat::BinOp(
                    desc::BinOpNat::Mod,
                    Box::new(desc::Nat::Ident(desc::Ident::new("threadIdx.x"))),
                    Box::new(desc::Nat::Lit(32)),
                ),
                Some(cu::Stmt::Expr(cu::Expr::FunCall {
                    fun: Box::new(cu::Expr::Ident("__syncwarp()".to_string())),
                    template_args: vec![],
                    args: vec![],
                })),
            ),
        },
        _ => panic!("Not a parallel collection type."),
    };

    let par_section = gen_parall_section(
        parall_ident,
        input_idents,
        inputs,
        body,
        &pindex,
        codegen_ctx,
        comp_unit,
        idx_checks,
    );

    let p = ParallelityCollec::create_from(parall_collec, &codegen_ctx.parall_ctx);
    let body = if let Some((Some(parall_cond), _)) = gen_parall_cond(&pindex, &p) {
        cu::Stmt::If {
            cond: parall_cond,
            body: Box::new(par_section),
        }
    } else {
        par_section
    };

    let cu_decls = match decls {
        Some(decls) => cu::Stmt::Seq(
            decls
                .iter()
                .map(|d| gen_stmt(d, false, &mut CodegenCtx::new(), &[], true, idx_checks))
                .collect(),
        ),
        None => cu::Stmt::Skip,
    };

    let sync_error = if let Some(sync) = sync_stmt {
        if idx_checks {
            cu::Stmt::Seq(vec![
                cu::Stmt::Label(format!("sync_{}", unsafe {
                    LABEL_COUNTER.load(Ordering::SeqCst)
                })),
                sync.clone(),
                cu::Stmt::If {
                    cond: cu::Expr::BinOp {
                        op: cu::BinOp::Neq,
                        lhs: Box::new(cu::Expr::Deref(Box::new(cu::Expr::Ident(
                            "global_failure".to_string(),
                        )))),
                        rhs: Box::new(cu::Expr::Lit(cu::Lit::I32(-1))),
                    },
                    body: Box::new(cu::Stmt::Block(Box::new(cu::Stmt::Return(None)))),
                },
                sync,
            ])
        } else {
            sync
        }
    } else {
        cu::Stmt::Skip
    };

    incr_label_counter();

    cu::Stmt::Seq(vec![cu_decls, body, sync_error])
}

fn gen_check_idx_stmt(
    expr: &desc::Expr,
    comp_unit: &[desc::FunDef],
    is_dev_fun: bool,
    idx_checks: bool,
) -> cu::Stmt {
    use desc::DataTyKind::*;
    use desc::ExprKind::*;
    if let Index(pl_expr, i) = &expr.expr {
        if idx_checks && is_dev_fun {
            let n = match &pl_expr.ty.as_ref().expect(&format!("{:?}", pl_expr)).ty {
                TyKind::Data(DataTy {
                    dty: DataTyKind::Array(_, m),
                    ..
                }) => m,
                TyKind::Data(DataTy {
                    dty: DataTyKind::Ref(_, _, _, a),
                    ..
                }) => match a.as_ref() {
                    DataTy {
                        dty: DataTyKind::Array(_, m),
                        ..
                    } => m,
                    DataTy {
                        dty: ArrayShape(_, m),
                        ..
                    } => m,
                    _ => panic!("cannot index into non array type!"),
                },
                t => panic!("cannot index into non array type! {:?}", t),
            };
            use crate::ast::*;
            cu::Stmt::If {
                cond: cu::Expr::BinOp {
                    op: cu::BinOp::Gt,
                    lhs: Box::new(cu::Expr::Nat(i.clone())),
                    rhs: Box::new(cu::Expr::Nat(n.clone())),
                },
                body: Box::new(cu::Stmt::Block(Box::new(cu::Stmt::Seq(vec![
                    cu::Stmt::Expr(cu::Expr::FunCall {
                        fun: Box::new(cu::Expr::Ident("descend::atomic_set".to_string())),
                        template_args: gen_args_kinded(&vec![ArgKinded::Ty(Ty::new(
                            TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))),
                        ))]),
                        args: vec![
                            cu::Expr::Ident("global_failure".to_string()),
                            cu::Expr::Lit(cu::Lit::I32(incr_idx_check_counter())),
                        ],
                    }),
                    cu::Stmt::Expr(cu::Expr::Ident(format!("goto sync_{}", unsafe {
                        LABEL_COUNTER.load(Ordering::SeqCst)
                    }))),
                ])))),
            }
        } else {
            cu::Stmt::Skip
        }
    } else {
        panic!(
            "cannot generate index statement from non index expression: {:?}",
            expr
        )
    }
}

fn gen_expr(
    expr: &desc::Expr,
    codegen_ctx: &mut CodegenCtx,
    comp_unit: &[desc::FunDef],
    dev_fun: bool,
    idx_checks: bool,
) -> CheckedExpr {
    use desc::ExprKind::*;

    match &expr.expr {
        Lit(l) => CheckedExpr::Expr(gen_lit(*l)),
        PlaceExpr(pl_expr) => CheckedExpr::Expr(gen_pl_expr(
            pl_expr,
            &codegen_ctx.shape_ctx,
            comp_unit,
            idx_checks,
        )),
        Proj(tuple, idx) => {
            if is_shape_ty(expr.ty.as_ref().unwrap()) {
                CheckedExpr::Expr(gen_shape(
                    &ShapeExpr::create_from(expr, &codegen_ctx.shape_ctx),
                    vec![],
                    &codegen_ctx.shape_ctx,
                    comp_unit,
                    idx_checks,
                ))
            } else {
                gen_expr(tuple, codegen_ctx, comp_unit, dev_fun, idx_checks).map(|e| {
                    cu::Expr::Proj {
                        tuple: Box::new(e),
                        n: *idx,
                    }
                })
            }
        }
        BinOp(op, lhs, rhs) => {
            gen_bin_op_expr(op, lhs, rhs, codegen_ctx, comp_unit, dev_fun, idx_checks)
        }
        UnOp(op, arg) => {
            gen_expr(arg, codegen_ctx, comp_unit, dev_fun, idx_checks).map(|e| cu::Expr::UnOp {
                op: match op {
                    desc::UnOp::Not => cu::UnOp::Not,
                    desc::UnOp::Neg => cu::UnOp::Neg,
                },
                arg: Box::new(e),
            })
        }
        Ref(_, _, pl_expr) => match &expr.ty.as_ref().unwrap().ty {
            desc::TyKind::Data(desc::DataTy {
                dty: DataTyKind::Ref(_, _, desc::Memory::GpuShared, _),
                ..
            }) => CheckedExpr::Expr(gen_pl_expr(
                pl_expr,
                &codegen_ctx.shape_ctx,
                comp_unit,
                idx_checks,
            )),
            _ => CheckedExpr::Expr(cu::Expr::Ref(Box::new(gen_pl_expr(
                pl_expr,
                &codegen_ctx.shape_ctx,
                comp_unit,
                idx_checks,
            )))),
        },
        BorrowIndex(_, _, pl_expr, n) => {
            if contains_shape_expr(pl_expr, &codegen_ctx.shape_ctx) {
                panic!("It should not be allowed to borrow from a shape expression.")
            } else {
                CheckedExpr::Expr(cu::Expr::Ref(Box::new(cu::Expr::ArraySubscript {
                    array: Box::new(gen_pl_expr(
                        pl_expr,
                        &codegen_ctx.shape_ctx,
                        comp_unit,
                        idx_checks,
                    )),
                    index: n.clone(),
                })))
            }
        }
        Index(pl_expr, idx) => {
            if contains_shape_expr(pl_expr, &codegen_ctx.shape_ctx) {
                CheckedExpr::ExprIdxCheck(
                    gen_check_idx_stmt(&expr, comp_unit, dev_fun, idx_checks),
                    gen_idx_into_shape(pl_expr, idx, &codegen_ctx.shape_ctx, comp_unit, idx_checks),
                )
            } else {
                CheckedExpr::ExprIdxCheck(
                    gen_check_idx_stmt(&expr, comp_unit, dev_fun, idx_checks),
                    cu::Expr::ArraySubscript {
                        array: Box::new(gen_pl_expr(
                            pl_expr,
                            &codegen_ctx.shape_ctx,
                            comp_unit,
                            idx_checks,
                        )),
                        index: idx.clone(),
                    },
                )
            }
        }
        IdxAssign(pl_expr, idx, expr) => {
            gen_expr(expr, codegen_ctx, comp_unit, dev_fun, idx_checks).map(|e| cu::Expr::Assign {
                lhs: Box::new(if contains_shape_expr(pl_expr, &codegen_ctx.shape_ctx) {
                    gen_idx_into_shape(pl_expr, idx, &codegen_ctx.shape_ctx, comp_unit, idx_checks)
                } else {
                    cu::Expr::ArraySubscript {
                        array: Box::new(gen_pl_expr(
                            pl_expr,
                            &codegen_ctx.shape_ctx,
                            comp_unit,
                            idx_checks,
                        )),
                        index: idx.clone(),
                    }
                }),
                rhs: Box::new(e),
            })
        }
        Assign(pl_expr, expr) => {
            gen_expr(expr, codegen_ctx, comp_unit, dev_fun, idx_checks).map(|e| cu::Expr::Assign {
                lhs: Box::new(gen_pl_expr(
                    pl_expr,
                    &codegen_ctx.shape_ctx.clone(),
                    comp_unit,
                    idx_checks,
                )),
                rhs: Box::new(e),
            })
        }
        Lambda(params, exec, ty, expr) => CheckedExpr::Expr(cu::Expr::Lambda {
            params: gen_param_decls(params.as_slice()),
            body: Box::new(gen_stmt(
                expr,
                !matches!(
                    ty.as_ref(),
                    desc::DataTy {
                        dty: DataTyKind::Scalar(desc::ScalarTy::Unit),
                        ..
                    }
                ),
                codegen_ctx,
                comp_unit,
                dev_fun,
                idx_checks,
            )),
            ret_ty: gen_ty(
                &desc::TyKind::Data(ty.as_ref().clone()),
                desc::Mutability::Mut,
            ),
            is_dev_fun: is_dev_fun(*exec),
        }),
        App(fun, kinded_args, args) => match &fun.expr {
            desc::ExprKind::PlaceExpr(desc::PlaceExpr {
                pl_expr: PlaceExprKind::Ident(name),
                ..
            }) if name.name == "exec" => gen_exec(
                &kinded_args[0],
                &kinded_args[1],
                &args[0],
                &args[1],
                &args[2],
                codegen_ctx,
                comp_unit,
                idx_checks,
            ),
            desc::ExprKind::PlaceExpr(desc::PlaceExpr {
                pl_expr: PlaceExprKind::Ident(ident),
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
                            codegen_ctx,
                            comp_unit,
                            dev_fun,
                            idx_checks,
                        ) {
                            CheckedExpr::Expr(expr) | CheckedExpr::ExprIdxCheck(_, expr) => expr,
                        },
                    ),
                    template_args: gen_args_kinded(kinded_args),
                    args: args
                        .iter()
                        .map(
                            |e| match gen_expr(e, codegen_ctx, comp_unit, dev_fun, idx_checks) {
                                CheckedExpr::Expr(expr) | CheckedExpr::ExprIdxCheck(_, expr) => {
                                    expr
                                }
                            },
                        )
                        .collect::<Vec<_>>(),
                })
            }
            _ => {
                let (reduced_fun, data_args, red_kinded_args) = match create_lambda_no_shape_args(
                    fun.as_ref(),
                    kinded_args.as_slice(),
                    args.as_slice(),
                    codegen_ctx,
                    comp_unit,
                ) {
                    Some((reduced_fun, data_args)) => (reduced_fun, data_args, vec![]),
                    None => (*fun.clone(), args.clone(), kinded_args.clone()),
                };
                CheckedExpr::Expr(cu::Expr::FunCall {
                    fun: Box::new({
                        match gen_expr(&reduced_fun, codegen_ctx, comp_unit, dev_fun, idx_checks) {
                            CheckedExpr::Expr(expr) | CheckedExpr::ExprIdxCheck(_, expr) => expr,
                        }
                    }),
                    template_args: gen_args_kinded(&red_kinded_args),
                    args: data_args
                        .iter()
                        .map(
                            |e| match gen_expr(e, codegen_ctx, comp_unit, dev_fun, idx_checks) {
                                CheckedExpr::Expr(expr) | CheckedExpr::ExprIdxCheck(_, expr) => {
                                    expr
                                }
                            },
                        )
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
            gen_expr(&inst_fun, codegen_ctx, comp_unit, dev_fun, idx_checks)
        }
        Array(elems) => CheckedExpr::Expr(cu::Expr::InitializerList {
            elems: elems
                .iter()
                .map(
                    |e| match gen_expr(e, codegen_ctx, comp_unit, dev_fun, idx_checks) {
                        CheckedExpr::Expr(expr) => expr,
                        CheckedExpr::ExprIdxCheck(_, _) => {
                            panic!("Elements of an array should not have to be checked!")
                        }
                    },
                )
                .collect(),
        }),
        // cu::Expr::FunCall {
        //     fun: Box::new(cu::Expr::Ident("descend::create_array".to_string())),
        //     template_args: vec![],
        //     args: elems
        //         .iter()
        //         .map(|e| gen_expr(e, parall_ctx, shape_ctx))
        //         .collect::<Vec<_>>(),
        // },
        Tuple(elems) => CheckedExpr::Expr(cu::Expr::Tuple(
            elems
                .iter()
                .map(
                    |el| match gen_expr(el, codegen_ctx, comp_unit, dev_fun, idx_checks) {
                        CheckedExpr::Expr(expr) => expr,
                        CheckedExpr::ExprIdxCheck(_, _) => {
                            panic!("Elements of a tuple should not have to be checked!")
                        }
                    },
                )
                .collect::<Vec<_>>(),
        )),
        Deref(e) => CheckedExpr::Expr(cu::Expr::Deref(Box::new(
            match gen_expr(e, codegen_ctx, comp_unit, dev_fun, idx_checks) {
                CheckedExpr::Expr(expr) => expr,
                CheckedExpr::ExprIdxCheck(_, _) => {
                    panic!("did not expect a check after deref!")
                }
            },
        ))),
        Idx(e, i) => CheckedExpr::Expr(cu::Expr::ArraySubscript {
            array: Box::new(
                match gen_expr(e, codegen_ctx, comp_unit, dev_fun, idx_checks) {
                    CheckedExpr::Expr(expr) => expr,
                    CheckedExpr::ExprIdxCheck(_, _) => panic!("should never happen"),
                },
            ),
            index: i.clone(),
        }),
        Let(_, _, _, _)
        | LetUninit(_, _)
        | Block(_, _)
        | IfElse(_, _, _)
        | Seq(_)
        | While(_, _)
        | For(_, _, _)
        | ForNat(_, _, _)
        | ParForWith(_, _, _, _, _, _) => panic!(
            "Trying to generate a statement where an expression is expected:\n{:?}",
            &expr
        ),
        Split(_, _, _, _, _) => {
            panic!("The split operator should have been descontructed by now.")
        }
        TupleView(_) => {
            panic!("All tuple shape should have been deconstructed using projections by now.")
        }
        Range(_, _) => {
            panic!("Range should be deconstructed at a different place.")
        }
    }
}

fn gen_bin_op_expr(
    op: &desc::BinOp,
    lhs: &desc::Expr,
    rhs: &desc::Expr,
    codegen_ctx: &mut CodegenCtx,
    comp_unit: &[desc::FunDef],
    dev_fun: bool,
    idx_checks: bool,
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
            gen_expr(lhs, codegen_ctx, comp_unit, dev_fun, idx_checks),
            gen_expr(rhs, codegen_ctx, comp_unit, dev_fun, idx_checks),
        ) {
            (ce::ExprIdxCheck(ch1, e1), ce::ExprIdxCheck(ch2, e2)) => CheckedExpr::ExprIdxCheck(
                cu::Stmt::Seq(vec![ch1, ch2]),
                cu::Expr::BinOp {
                    op: op,
                    lhs: Box::new(e1),
                    rhs: Box::new(e2),
                },
            ),
            (ce::Expr(e1), ce::ExprIdxCheck(ch, e2)) | (ce::ExprIdxCheck(ch, e1), ce::Expr(e2)) => {
                CheckedExpr::ExprIdxCheck(
                    ch,
                    cu::Expr::BinOp {
                        op: op,
                        lhs: Box::new(e1),
                        rhs: Box::new(e2),
                    },
                )
            }
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
        pl_expr: PlaceExprKind::Ident(ident),
        ..
    }) = &ident.expr
    {
        ident.clone()
    } else {
        panic!("Generic functions must be global functions.")
    }
}

fn contains_shape_expr(pl_expr: &desc::PlaceExpr, shape_ctx: &ShapeCtx) -> bool {
    let (_, pl) = pl_expr.to_pl_ctx_and_most_specif_pl();
    shape_ctx.contains_key(&pl.ident.name)
}

fn gen_idx_into_shape(
    pl_expr: &desc::PlaceExpr,
    idx: &desc::Nat,
    shape_ctx: &ShapeCtx,
    comp_unit: &[desc::FunDef],
    idx_checks: bool,
) -> cu::Expr {
    let collec_shape = ShapeExpr::create_from(
        &desc::Expr::new(desc::ExprKind::PlaceExpr(pl_expr.clone())),
        shape_ctx,
    );
    gen_shape(
        &ShapeExpr::Idx {
            idx: idx.clone(),
            shape: Box::new(collec_shape),
        },
        vec![],
        shape_ctx,
        comp_unit,
        idx_checks,
    )
}

fn create_lambda_no_shape_args(
    fun: &desc::Expr,
    generic_args: &[desc::ArgKinded],
    args: &[desc::Expr],
    codegen_ctx: &mut CodegenCtx,
    comp_unit: &[desc::FunDef],
) -> Option<(desc::Expr, Vec<desc::Expr>)> {
    // FIXME doesn't work for predeclared functions which expect a shape type argument
    match &fun.expr {
        desc::ExprKind::Lambda(param_decls, exec, ret_dty, body) => {
            Some(create_lambda_and_args_only_dtys(
                fun,
                param_decls,
                args,
                body,
                *exec,
                ret_dty,
                codegen_ctx,
            ))
        }
        desc::ExprKind::PlaceExpr(desc::PlaceExpr {
            pl_expr: PlaceExprKind::Ident(f),
            ..
        }) => {
            let fun_def = comp_unit
                .iter()
                .find(|fun_def| fun_def.name == f.name)
                .expect("Cannot find function definition.");
            if !contains_shape_or_th_hierchy_params(&fun_def.param_decls) {
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
                codegen_ctx,
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
    codegen_ctx: &mut CodegenCtx,
) -> (desc::Expr, Vec<desc::Expr>) {
    let (data_param_decls, data_args) = separate_param_decls_from_args(
        filter_and_map_shape_th_hierchy_params(param_decls, args, codegen_ctx),
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
            .filter(|p_ty| !is_shape_ty(&p_ty))
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

fn contains_shape_or_th_hierchy_params(param_decls: &[desc::ParamDecl]) -> bool {
    param_decls.iter().any(|p| {
        is_shape_ty(p.ty.as_ref().unwrap())
            || matches!(
                p.ty.as_ref().unwrap().ty,
                desc::TyKind::Data(DataTy {
                    dty: DataTyKind::ThreadHierchy(_),
                    ..
                })
            )
    })
}

fn filter_and_map_shape_th_hierchy_params<'a>(
    param_decls: &'a [desc::ParamDecl],
    args: &'a [desc::Expr],
    codegen_ctx: &mut CodegenCtx,
) -> Vec<(&'a desc::ParamDecl, &'a desc::Expr)> {
    let (reducable_parms_with_args, data_params_with_args): (Vec<_>, Vec<_>) =
        param_decls.iter().zip(args.iter()).partition(|&(p, _)| {
            is_shape_ty(p.ty.as_ref().unwrap())
                || matches!(
                    &p.ty.as_ref().unwrap().ty,
                    desc::TyKind::Data(DataTy {
                        dty: DataTyKind::ThreadHierchy(_),
                        ..
                    })
                )
        });
    let (shape_params_with_args, th_hierchy_params_with_args): (Vec<_>, Vec<_>) =
        reducable_parms_with_args
            .iter()
            .partition(|&(p, _)| is_shape_ty(p.ty.as_ref().unwrap()));
    for (p, arg) in shape_params_with_args {
        codegen_ctx.shape_ctx.insert(
            &p.ident.name,
            ShapeExpr::create_from(arg, &codegen_ctx.shape_ctx),
        );
    }
    for (p, arg) in th_hierchy_params_with_args {
        codegen_ctx.parall_ctx.insert(
            &p.ident.name,
            ParallelityCollec::create_from(arg, &codegen_ctx.parall_ctx),
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
    shape_ctx: &ShapeCtx,
    comp_unit: &[desc::FunDef],
    idx_checks: bool,
) -> cu::Expr {
    match &pl_expr {
        desc::PlaceExpr {
            pl_expr: PlaceExprKind::Ident(ident),
            ..
        } => {
            if shape_ctx.contains_key(&ident.name) {
                gen_shape(
                    &shape_ctx.get(&ident.name),
                    vec![],
                    shape_ctx,
                    comp_unit,
                    idx_checks,
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
            pl_expr: PlaceExprKind::Proj(pl, n),
            ..
        } => match pl_expr.to_place() {
            // FIXME this does not work when there are tuples inside of shape tuples
            Some(p) if shape_ctx.contains_key(&p.ident.name) => gen_shape(
                &shape_ctx.get(&p.ident.name),
                p.path.iter().map(|n| desc::Nat::Lit(*n)).collect(),
                shape_ctx,
                comp_unit,
                idx_checks,
            ),
            _ => cu::Expr::Proj {
                tuple: Box::new(gen_pl_expr(pl.as_ref(), shape_ctx, comp_unit, idx_checks)),
                n: *n,
            },
        },
        desc::PlaceExpr {
            pl_expr: PlaceExprKind::Deref(ple),
            ..
        } => {
            // If an identifier that refers to an unwrapped shape expression is being dereferenced,
            // just generate from the shape expression and omit generating the dereferencing.
            // The dereferencing will happen through indexing.
            match ple.to_place() {
                Some(pl) if shape_ctx.contains_key(&pl.ident.name) => gen_shape(
                    &shape_ctx.get(&pl.ident.name),
                    pl.path.iter().map(|n| desc::Nat::Lit(*n)).collect(),
                    shape_ctx,
                    comp_unit,
                    idx_checks,
                ),
                _ => cu::Expr::Deref(Box::new(gen_pl_expr(
                    ple.as_ref(),
                    shape_ctx,
                    comp_unit,
                    idx_checks,
                ))),
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

fn gen_shape(
    shape_expr: &ShapeExpr,
    mut path: Vec<desc::Nat>,
    shape_ctx: &ShapeCtx,
    comp_unit: &[desc::FunDef],
    idx_checks: bool,
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

    match (shape_expr, path.as_slice()) {
        (ShapeExpr::ToView { ref_expr, .. }, _) => {
            path.reverse();
            gen_indexing(
                match gen_expr(
                    ref_expr,
                    &mut CodegenCtx {
                        parall_ctx: ParallCtx::new(),
                        shape_ctx: shape_ctx.clone(),
                    },
                    comp_unit,
                    false,
                    idx_checks,
                ) {
                    CheckedExpr::Expr(e) => e,
                    CheckedExpr::ExprIdxCheck(_, _) => panic!("should never happen"),
                },
                &path,
            )
        }
        (ShapeExpr::Tuple { shapes: shapes }, [path @ .., prj]) => match prj.eval() {
            Ok(i) => match &shapes[i] {
                ViewOrExpr::V(shape_expr) => {
                    gen_shape(shape_expr, path.to_vec(), shape_ctx, comp_unit, idx_checks)
                }
                ViewOrExpr::E(expr) => gen_shape(
                    &ShapeExpr::ToView {
                        ref_expr: Box::new(expr.clone()),
                    },
                    path.to_vec(),
                    shape_ctx,
                    comp_unit,
                    idx_checks,
                ), // gen_expr(expr, &mut HashMap::new(), shape_ctx, comp_unit),
            },
            Err(e) => panic!("{:?}", e),
        },
        (ShapeExpr::Idx { idx, shape: shape }, _) => {
            path.push(idx.clone());
            gen_shape(shape, path, shape_ctx, comp_unit, idx_checks)
        }
        (ShapeExpr::Proj { shape, i }, _) => {
            path.push(desc::Nat::Lit(*i));
            gen_shape(shape, path, shape_ctx, comp_unit, idx_checks)
        }
        (ShapeExpr::SplitAt { pos, shape }, _) => {
            let proj = path.pop();
            let idx = path.pop();
            match (proj, idx) {
                (Some(pr), Some(i)) => match pr.eval() {
                    Ok(v) => {
                        if v == 0 {
                            path.push(i);
                            gen_shape(shape, path, shape_ctx, comp_unit, idx_checks)
                        } else if v == 1 {
                            path.push(desc::Nat::BinOp(
                                desc::BinOpNat::Add,
                                Box::new(i),
                                Box::new(pos.clone()),
                            ));
                            gen_shape(shape, path, shape_ctx, comp_unit, idx_checks)
                        } else {
                            panic!("split_at can only generate a 2-tuple shape.")
                        }
                    }
                    Err(m) => panic!("{:?}", m),
                },
                _ => panic!("Cannot create SplitAt shape. Index or projection missing."),
            }
        }
        (ShapeExpr::Group { size, n, shape }, _) => {
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
                    gen_shape(shape, path, shape_ctx, comp_unit, idx_checks)
                }
                (Some(i), None) => {
                    path.push(desc::Nat::BinOp(
                        desc::BinOpNat::Mul,
                        Box::new(i),
                        Box::new(size.clone()),
                    ));
                    gen_shape(shape, path, shape_ctx, comp_unit, idx_checks)
                }
                _ => panic!("Cannot generate Group shape. One or more indices missing."),
            }
        }
        (ShapeExpr::Zip { n, shapes }, _) => {
            let idx = path.pop();
            let proj = path.pop();
            match (idx, proj) {
                (Some(i), Some(pr)) => match pr.eval() {
                    Ok(v) => {
                        let inner_shape = &shapes[v];
                        path.push(i);
                        gen_shape(inner_shape, path, shape_ctx, comp_unit, idx_checks)
                    }
                    Err(m) => panic!("{:?}", m),
                },
                _ => panic!("Cannot generate Zip View. Index or projection missing."),
            }
        }
        (ShapeExpr::Join { m, n, shape }, _) => unimplemented!(),
        (ShapeExpr::Transpose { m, n, shape }, _) => unimplemented!(),
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
        ty: gen_ty(&ty.as_ref().unwrap().ty, *mutbl),
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
            ty: desc::TyKind::TupleView(_),
            ..
        }) => None,
        desc::ArgKinded::Ty(desc::Ty {
            ty:
                desc::TyKind::Data(DataTy {
                    dty: DataTyKind::ThreadHierchy(_),
                    ..
                }),
            ..
        }) => None,
        desc::ArgKinded::Ty(desc::Ty {
            ty: desc::TyKind::Fn(_, _, _, _),
            ..
        }) => unimplemented!("needed?"),
        desc::ArgKinded::DataTy(_)
        | desc::ArgKinded::Memory(_)
        | desc::ArgKinded::Provenance(_)
        | desc::ArgKinded::Ident(_) => None,
        desc::ArgKinded::Ty(desc::Ty {
            ty: desc::TyKind::Dead(_),
            ..
        }) => panic!("Dead types cannot be generated."),
    }
}

// Param mutbl is not strictly necessary because every const type can just be wrapped
// in cu::Ty::Const. However, the formalism uses this, because it shows the generated code
// as opposed to a Cuda-AST and there, the order of the const is different
// when it comes to pointers (C things).
fn gen_ty(ty: &desc::TyKind, mutbl: desc::Mutability) -> cu::Ty {
    use desc::DataTyKind as d;
    use desc::TyKind::*;

    let m = desc::Mutability::Mut;
    let cu_ty = match ty {
        Ident(ident) => cu::Ty::Ident(ident.name.clone()),
        Data(DataTy {
            dty: d::Atomic(a), ..
        }) => match a {
            desc::ScalarTy::Unit => cu::Ty::Atomic(cu::ScalarTy::Void),
            desc::ScalarTy::I32 => cu::Ty::Atomic(cu::ScalarTy::I32),
            desc::ScalarTy::U32 => cu::Ty::Atomic(cu::ScalarTy::U32),
            desc::ScalarTy::F32 => cu::Ty::Atomic(cu::ScalarTy::F32),
            desc::ScalarTy::Bool => cu::Ty::Atomic(cu::ScalarTy::Bool),
            desc::ScalarTy::Gpu => cu::Ty::Atomic(cu::ScalarTy::Gpu),
        },
        Data(DataTy {
            dty: d::Scalar(s), ..
        }) => match s {
            desc::ScalarTy::Unit => cu::Ty::Scalar(cu::ScalarTy::Void),
            desc::ScalarTy::I32 => cu::Ty::Scalar(cu::ScalarTy::I32),
            desc::ScalarTy::U32 => cu::Ty::Scalar(cu::ScalarTy::U32),
            desc::ScalarTy::F32 => cu::Ty::Scalar(cu::ScalarTy::F32),
            desc::ScalarTy::Bool => cu::Ty::Scalar(cu::ScalarTy::Bool),
            desc::ScalarTy::Gpu => cu::Ty::Scalar(cu::ScalarTy::Gpu),
        },
        Data(DataTy {
            dty: d::Tuple(tys), ..
        }) => cu::Ty::Tuple(tys.iter().map(|ty| gen_ty(&Data(ty.clone()), m)).collect()),
        Data(DataTy {
            dty: d::Array(ty, n),
            ..
        }) => cu::Ty::Array(Box::new(gen_ty(&Data(ty.as_ref().clone()), m)), n.clone()),
        Data(DataTy {
            dty: d::At(ty, mem),
            ..
        }) => {
            if let desc::Memory::GpuShared = mem {
                let dty = match ty.as_ref() {
                    DataTy {
                        dty: d::Array(dty, _),
                        ..
                    } => dty.as_ref().clone(),
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
        Data(DataTy {
            dty: d::Ref(_, own, _, ty),
            ..
        }) => {
            let tty = Box::new(gen_ty(
                &Data(match ty.as_ref() {
                    // Pointers to arrays point to the element type.
                    desc::DataTy {
                        dty: d::Array(elem_ty, _),
                        ..
                    } => elem_ty.as_ref().clone(),
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
        Data(DataTy {
            dty: d::RawPtr(ty), ..
        }) => {
            let tty = Box::new(gen_ty(
                &Data(match ty.as_ref() {
                    desc::DataTy {
                        dty: d::Array(elem_ty, _),
                        ..
                    } => panic!("should never happen"),
                    _ => ty.as_ref().clone(),
                }),
                desc::Mutability::Mut,
            ));
            cu::Ty::Ptr(tty, None)
        }
        // TODO is this correct. I guess we want to generate type identifiers in generic functions.
        Data(DataTy {
            dty: d::Ident(ident),
            ..
        }) => cu::Ty::Ident(ident.name.clone()),
        Data(DataTy {
            dty: d::ArrayShape(_, _),
            ..
        }) => panic!(
            "Cannot generate array shape types.\
            Anything with this type should have been compiled away."
        ),
        Data(DataTy {
            dty: d::Dead(_), ..
        }) => {
            panic!("Dead types are only for type checking and cannot be generated.")
        }
        Fn(_, _, _, _) => unimplemented!("needed?"),
        TupleView(_) => panic!(
            "Cannot generate tuple shape types.\
            Anything with this type should have been compiled away."
        ),
        Range => panic!("Range types cannot be generated."),
        Dead(_) => panic!("Dead types cannot be generated."),
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
        desc::TyKind::Data(desc::DataTy {
            dty: DataTyKind::Array(_, n),
            ..
        }) => Some(n.clone()),
        desc::TyKind::Data(desc::DataTy {
            dty: DataTyKind::Ref(_, _, _, arr),
            ..
        }) => match arr.as_ref() {
            desc::DataTy {
                dty: DataTyKind::Array(_, n),
                ..
            } => Some(n.clone()),
            desc::DataTy {
                dty: DataTyKind::ArrayShape(_, n),
                ..
            } => Some(n.clone()),
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
    fn create_from(expr: &desc::Expr, parall_ctx: &ParallCtx) -> ParallelityCollec {
        match &expr.expr {
            desc::ExprKind::App(f, gen_args, args) => {
                if let desc::ExprKind::PlaceExpr(desc::PlaceExpr {
                    pl_expr: PlaceExprKind::Ident(ident),
                    ..
                }) = &f.expr
                {
                    if ident.name == crate::ty_check::pre_decl::SPLIT_THREAD_GRP {
                        if let (TyKind::Fn(_, _, _, ret_ty), Some(p)) =
                            (&f.ty.as_ref().unwrap().ty, args.first())
                        {
                            if let (
                                TyKind::TupleView(elem_tys),
                                TyKind::Data(DataTy {
                                    dty: DataTyKind::ThreadHierchy(th_hierchy),
                                    ..
                                }),
                            ) = (&ret_ty.as_ref().ty, &p.ty.as_ref().unwrap().ty)
                            {
                                if let (
                                    TyKind::Data(DataTy {
                                        dty: DataTyKind::ThreadHierchy(th_hrchy),
                                        ..
                                    }),
                                    ThreadHierchyTy::ThreadGrp(n1, n2, n3),
                                ) = (&elem_tys.first().unwrap().ty, th_hierchy.as_ref())
                                {
                                    if let ThreadHierchyTy::ThreadGrp(k, _, _) = th_hrchy.as_ref() {
                                        return ParallelityCollec::Split {
                                            pos: k.clone(),
                                            coll_size: n1.clone(),
                                            parall_expr: Box::new(ParallelityCollec::create_from(
                                                p, parall_ctx,
                                            )),
                                        };
                                    }
                                }
                            }
                        }
                        panic!("Cannot create `split` from the provided arguments.");
                    } else if ident.name == crate::ty_check::pre_decl::SPLIT_WARP {
                        unimplemented!("Needs to take generic arguments from function type.");
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
        parall_ctx: &ParallCtx,
    ) -> ParallelityCollec {
        match parall_expr {
            desc::PlaceExpr {
                pl_expr: PlaceExprKind::Ident(ident),
                ..
            } => parall_ctx.get(&ident.name).clone(),
            desc::PlaceExpr {
                pl_expr: PlaceExprKind::Proj(pp, i),
                ..
            } => ParallelityCollec::Proj {
                parall_expr: Box::new(ParallelityCollec::create_parall_pl_expr(pp, parall_ctx)),
                i: *i,
            },
            desc::PlaceExpr {
                pl_expr: PlaceExprKind::Deref(_),
                ..
            } => panic!(
                "It is not possible to take references of Grids or Blocks.\
                This should never happen."
            ),
        }
    }
}

fn is_parall_collec_ty(ty: &desc::Ty) -> bool {
    matches!(
        ty.ty,
        desc::TyKind::Data(DataTy {
            dty: DataTyKind::ThreadHierchy(_),
            ..
        })
    )
}

#[derive(Debug, Clone)]
enum ViewOrExpr {
    V(ShapeExpr),
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
// During code generation shape function applications are converted to View Variants and used
// to generate Indices.
#[derive(Debug, Clone)]
enum ShapeExpr {
    ToView {
        ref_expr: Box<desc::Expr>,
    },
    Tuple {
        shapes: Vec<ViewOrExpr>,
    },
    Idx {
        idx: desc::Nat,
        shape: Box<ShapeExpr>,
    },
    Proj {
        shape: Box<ShapeExpr>,
        i: usize,
    },
    SplitAt {
        pos: desc::Nat,
        shape: Box<ShapeExpr>,
    },
    Group {
        size: desc::Nat,
        n: desc::Nat,
        shape: Box<ShapeExpr>,
    },
    Join {
        m: desc::Nat,
        n: desc::Nat,
        shape: Box<ShapeExpr>,
    },

    Zip {
        n: desc::Nat,
        shapes: Vec<ShapeExpr>,
    },
    Transpose {
        m: desc::Nat,
        n: desc::Nat,
        shape: Box<ShapeExpr>,
    },
}

impl ShapeExpr {
    // Precondition: Expression is a fully typed function application and has type ArrayView.
    fn create_from(expr: &desc::Expr, shape_ctx: &ShapeCtx) -> ShapeExpr {
        match &expr.expr {
            // TODO this is assuming that f is an identifier
            desc::ExprKind::App(f, gen_args, args) => {
                if let desc::ExprKind::PlaceExpr(desc::PlaceExpr {
                    pl_expr: PlaceExprKind::Ident(ident),
                    ..
                }) = &f.expr
                {
                    let f_ty = &f.ty.as_ref().unwrap().ty;
                    if ident.name == crate::ty_check::pre_decl::TO_VIEW
                        || ident.name == crate::ty_check::pre_decl::TO_VIEW_MUT
                    {
                        ShapeExpr::create_to_shape_shape(args)
                    } else if ident.name == crate::ty_check::pre_decl::GROUP
                        || ident.name == crate::ty_check::pre_decl::GROUP_MUT
                    {
                        ShapeExpr::create_group_shape(args, f_ty, shape_ctx)
                    // } else if ident.name == crate::ty_check::pre_decl::JOIN {
                    //     ShapeExpr::create_join_shape(args, f_ty, shape_ctx)
                    // } else if ident.name == crate::ty_check::pre_decl::ZIP {
                    //     ShapeExpr::create_zip_shape(args, f_ty, shape_ctx)
                    // } else if ident.name == crate::ty_check::pre_decl::TRANSPOSE {
                    //     ShapeExpr::create_transpose_shape(args, f_ty, shape_ctx)
                    } else {
                        unimplemented!()
                    }
                } else {
                    panic!("Non-globally defined shape functions do not exist.")
                }
            }
            desc::ExprKind::Split(_, _, _, s, shape) => {
                ShapeExpr::create_split_at_shape(s, shape.as_ref(), shape_ctx)
            }
            desc::ExprKind::PlaceExpr(pl_expr) => {
                ShapeExpr::create_pl_expr_shape(pl_expr, shape_ctx)
            }
            desc::ExprKind::TupleView(elems) => ShapeExpr::create_tuple_shape(elems, shape_ctx),
            desc::ExprKind::Proj(expr, i) => ShapeExpr::Proj {
                shape: Box::new(ShapeExpr::create_from(expr, shape_ctx)),
                i: *i,
            },
            _ => panic!(
                "Expected a function application, identifer or projection, but found {:?}",
                expr.expr
            ),
        }
    }

    fn create_to_shape_shape(args: &[desc::Expr]) -> ShapeExpr {
        match args.first() {
            Some(e) =>
            // e cannot contain shapes, so the shape_ctx can be empty
            {
                ShapeExpr::ToView {
                    ref_expr: Box::new(e.clone()),
                }
            }
            _ => panic!("Place expression argument for to shape does not exist."),
        }
    }

    fn create_pl_expr_shape(shape: &desc::PlaceExpr, shape_ctx: &ShapeCtx) -> ShapeExpr {
        match shape {
            desc::PlaceExpr {
                pl_expr: PlaceExprKind::Ident(ident),
                ..
            } => shape_ctx.get(&ident.name).clone(),
            desc::PlaceExpr {
                pl_expr: PlaceExprKind::Proj(vv, i),
                ..
            } => ShapeExpr::Proj {
                shape: Box::new(ShapeExpr::create_pl_expr_shape(vv, shape_ctx)),
                i: *i,
            },
            desc::PlaceExpr {
                pl_expr: PlaceExprKind::Deref(_),
                ..
            } => {
                panic!("It is not possible to take references of shapes. This should never happen.")
            }
        }
    }

    fn create_tuple_shape(elems: &[desc::Expr], shape_ctx: &ShapeCtx) -> ShapeExpr {
        ShapeExpr::Tuple {
            shapes: elems
                .iter()
                .map(|e| {
                    if is_shape_ty(&e.ty.as_ref().unwrap()) {
                        ViewOrExpr::V(ShapeExpr::create_from(e, shape_ctx))
                    } else {
                        ViewOrExpr::E(e.clone())
                    }
                })
                .collect(),
        }
    }

    fn create_split_at_shape(
        s: &desc::Nat,
        shape: &desc::PlaceExpr,
        shape_ctx: &ShapeCtx,
    ) -> ShapeExpr {
        ShapeExpr::SplitAt {
            pos: s.clone(),
            shape: Box::new(ShapeExpr::create_from(
                &desc::Expr::new(desc::ExprKind::PlaceExpr(shape.clone())),
                shape_ctx,
            )),
        }
    }

    fn create_group_shape(args: &[desc::Expr], f_ty: &TyKind, shape_ctx: &ShapeCtx) -> ShapeExpr {
        if let (desc::TyKind::Fn(_, _, _, ret_ty), Some(v)) = (f_ty, args.first()) {
            if let (
                TyKind::Data(DataTy {
                    dty: DataTyKind::Ref(_, _, _, arr_ty),
                    ..
                }),
                TyKind::Data(DataTy {
                    dty: DataTyKind::Ref(_, _, _, arg_arr_ty),
                    ..
                }),
            ) = (&ret_ty.ty, &v.ty.as_ref().unwrap().ty)
            {
                if let (
                    DataTy {
                        dty: DataTyKind::ArrayShape(inner_ty, _),
                        ..
                    },
                    DataTy {
                        dty: DataTyKind::ArrayShape(_, n),
                        ..
                    },
                ) = (arr_ty.as_ref(), arg_arr_ty.as_ref())
                {
                    if let DataTy {
                        dty: DataTyKind::ArrayShape(_, s),
                        ..
                    } = inner_ty.as_ref()
                    {
                        return ShapeExpr::Group {
                            size: s.clone(),
                            n: n.clone(),
                            shape: Box::new(ShapeExpr::create_from(v, shape_ctx)),
                        };
                    }
                }
            }
        }
        panic!("Cannot create `group` from the provided arguments.");
    }
    //
    // fn create_join_shape(args: &[desc::Expr], f_ty: &TyKind, shape_ctx: &ShapeCtx) -> ShapeExpr {
    //     if let (desc::TyKind::Fn(_, _, _, ret_ty), Some(v)) = (f_ty, args.first()) {
    //     if let (desc::ArgKinded::Nat(m), desc::ArgKinded::Nat(n), Some(v)) =
    //         (&gen_args[0], &gen_args[1], args.first())
    //     {
    //         return ShapeExpr::Join {
    //             m: m.clone(),
    //             n: n.clone(),
    //             shape: Box::new(ShapeExpr::create_from(v, shape_ctx)),
    //         };
    //     }
    //     panic!("Cannot create `to_shape` from the provided arguments.");
    // }

    // fn create_zip_shape(args: &[desc::Expr], f_ty: &TyKind, shape_ctx: &ShapeCtx) -> ShapeExpr {
    //     if let (desc::TyKind::Fn(_, _, _, ret_ty), Some(v)) = (f_ty, &args[0], args[1]) {
    //     if let (desc::ArgKinded::Nat(n), desc::ArgKinded::Ty(t1), desc::ArgKinded::Ty(t2), v1, v2) =
    //         (&gen_args[0], &gen_args[1], &gen_args[2], &args[0], &args[1])
    //     {
    //         return ShapeExpr::Zip {
    //             n: n.clone(),
    //             shapes: vec![
    //                 ShapeExpr::create_from(v1, shape_ctx),
    //                 ShapeExpr::create_from(v2, shape_ctx),
    //             ],
    //         };
    //     }
    //     panic!(
    //         "Cannot create `zip` from the provided arguments:\n{:?},\n{:?},\n{:?}",
    //         &gen_args[0], &gen_args[1], &gen_args[2]
    //     );
    // }

    // fn create_transpose_shape(
    //     args: &[desc::Expr],
    //     f_ty: &TyKind,
    //     shape_ctx: &ShapeCtx,
    // ) -> ShapeExpr {
    //     if let (
    //         desc::ArgKinded::Nat(m),
    //         desc::ArgKinded::Nat(n),
    //         desc::ArgKinded::Ty(ty),
    //         Some(v),
    //     ) = (&gen_args[0], &gen_args[1], &gen_args[2], args.first())
    //     {
    //         return ShapeExpr::Transpose {
    //             m: m.clone(),
    //             n: n.clone(),
    //             shape: Box::new(ShapeExpr::create_from(v, shape_ctx)),
    //         };
    //     }
    //     panic!("Cannot create `to_shape` from the provided arguments.");
    // }

    fn collect_and_rename_input_exprs(&mut self) -> Vec<(String, desc::Expr)> {
        fn collect_and_rename_input_exprs_rec(
            v: &mut ShapeExpr,
            count: &mut u32,
            mut vec: Vec<(String, desc::Expr)>,
        ) -> Vec<(String, desc::Expr)> {
            match v {
                ShapeExpr::ToView { ref_expr } => {
                    let new_name = format!("p{}", *count);
                    vec.push((new_name.clone(), ref_expr.as_ref().clone()));
                    ref_expr.expr = desc::ExprKind::PlaceExpr(desc::PlaceExpr::new(
                        PlaceExprKind::Ident(desc::Ident::new(&new_name)),
                    ));
                    *count += 1;
                    vec
                }
                ShapeExpr::SplitAt { shape: shape, .. } => {
                    collect_and_rename_input_exprs_rec(shape, count, vec)
                }
                ShapeExpr::Group { shape: shape, .. } => {
                    collect_and_rename_input_exprs_rec(shape, count, vec)
                }
                ShapeExpr::Join { shape: shape, .. } => {
                    collect_and_rename_input_exprs_rec(shape, count, vec)
                }
                ShapeExpr::Transpose { shape: shape, .. } => {
                    collect_and_rename_input_exprs_rec(shape, count, vec)
                }
                ShapeExpr::Zip { shapes: shapes, .. } => {
                    let mut renamed = vec;
                    for v in shapes {
                        renamed = collect_and_rename_input_exprs_rec(v, count, renamed);
                    }
                    renamed
                }
                ShapeExpr::Tuple { shapes: elems } => {
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
                ShapeExpr::Idx { shape: shape, .. } => {
                    collect_and_rename_input_exprs_rec(shape, count, vec)
                }
                ShapeExpr::Proj { shape: shape, .. } => {
                    collect_and_rename_input_exprs_rec(shape, count, vec)
                }
            }
        }
        let vec = vec![];
        let mut count = 0;
        collect_and_rename_input_exprs_rec(self, &mut count, vec)
    }
}

fn replace_arg_kinded_idents(mut fun_def: desc::FunDef) -> desc::FunDef {
    use desc::*;
    struct ReplaceArgKindedIdents {
        ident_names_to_kinds: HashMap<String, Kind>,
    }
    impl VisitMut for ReplaceArgKindedIdents {
        fn visit_expr(&mut self, expr: &mut Expr) {
            match &mut expr.expr {
                ExprKind::Block(prvs, body) => {
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
                                        DataTy::new(DataTyKind::Ident(to_be_kinded)),
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
                _ => visit_mut::walk_expr(self, expr),
            }
        }

        fn visit_fun_def(&mut self, fun_def: &mut FunDef) {
            self.ident_names_to_kinds = fun_def
                .generic_params
                .iter()
                .map(|desc::IdentKinded { ident, kind }| (ident.name.clone(), *kind))
                .collect();
            visit_mut::walk_fun_def(self, fun_def)
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

    impl VisitMut for InlineParForFuns<'_> {
        fn visit_expr(&mut self, expr: &mut Expr) {
            match &mut expr.expr {
                ExprKind::ParForWith(_, _, _, _, _, body) => match &mut body.expr {
                    ExprKind::TupleView(t) => {
                        for f in t {
                            match &mut f.expr {
                                ExprKind::PlaceExpr(PlaceExpr {
                                    pl_expr: PlaceExprKind::Ident(x),
                                    ..
                                }) => f.expr = self.create_lambda_from_fun_def(&x.name),
                                _ => visit_mut::walk_expr(self, f),
                            }
                        }
                    }
                    ExprKind::PlaceExpr(PlaceExpr {
                        pl_expr: PlaceExprKind::Ident(x),
                        ..
                    }) => body.expr = self.create_lambda_from_fun_def(&x.name),
                    _ => visit_mut::walk_expr(self, body),
                },
                _ => visit_mut::walk_expr(self, expr),
            }
        }
    }

    let mut inliner = InlineParForFuns { comp_unit };
    inliner.visit_fun_def(&mut fun_def);
    fun_def
}

fn is_shape_ty(ty: &desc::Ty) -> bool {
    match &ty.ty {
        desc::TyKind::Data(desc::DataTy {
            dty: DataTyKind::Ref(_, _, _, arr_vty),
            ..
        }) => {
            matches!(
                arr_vty.as_ref(),
                desc::DataTy {
                    dty: DataTyKind::ArrayShape(_, _),
                    ..
                }
            )
        }
        desc::TyKind::TupleView(_) => true,
        _ => false,
    }
}

static mut LABEL_COUNTER: AtomicI32 = AtomicI32::new(0);
static mut IDX_CHECK_COUNTER: AtomicI32 = AtomicI32::new(0);

fn incr_idx_check_counter() -> i32 {
    incr_atomic_counter(unsafe { &IDX_CHECK_COUNTER })
}

fn incr_label_counter() -> i32 {
    incr_atomic_counter(unsafe { &LABEL_COUNTER })
}

fn incr_atomic_counter(counter: &AtomicI32) -> i32 {
    counter.fetch_add(1, Ordering::SeqCst)
}
