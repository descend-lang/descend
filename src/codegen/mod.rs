mod cu_ast;
mod printer;

use crate::ast as desc;
use crate::ast::visit::Visit;
use crate::ty_check;
use crate::ty_check::matches_dty;
use cu_ast as cu;
use std::collections::HashMap;
use std::fmt::Debug;
use std::sync::atomic::{AtomicI32, Ordering};

// Precondition. all function definitions are successfully typechecked and
// therefore every subexpression stores a type
pub fn gen(comp_unit: &desc::CompilUnit, idx_checks: bool) -> String {
    let initial_fns_to_generate = collect_initial_fns_to_generate(comp_unit);
    let mut codegen_ctx = CodegenCtx::new(
        // CpuThread is only a dummy and will be set according to the generated function.
        desc::ExecExpr::new(desc::Exec::new(desc::BaseExec::CpuThread)),
        &comp_unit.fun_defs,
    );
    let mut initial_fns = Vec::with_capacity(initial_fns_to_generate.len() * 2);
    for fun_def in &initial_fns_to_generate {
        let exec = match &fun_def.exec_decl.ty.ty {
            desc::ExecTyKind::CpuThread => desc::BaseExec::CpuThread,
            desc::ExecTyKind::GpuGrid(gdim, bdim) => {
                desc::BaseExec::GpuGrid(gdim.clone(), bdim.clone())
            }
            _ => unreachable!("Every exec must be constructed based on a gpu grid."),
        };
        codegen_ctx.push_scope();
        codegen_ctx.exec = desc::ExecExpr::new(desc::Exec::new(exec));
        initial_fns.push(gen_fun_def(fun_def, &mut codegen_ctx));
        codegen_ctx.drop_scope();
        debug_assert_eq!(codegen_ctx.shape_ctx.map.len(), 0);
    }

    let cu_fn_defs = codegen_ctx
        .inst_fn_ctx
        .into_values()
        .map(|f| cu::Item::FnDef(Box::new(f)))
        .chain(
            initial_fns
                .into_iter()
                .map(|f| cu::Item::FnDef(Box::new(f))),
        )
        .collect::<Vec<_>>();
    let fn_decls = collect_fn_decls(&cu_fn_defs);
    let include = cu::Item::Include("descend.cuh".to_string());
    let decl_comment = cu::Item::MultiLineComment("function declarations".to_string());
    let def_comment = cu::Item::MultiLineComment("function definitions".to_string());
    let cu_program = std::iter::once(&include)
        .chain(std::iter::once(&decl_comment))
        .chain(&fn_decls)
        .chain(std::iter::once(&def_comment))
        .chain(&cu_fn_defs)
        .collect::<Vec<_>>();
    printer::print(&cu_program)
}

fn collect_initial_fns_to_generate(comp_unit: &desc::CompilUnit) -> Vec<desc::FunDef> {
    comp_unit
        .fun_defs
        .iter()
        // Filter out the only functions that make sense to be generated without an explicit call.
        //
        // As soon as views or exec resources are generic, we need to know the specific values
        // that are used in a function call, so that we can inline them (therefore these functions
        // are not inlcuded).
        // We know the values for GpuGrid, GlobalThreads and CpuThread, because all are unit types.
        .filter(|f| {
            f.param_decls
                .iter()
                .all(|p| !is_view_dty(p.ty.as_ref().unwrap()))
                && matches!(
                    &f.exec_decl.ty.ty,
                    desc::ExecTyKind::GpuGrid(_, _)
                        | desc::ExecTyKind::GpuGlobalThreads(_)
                        | desc::ExecTyKind::CpuThread
                )
        })
        .cloned()
        .collect::<Vec<desc::FunDef>>()
}

fn collect_fn_decls<'a>(items: &'a [cu::Item<'a>]) -> Vec<cu::Item<'a>> {
    items
        .iter()
        .filter_map(|fn_def| {
            if let cu::Item::FnDef(fn_def) = fn_def {
                Some(cu::Item::FunDecl(&fn_def.fn_sig))
            } else {
                None
            }
        })
        .collect()
}

struct CodegenCtx<'a> {
    shape_ctx: ShapeCtx,
    inst_fn_ctx: HashMap<String, cu::FnDef>,
    exec_mapping: ExecMapping,
    exec: desc::ExecExpr,
    comp_unit: &'a [desc::FunDef],
    idx_checks: bool,
}

impl<'a> CodegenCtx<'a> {
    fn new(exec: desc::ExecExpr, comp_unit: &'a [desc::FunDef]) -> Self {
        CodegenCtx {
            shape_ctx: ShapeCtx::new(),
            inst_fn_ctx: HashMap::new(),
            exec_mapping: ExecMapping::new(),
            exec,
            comp_unit,
            idx_checks: false,
        }
    }

    fn push_scope(&mut self) {
        self.shape_ctx.push_scope();
        self.exec_mapping.push_scope();
    }

    fn drop_scope(&mut self) {
        self.shape_ctx.drop_scope();
        self.exec_mapping.drop_scope();
    }
}

type ShapeCtx = ScopeCtx<ShapeExpr>;
type ExecMapping = ScopeCtx<desc::ExecExpr>;

#[derive(Default, Clone, Debug)]
struct ScopeCtx<T: Debug + Clone> {
    map: Vec<HashMap<String, T>>,
}

impl<T: Debug + Clone> ScopeCtx<T> {
    fn new() -> Self {
        ScopeCtx { map: vec![] }
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
    // TODO Wrap in Box
    ExprIdxCheck(cu::Stmt, cu::Expr),
}

impl CheckedExpr {
    fn map<F>(self, f: F) -> Self
    where
        F: FnOnce(cu::Expr) -> cu::Expr,
    {
        match self {
            Self::Expr(e) => Self::Expr(f(e)),
            Self::ExprIdxCheck(c, e) => Self::ExprIdxCheck(c, f(e)),
        }
    }

    fn expr(&self) -> &cu::Expr {
        match self {
            Self::Expr(e) => e,
            Self::ExprIdxCheck(c, e) => panic!("expected expr, found idxCheck"),
        }
    }
}

fn gen_fun_def(gl_fun: &desc::FunDef, codegen_ctx: &mut CodegenCtx) -> cu::FnDef {
    let desc::FunDef {
        ident: name,
        generic_params: ty_idents,
        param_decls: params,
        ret_dty: ret_ty,
        exec_decl,
        body_expr,
        ..
    } = gl_fun;

    let fn_sig = cu::FnSig::new(
        name.name.to_string(),
        gen_templ_params(ty_idents),
        gen_param_decls(params),
        gen_ty(
            &desc::TyKind::Data(Box::new(ret_ty.clone())),
            desc::Mutability::Mut,
        ),
        is_dev_fun(&exec_decl.ty),
    );

    cu::FnDef::new(
        fn_sig,
        gen_stmt(
            body_expr,
            !matches!(
                ret_ty,
                desc::DataTy {
                    dty: desc::DataTyKind::Scalar(desc::ScalarTy::Unit),
                    ..
                }
            ),
            codegen_ctx,
        ),
    )
}

// Generate CUDA code for Descend syntax that allows sequencing.
fn gen_stmt(expr: &desc::Expr, return_value: bool, codegen_ctx: &mut CodegenCtx) -> cu::Stmt {
    use desc::ExprKind::*;
    match &expr.expr {
        Let(pattern, _, e) => {
            // Let View
            gen_let(pattern, &e, codegen_ctx)
        }
        LetUninit(ident, ty) => {
            let (ty, addr_space) = match &ty.ty {
                desc::TyKind::Data(dty) => {
                    if let desc::DataTyKind::At(ddty, desc::Memory::GpuShared) = &dty.dty {
                        (
                            if let desc::DataTy {
                                dty: desc::DataTyKind::Array(d, n),
                                ..
                            } = ddty.as_ref()
                            {
                                cu::Ty::CArray(
                                    Box::new(gen_ty(
                                        &desc::TyKind::Data(Box::new(d.as_ref().clone())),
                                        desc::Mutability::Mut,
                                    )),
                                    n.clone(),
                                )
                            } else {
                                gen_ty(&ty.as_ref().ty, desc::Mutability::Mut)
                            },
                            Some(cu::GpuAddrSpace::Shared),
                        )
                    } else {
                        (gen_ty(&ty.as_ref().ty, desc::Mutability::Mut), None)
                    }
                }
                _ => (gen_ty(&ty.as_ref().ty, desc::Mutability::Mut), None),
            };
            cu::Stmt::VarDecl {
                name: ident.name.to_string(),
                ty,
                addr_space,
                expr: None,
            }
        }
        Block(_, expr) => {
            codegen_ctx.push_scope();
            let block_stmt = gen_stmt(expr, return_value, codegen_ctx);
            codegen_ctx.drop_scope();
            cu::Stmt::Block(Box::new(block_stmt))
        }
        // e1 ; e2
        Seq(s) => {
            let (last, leading) = s.split_last().unwrap();
            let mut stmts = leading
                .iter()
                .map(|stmt| gen_stmt(stmt, false, codegen_ctx))
                .collect::<Vec<_>>();
            stmts.append(&mut vec![gen_stmt(last, return_value, codegen_ctx)]);
            let mut stmts_seq = vec![];
            for stmt in stmts {
                stmts_seq.push(stmt);
            }
            cu::Stmt::Seq(stmts_seq)
        }
        ForNat(ident, range, body) => {
            let i = cu::Expr::Ident(ident.name.to_string());
            let (init, cond, iter) = match range {
                desc::Nat::App(r_name, input) => {
                    let (init_decl, cond, iter) = match r_name.name.as_ref() {
                        "range" => {
                            let init_decl = cu::Stmt::VarDecl {
                                name: ident.name.to_string(),
                                ty: cu::Ty::Scalar(cu::ScalarTy::SizeT),
                                addr_space: None,
                                expr: Some(cu::Expr::Nat(input[0].clone())),
                            };
                            let cond = cu::Expr::BinOp {
                                op: cu::BinOp::Lt,
                                lhs: Box::new(i.clone()),
                                rhs: Box::new(cu::Expr::Nat(input[1].clone())),
                            };
                            let iter = cu::Expr::Assign {
                                lhs: Box::new(i.clone()),
                                rhs: Box::new(cu::Expr::BinOp {
                                    op: cu::BinOp::Add,
                                    lhs: Box::new(i),
                                    rhs: Box::new(cu::Expr::Lit(cu::Lit::U32(1))),
                                }),
                            };
                            (init_decl, cond, iter)
                        }
                        "halved_range" => {
                            let init_decl = cu::Stmt::VarDecl {
                                name: ident.name.to_string(),
                                ty: cu::Ty::Scalar(cu::ScalarTy::SizeT),
                                addr_space: None,
                                expr: Some(cu::Expr::Nat(input[0].clone())),
                            };
                            let cond = cu::Expr::BinOp {
                                op: cu::BinOp::Gt,
                                lhs: Box::new(i.clone()),
                                rhs: Box::new(cu::Expr::Lit(cu::Lit::U32(0))),
                            };
                            let iter = cu::Expr::Assign {
                                lhs: Box::new(i.clone()),
                                rhs: Box::new(cu::Expr::BinOp {
                                    op: cu::BinOp::Div,
                                    lhs: Box::new(i),
                                    rhs: Box::new(cu::Expr::Lit(cu::Lit::U32(2))),
                                }),
                            };
                            (init_decl, cond, iter)
                        }
                        "doubled_range" => {
                            let init_decl = cu::Stmt::VarDecl {
                                name: ident.name.to_string(),
                                ty: cu::Ty::Scalar(cu::ScalarTy::SizeT),
                                addr_space: None,
                                expr: Some(cu::Expr::Nat(input[0].clone())),
                            };
                            let cond = cu::Expr::BinOp {
                                op: cu::BinOp::Le,
                                lhs: Box::new(i.clone()),
                                rhs: Box::new(cu::Expr::Nat(input[1].clone())),
                            };
                            let iter = cu::Expr::Assign {
                                lhs: Box::new(i.clone()),
                                rhs: Box::new(cu::Expr::BinOp {
                                    op: cu::BinOp::Mul,
                                    lhs: Box::new(i),
                                    rhs: Box::new(cu::Expr::Lit(cu::Lit::U32(2))),
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
                stmt: Box::new(gen_stmt(body, false, codegen_ctx)),
            }
        }
        While(cond, body) => cu::Stmt::While {
            cond: match gen_expr(cond, codegen_ctx) {
                CheckedExpr::Expr(expr) => expr,
                CheckedExpr::ExprIdxCheck(_, expr) => {
                    println!("found a condition in while-loop which needs checks!"); // TODO implement checks
                    expr
                }
            },
            stmt: Box::new(gen_stmt(body, false, codegen_ctx)),
        },
        For(ident, coll_expr, body) => {
            if matches_dty!(
                coll_expr.ty.as_ref().unwrap(),
                desc::DataTy {
                    dty: desc::DataTyKind::Range,
                    ..
                }
            ) {
                gen_for_range(ident, coll_expr, body, codegen_ctx)
            } else {
                gen_for_each(ident, coll_expr, body, codegen_ctx)
            }
        }
        Indep(pb) => gen_indep(pb.dim_compo, &pb.pos, &pb.branch_bodies, codegen_ctx),
        Sched(pf) => gen_sched(pf, codegen_ctx),
        // FIXME this assumes that IfElse is not an Expression.
        IfElse(cond, e_tt, e_ff) => match gen_expr(cond, codegen_ctx) {
            CheckedExpr::ExprIdxCheck(check, con) => {
                cu::Stmt::Seq(vec![check, gen_if_else(con, e_tt, e_ff, codegen_ctx)])
            }
            CheckedExpr::Expr(con) => gen_if_else(con, e_tt, e_ff, codegen_ctx),
        },
        If(cond, e_tt) => match gen_expr(cond, codegen_ctx) {
            CheckedExpr::ExprIdxCheck(check, con) => {
                cu::Stmt::Seq(vec![check, gen_if(con, e_tt, codegen_ctx)])
            }
            CheckedExpr::Expr(con) => gen_if(con, e_tt, codegen_ctx),
        },
        _ => {
            if return_value {
                match gen_expr(&expr, codegen_ctx) {
                    CheckedExpr::ExprIdxCheck(ch, e) if codegen_ctx.idx_checks => {
                        cu::Stmt::Seq(vec![ch, cu::Stmt::Return(Some(e))])
                    }
                    CheckedExpr::ExprIdxCheck(_, e) => cu::Stmt::Return(Some(e)),
                    CheckedExpr::Expr(e) => cu::Stmt::Return(Some(e)),
                }
            } else {
                match gen_expr(&expr, codegen_ctx) {
                    CheckedExpr::ExprIdxCheck(ch, e) if codegen_ctx.idx_checks => {
                        cu::Stmt::Seq(vec![ch, cu::Stmt::Expr(e)])
                    }
                    CheckedExpr::ExprIdxCheck(_, e) => cu::Stmt::Expr(e),
                    CheckedExpr::Expr(e) => cu::Stmt::Expr(e),
                }
            }
        }
    }
}

fn gen_let(pattern: &desc::Pattern, e: &desc::Expr, codegen_ctx: &mut CodegenCtx) -> cu::Stmt {
    match pattern {
        desc::Pattern::Tuple(tuple_elems) => cu::Stmt::Seq(
            tuple_elems
                .iter()
                .enumerate()
                .map(|(i, tp)| {
                    gen_let(
                        tp,
                        &desc::Expr::with_type(
                            desc::ExprKind::Proj(Box::new(e.clone()), i),
                            match ty_check::proj_elem_dty(&e.ty.as_ref().unwrap().dty(), i) {
                                Ok(dty) => desc::Ty::new(desc::TyKind::Data(Box::new(dty))),
                                Err(err) => {
                                    panic!("Cannot project tuple element type at {}", i)
                                }
                            },
                        ),
                        codegen_ctx,
                    )
                })
                .collect(),
        ),
        desc::Pattern::Ident(mutbl, ident) => gen_decl_init(ident, *mutbl, e, codegen_ctx),
        desc::Pattern::Wildcard => gen_decl_init(
            &desc::Ident::new(&desc::utils::fresh_name("$wild")),
            desc::Mutability::Const,
            e,
            codegen_ctx,
        ),
    }
}

fn gen_decl_init(
    ident: &desc::Ident,
    mutbl: desc::Mutability,
    e: &desc::Expr,
    codegen_ctx: &mut CodegenCtx,
) -> cu::Stmt {
    if is_view_dty(e.ty.as_ref().unwrap()) {
        codegen_ctx
            .shape_ctx
            .insert(&ident.name, ShapeExpr::create_from(e, &codegen_ctx));
        cu::Stmt::Skip
        // Let Expression
    } else if let desc::DataTy {
        dty: desc::DataTyKind::At(dty, desc::Memory::GpuShared),
        ..
    } = &e.ty.as_ref().unwrap().dty()
    {
        let cu_ty = if let desc::DataTy {
            dty: desc::DataTyKind::Array(elem_dty, n),
            ..
        } = dty.as_ref()
        {
            cu::Ty::CArray(
                Box::new(gen_ty(
                    &desc::TyKind::Data(Box::new(elem_dty.as_ref().clone())),
                    mutbl,
                )),
                n.clone(),
            )
        } else {
            gen_ty(&desc::TyKind::Data(Box::new(dty.as_ref().clone())), mutbl)
        };
        cu::Stmt::VarDecl {
            name: ident.name.to_string(),
            ty: cu_ty,
            addr_space: Some(cu::GpuAddrSpace::Shared),
            expr: None,
        }
    } else {
        let gened_ty = gen_ty(&e.ty.as_ref().unwrap().ty, mutbl);
        let (init_expr, cu_ty, checks) = match gened_ty {
            cu::Ty::Array(_, _) => {
                let (ex, ch) = match gen_expr(e, codegen_ctx) {
                    CheckedExpr::Expr(e) => (e, None),
                    CheckedExpr::ExprIdxCheck(c, e) => (e, Some(c)),
                };
                (ex, gened_ty, ch)
            }
            _ => {
                let (ex, ch) = match gen_expr(e, codegen_ctx) {
                    CheckedExpr::Expr(e) => (e, None),
                    CheckedExpr::ExprIdxCheck(c, e) => (e, Some(c)),
                };
                (
                    ex,
                    if mutbl == desc::Mutability::Mut {
                        cu::Ty::Scalar(cu::ScalarTy::Auto)
                    } else {
                        cu::Ty::Const(Box::new(cu::Ty::Scalar(cu::ScalarTy::Auto)))
                    },
                    ch,
                )
            }
        };
        let var_decl = cu::Stmt::VarDecl {
            name: ident.name.to_string(),
            ty: cu_ty,
            addr_space: None,
            expr: Some(init_expr),
        };
        if !codegen_ctx.idx_checks || checks.is_none() {
            var_decl
        } else {
            cu::Stmt::Seq(vec![checks.unwrap(), var_decl])
        }
    }
}

fn has_generatable_ty(e: &desc::Expr) -> bool {
    matches!(&e.ty.as_ref().unwrap().ty, desc::TyKind::Data(_))
}

fn gen_if_else(
    cond: cu_ast::Expr,
    e_tt: &desc::Expr,
    e_ff: &desc::Expr,
    codegen_ctx: &mut CodegenCtx,
) -> cu::Stmt {
    cu::Stmt::IfElse {
        cond: cond,
        true_body: Box::new(gen_stmt(e_tt, false, codegen_ctx)),
        false_body: Box::new(gen_stmt(e_ff, false, codegen_ctx)),
    }
}

fn gen_if(cond: cu_ast::Expr, e_tt: &desc::Expr, codegen_ctx: &mut CodegenCtx) -> cu::Stmt {
    cu::Stmt::If {
        cond: cond,
        body: Box::new(gen_stmt(e_tt, false, codegen_ctx)),
    }
}

fn gen_for_each(
    ident: &desc::Ident,
    coll_expr: &desc::Expr,
    body: &desc::Expr,
    codegen_ctx: &mut CodegenCtx,
) -> cu::Stmt {
    let i_name = crate::ast::utils::fresh_name("i__");
    let i_decl = cu::Stmt::VarDecl {
        name: i_name.clone(),
        ty: cu::Ty::Scalar(cu::ScalarTy::SizeT),
        addr_space: None,
        expr: Some(cu::Expr::Lit(cu::Lit::I32(0))),
    };
    let i = cu::Expr::Ident(i_name.to_string());
    codegen_ctx.push_scope();
    codegen_ctx.shape_ctx.insert(
        &ident.name,
        ShapeExpr::Idx {
            idx: desc::Nat::Ident(desc::Ident::new(&i_name)),
            shape: Box::new(if is_view_dty(coll_expr.ty.as_ref().unwrap()) {
                ShapeExpr::create_from(coll_expr, &codegen_ctx)
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
        stmt: Box::new(gen_stmt(body, false, codegen_ctx)),
    };

    codegen_ctx.shape_ctx.drop_scope();
    for_loop
}

fn gen_for_range(
    ident: &desc::Ident,
    range: &desc::Expr,
    body: &desc::Expr,
    codegen_ctx: &mut CodegenCtx,
) -> cu::Stmt {
    if let desc::ExprKind::Range(l, u) = &range.expr {
        let lower = gen_expr(l, codegen_ctx);
        let upper = gen_expr(u, codegen_ctx);

        let i_name = ident.name.clone();
        let i_decl = cu::Stmt::VarDecl {
            name: i_name.to_string(),
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
            stmt: Box::new(gen_stmt(body, false, codegen_ctx)),
        }
    } else {
        panic!("Expected range expression")
    }
}

fn gen_exec(
    grid_dims: usize,
    blocks: Vec<desc::ArgKinded>,
    threads: Vec<desc::ArgKinded>,
    gpu_expr: &desc::Expr,
    input_expr: &desc::Expr,
    fun: &desc::Expr,
    codegen_ctx: &mut CodegenCtx,
) -> CheckedExpr {
    // Prepare parameter declarations for inputs
    let mut cu_input_expr = ShapeExpr::create_from(input_expr, &codegen_ctx);
    let name_to_exprs = cu_input_expr.collect_and_rename_input_exprs();
    let mut param_decls: Vec<_> = name_to_exprs
        .iter()
        .map(|(name, expr)| cu::ParamDecl {
            name: name.clone(),
            // TODO why Mutability::Const??!
            ty: gen_ty(&expr.ty.as_ref().unwrap().ty, desc::Mutability::Const),
        })
        .collect();

    if codegen_ctx.idx_checks {
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
    let gpu = match gen_expr(gpu_expr, codegen_ctx) {
        CheckedExpr::Expr(e) => e,
        CheckedExpr::ExprIdxCheck(_, _) => {
            panic!("Did not expect to check a condition for GPU")
        }
    };

    // FIXME only allows Lambdas
    let (dev_fun, free_kinded_idents): (cu::Expr, Vec<desc::IdentKinded>) =
        if let desc::ExprKind::Lambda(params, ident_exec, _, body) = &fun.expr {
            codegen_ctx.push_scope();
            let (gdim, bdim) = if let desc::ExecTyKind::GpuGrid(gdim, bdim) = &ident_exec.ty.ty {
                (gdim.clone(), bdim.clone())
            } else {
                panic!(
                    "Expected GpuGrid execution resource type, but found {}",
                    &ident_exec.ty.ty
                )
            };
            codegen_ctx.exec =
                desc::ExecExpr::new(desc::Exec::new(desc::BaseExec::GpuGrid(gdim, bdim)));

            // Remember to inline input shape expression
            let in_name = &params[0].ident.name.clone();
            codegen_ctx.shape_ctx.insert(in_name, cu_input_expr);

            let gpu_fun_body = gen_stmt(body, false, codegen_ctx);
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

            // FIXME reintroduce, but differentiate between statically computed and runtime computed
            //  values, especially for array sizes
            // let free_kinded_idents = {
            //     let mut free_kinded_idents = desc::utils::FreeKindedIdents::new();
            //     free_kinded_idents.visit_expr(&body.clone());
            //     free_kinded_idents
            //         .set
            //         .iter()
            //         .filter(|ki| ki.kind != desc::Kind::Provenance)
            //         .cloned()
            //         .collect::<Vec<_>>()
            // };
            // let nat_param_decls = free_kinded_idents
            //     .iter()
            //     .map(|ki| match &ki.kind {
            //         desc::Kind::Nat => cu::ParamDecl {
            //             name: ki.ident.name.to_string(),
            //             ty: cu::Ty::Scalar(cu::ScalarTy::SizeT),
            //         },
            //         desc::Kind::Provenance | desc::Kind::Memory | desc::Kind::DataTy => {
            //             panic!("Unexpected found {:?}.", ki.ident.name)
            //         }
            //     })
            //     .collect::<Vec<_>>();
            let mut all_param_decls = param_decls;
            // FIXME see above
            // all_param_decls.extend(nat_param_decls);

            codegen_ctx.drop_scope();
            (
                cu::Expr::Lambda {
                    captures: vec![],
                    params: all_param_decls,
                    body: Box::new(if codegen_ctx.idx_checks {
                        global_failure_init.push(gpu_fun_body);
                        cu::Stmt::Seq(global_failure_init)
                    } else {
                        gpu_fun_body
                    }),
                    ret_ty: cu::Ty::Scalar(cu::ScalarTy::Void),
                    is_dev_fun: true,
                },
                vec![]
                // FIXME see above
                // free_kinded_idents,
            )
        } else {
            panic!("Currently only lambdas can be passed.")
        };
    let mut checks: Vec<cu::Stmt> = vec![];
    let mut input: Vec<_> = name_to_exprs
        .iter()
        .map(|(_, pl_expr)| match gen_expr(pl_expr, codegen_ctx) {
            CheckedExpr::ExprIdxCheck(check, expr) if codegen_ctx.idx_checks => {
                checks.push(check);
                expr
            }
            CheckedExpr::ExprIdxCheck(_, expr) => expr,
            CheckedExpr::Expr(expr) => expr,
        })
        .collect();
    let template_args = if grid_dims == 1 {
        gen_args_kinded(vec![blocks[0].clone(), threads[0].clone()].as_slice())
    } else if grid_dims == 2 {
        gen_args_kinded(
            vec![
                blocks[0].clone(),
                blocks[1].clone(),
                threads[0].clone(),
                threads[1].clone(),
            ]
            .as_slice(),
        )
    } else {
        unimplemented!()
    };

    let mut args: Vec<cu::Expr> = vec![gpu, dev_fun];
    args.append(&mut input);
    let mut nat_input_idents = free_kinded_idents
        .iter()
        .filter_map(|ki| {
            if let desc::Kind::Nat = ki.kind {
                Some(cu::Expr::Nat(desc::Nat::Ident(ki.ident.clone())))
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    args.append(&mut nat_input_idents);

    let exec_name = if grid_dims == 1 {
        "descend::exec".to_string()
    } else if grid_dims == 2 {
        "descend::exec_xy".to_string()
    } else {
        unimplemented!()
    };

    codegen_ctx.exec = desc::ExecExpr::new(desc::Exec::new(desc::BaseExec::CpuThread));

    if checks.is_empty() {
        CheckedExpr::Expr(cu::Expr::FunCall {
            fun: Box::new(cu::Expr::Ident(exec_name.to_string())),
            template_args,
            args,
        })
    } else {
        CheckedExpr::ExprIdxCheck(
            cu::Stmt::Seq(checks),
            cu::Expr::FunCall {
                fun: Box::new(cu::Expr::Ident(exec_name.to_string())),
                template_args,
                args,
            },
        )
    }
}

fn gen_indep(
    dim_compo: desc::DimCompo,
    pos: &desc::Nat,
    branch_bodies: &[desc::Expr],
    codegen_ctx: &mut CodegenCtx,
) -> cu::Stmt {
    let outer_exec = codegen_ctx.exec.clone();
    codegen_ctx.push_scope();
    codegen_ctx.exec = desc::ExecExpr::new(codegen_ctx.exec.exec.clone().split_proj(
        dim_compo,
        pos.clone(),
        0,
    ));
    let fst_branch = gen_stmt(&branch_bodies[0], false, codegen_ctx);
    codegen_ctx.drop_scope();
    codegen_ctx.push_scope();
    codegen_ctx.exec = desc::ExecExpr::new(codegen_ctx.exec.exec.clone().split_proj(
        dim_compo,
        pos.clone(),
        1,
    ));
    let snd_branch = gen_stmt(&branch_bodies[1], false, codegen_ctx);
    codegen_ctx.drop_scope();
    codegen_ctx.exec = outer_exec;

    let split_cond = gen_indep_branch_cond(dim_compo, pos, &codegen_ctx.exec.exec);
    cu::Stmt::Seq(vec![
        cu::Stmt::IfElse {
            cond: split_cond,
            true_body: Box::new(fst_branch),
            false_body: Box::new(snd_branch),
        },
        //  gen_sync_stmt(&split_par_collec),
    ])
}

fn gen_sync_stmt(exec: &desc::ExecExpr) -> cu::Stmt {
    let sync = cu::Stmt::Expr(cu::Expr::FunCall {
        fun: Box::new(cu::Expr::Ident("__syncthreads".to_string())),
        template_args: vec![],
        args: vec![],
    });
    unimplemented!()
    // match exec {
    //     ParallelityCollec::Split { parall_collec, .. } => gen_sync_stmt(parall_collec),
    //     ParallelityCollec::Grid(_, _) | ParallelityCollec::ToThreadGrp(_) => cu::Stmt::Skip,
    //     ParallelityCollec::Block(_) => sync,
    //     ParallelityCollec::Proj { parall_expr, .. } => {
    //         if let ParallelityCollec::Split { parall_collec, .. } = parall_expr.as_ref() {
    //             match parall_collec.as_ref() {
    //                 ParallelityCollec::Block(_) => sync,
    //                 _ => cu::Stmt::Skip,
    //             }
    //         } else {
    //             panic!("this should never happen")
    //         }
    //     }
    //     _ => unimplemented!(),
    // }
}

fn gen_parall_section(sched: &desc::Sched, codegen_ctx: &mut CodegenCtx) -> cu::Stmt {
    codegen_ctx.push_scope();
    let inner_exec = desc::ExecExpr::new(codegen_ctx.exec.exec.clone().distrib(sched.dim));
    let outer_exec = codegen_ctx.exec.clone();
    if let Some(id) = &sched.inner_exec_ident {
        codegen_ctx
            .exec_mapping
            .insert(&id.name, inner_exec.clone());
    }
    codegen_ctx.exec = inner_exec;

    // for (ident, input_expr) in sched
    //     .input_idents
    //     .iter()
    //     .map(|ident| ident.name.clone())
    //     .zip(&sched.input_views)
    // {
    //     let input_arg_shape = ShapeExpr::create_from(input_expr, &codegen_ctx.shape_ctx);
    //     let par_distrib = input_arg_shape.par_distrib_shape(sched.dim, &codegen_ctx.exec);
    //     codegen_ctx.shape_ctx.insert(&ident, par_distrib);
    // }
    let stmt = gen_stmt(&sched.body, false, codegen_ctx);

    codegen_ctx.exec = outer_exec;
    codegen_ctx.drop_scope();
    stmt
}

fn gen_sched(sched: &desc::Sched, codegen_ctx: &mut CodegenCtx) -> cu::Stmt {
    let par_section = gen_parall_section(sched, codegen_ctx);
    cu::Stmt::Seq(vec![par_section])
}

fn gen_check_idx_stmt(expr: &desc::Expr, codegen_ctx: &mut CodegenCtx) -> cu::Stmt {
    use desc::ExprKind::*;
    if let Index(pl_expr, i) = &expr.expr {
        if codegen_ctx.idx_checks && is_dev_fun(&codegen_ctx.exec.ty.as_ref().unwrap()) {
            let n = match &pl_expr
                .ty
                .as_ref()
                .unwrap_or_else(|| panic!("{:?}", pl_expr))
                .dty()
                .dty
            {
                DataTyKind::Array(_, m) => m,
                DataTyKind::Ref(reff) => match &reff.dty.as_ref().dty {
                    DataTyKind::Array(_, m) => m,
                    DataTyKind::ArrayShape(_, m) => m,
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
                        template_args: gen_args_kinded(&vec![ArgKinded::DataTy(DataTy::new(
                            DataTyKind::Scalar(ScalarTy::I32),
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

fn gen_expr(expr: &desc::Expr, codegen_ctx: &mut CodegenCtx) -> CheckedExpr {
    use desc::ExprKind::*;

    match &expr.expr {
        Lit(l) => CheckedExpr::Expr(gen_lit(*l)),
        PlaceExpr(pl_expr) => CheckedExpr::Expr(gen_pl_expr(pl_expr, codegen_ctx)),
        Proj(tuple, idx) => {
            if is_view_dty(expr.ty.as_ref().unwrap()) {
                CheckedExpr::Expr(gen_shape(
                    &ShapeExpr::create_from(expr, &codegen_ctx),
                    vec![],
                    codegen_ctx,
                ))
            } else {
                gen_expr(tuple, codegen_ctx).map(|e| cu::Expr::Proj {
                    tuple: Box::new(e),
                    n: *idx,
                })
            }
        }
        BinOp(op, lhs, rhs) => gen_bin_op_expr(op, lhs, rhs, codegen_ctx),
        UnOp(op, arg) => gen_expr(arg, codegen_ctx).map(|e| cu::Expr::UnOp {
            op: match op {
                desc::UnOp::Not => cu::UnOp::Not,
                desc::UnOp::Neg => cu::UnOp::Neg,
            },
            arg: Box::new(e),
        }),
        Ref(_, _, pl_expr) => {
            //match &expr.ty.as_ref().unwrap().ty {
            // desc::TyKind::Data(desc::DataTy {
            //     dty: desc::DataTyKind::Ref(_, _, desc::Memory::GpuShared, _),
            //     ..
            // }) => CheckedExpr::Expr(gen_pl_expr(
            //     pl_expr,
            //     &codegen_ctx.shape_ctx,
            //     comp_unit,
            //     idx_checks,
            // )),
            // _ =>
            let ref_pl_expr = gen_pl_expr(pl_expr, codegen_ctx);
            CheckedExpr::Expr(match &pl_expr.ty.as_ref().unwrap().dty() {
                desc::DataTy {
                    dty: desc::DataTyKind::At(_, desc::Memory::GpuShared),
                    ..
                } => ref_pl_expr,
                _ => cu::Expr::Ref(Box::new(ref_pl_expr)),
            })
        }
        BorrowIndex(_, _, pl_expr, n) => {
            if contains_shape_expr(pl_expr, &codegen_ctx.shape_ctx) {
                // TODO sure?!
                panic!("It should not be allowed to borrow from a shape expression.")
            } else {
                CheckedExpr::Expr(cu::Expr::Ref(Box::new(cu::Expr::ArraySubscript {
                    array: Box::new(gen_pl_expr(pl_expr, codegen_ctx)),
                    index: n.clone(),
                })))
            }
        }
        Index(pl_expr, idx) => {
            // if contains_shape_expr(pl_expr, &codegen_ctx.shape_ctx) {
            //     CheckedExpr::ExprIdxCheck(
            //         gen_check_idx_stmt(expr, codegen_ctx),
            //         gen_idx_into_shape(pl_expr, idx, codegen_ctx),
            //     )
            // } else {
            //     CheckedExpr::ExprIdxCheck(
            //         gen_check_idx_stmt(expr, codegen_ctx),
            //         cu::Expr::ArraySubscript {
            //             array: Box::new(gen_pl_expr(pl_expr, codegen_ctx)),
            //             index: idx.clone(),
            //         },
            //     )
            // }
            CheckedExpr::Expr(if contains_shape_expr(pl_expr, &codegen_ctx.shape_ctx) {
                gen_idx_into_shape(pl_expr, idx, codegen_ctx)
            } else {
                cu::Expr::ArraySubscript {
                    array: Box::new(gen_pl_expr(pl_expr, codegen_ctx)),
                    index: idx.clone(),
                }
            })
        }
        IdxAssign(pl_expr, idx, expr) => {
            let cu_expr = gen_expr(expr, codegen_ctx);
            let cu_idx = if contains_shape_expr(pl_expr, &codegen_ctx.shape_ctx) {
                gen_idx_into_shape(pl_expr, idx, codegen_ctx)
            } else {
                cu::Expr::ArraySubscript {
                    array: Box::new(gen_pl_expr(pl_expr, codegen_ctx)),
                    index: idx.clone(),
                }
            };
            cu_expr.map(|e| cu::Expr::Assign {
                lhs: Box::new(cu_idx),
                rhs: Box::new(e),
            })
        }
        Assign(pl_expr, expr) => {
            let e = gen_expr(expr, codegen_ctx);
            CheckedExpr::Expr(cu::Expr::Assign {
                lhs: Box::new(gen_pl_expr(pl_expr, codegen_ctx)),
                rhs: Box::new(e.expr().clone()),
            })
        }
        Select(_, _, _) => CheckedExpr::Expr(cu::Expr::Ref(Box::new(gen_shape(
            &ShapeExpr::create_from(expr, codegen_ctx),
            vec![],
            codegen_ctx,
        )))),
        Lambda(params, exec_decl, dty, body) => CheckedExpr::Expr(cu::Expr::Lambda {
            captures: {
                let mut free_idents = desc::utils::FreeKindedIdents::new();
                free_idents.visit_expr(body);
                free_idents.set.iter().map(|ki| ki.ident.clone()).collect()
            },
            params: gen_param_decls(params.as_slice()),
            body: Box::new(gen_stmt(
                body,
                !matches!(
                    dty.as_ref(),
                    desc::DataTy {
                        dty: desc::DataTyKind::Scalar(desc::ScalarTy::Unit),
                        ..
                    }
                ),
                codegen_ctx,
            )),
            ret_ty: gen_ty(&desc::TyKind::Data(dty.clone()), desc::Mutability::Mut),
            is_dev_fun: is_dev_fun(&exec_decl.ty),
        }),
        App(fun, kinded_args, args) => match &fun.expr {
            PlaceExpr(pl_expr) => match &pl_expr.pl_expr {
                desc::PlaceExprKind::Ident(name)
                    if name.name.as_ref() == ty_check::pre_decl::EXEC =>
                {
                    gen_exec(
                        1,
                        vec![kinded_args[0].clone()],
                        vec![kinded_args[1].clone()],
                        &args[0],
                        &args[1],
                        &args[2],
                        codegen_ctx,
                    )
                }
                desc::PlaceExprKind::Ident(name)
                    if name.name.as_ref() == ty_check::pre_decl::EXEC_XY =>
                {
                    gen_exec(
                        2,
                        vec![kinded_args[0].clone(), kinded_args[1].clone()],
                        vec![kinded_args[2].clone(), kinded_args[3].clone()],
                        &args[0],
                        &args[1],
                        &args[2],
                        codegen_ctx,
                    )
                }
                desc::PlaceExprKind::Ident(ident)
                    if ty_check::pre_decl::fun_decls()
                        .iter()
                        .any(|(name, _)| &ident.name.as_ref() == name) =>
                {
                    let pre_decl_ident = desc::Ident::new(&format!("descend::{}", ident.name));
                    CheckedExpr::Expr(create_fn_call(
                        cu::Expr::Ident(pre_decl_ident.name.to_string()),
                        gen_args_kinded(kinded_args),
                        gen_fn_call_args(args, codegen_ctx),
                    ))
                }
                desc::PlaceExprKind::Ident(ident)
                    if codegen_ctx.comp_unit.iter().any(|f| &f.ident == ident) =>
                {
                    CheckedExpr::Expr(gen_global_fn_call(
                        codegen_ctx
                            .comp_unit
                            .iter()
                            .find(|f| &f.ident == ident)
                            .unwrap(),
                        kinded_args,
                        args,
                        codegen_ctx,
                    ))
                }
                _ => panic!("Unexpected functions cannot be stored in memory."),
            },
            _ => CheckedExpr::Expr(gen_lambda_call(fun, args, codegen_ctx)),
        },
        DepApp(fun, kinded_args) => {
            // let ident = extract_fn_ident(fun);
            // let fun_def = codegen_ctx
            //     .comp_unit
            //     .iter()
            //     .find(|fun_def| fun_def.ident == ident)
            //     .expect("Cannot find function definition.");
            // let inst_fun = partial_app_gen_args(fun_def, kinded_args);
            // gen_expr(&inst_fun, codegen_ctx)
            todo!()
        }
        Array(elems) => CheckedExpr::Expr(cu::Expr::InitializerList {
            elems: elems
                .iter()
                .map(|e| match gen_expr(e, codegen_ctx) {
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
        //         .map(|e| gen_expr(e, parall_ctx, shape_ctx))
        //         .collect::<Vec<_>>(),
        // },
        Tuple(elems) => CheckedExpr::Expr(cu::Expr::Tuple(
            elems
                .iter()
                .map(|el| match gen_expr(el, codegen_ctx) {
                    CheckedExpr::Expr(expr) => expr,
                    CheckedExpr::ExprIdxCheck(_, _) => {
                        panic!("Elements of a tuple should not have to be checked!")
                    }
                })
                .collect::<Vec<_>>(),
        )),
        Deref(e) => CheckedExpr::Expr(cu::Expr::Deref(Box::new(match gen_expr(e, codegen_ctx) {
            CheckedExpr::Expr(expr) => expr,
            CheckedExpr::ExprIdxCheck(_, _) => {
                panic!("did not expect a check after deref!")
            }
        }))),
        Idx(e, i) => CheckedExpr::Expr(cu::Expr::ArraySubscript {
            array: Box::new(match gen_expr(e, codegen_ctx) {
                CheckedExpr::Expr(expr) => expr,
                CheckedExpr::ExprIdxCheck(_, _) => panic!("should never happen"),
            }),
            index: i.clone(),
        }),
        Sync => CheckedExpr::Expr(cu::Expr::FunCall {
            fun: Box::new(cu::Expr::Ident("__syncthreads".to_string())),
            template_args: vec![],
            args: vec![],
        }),
        Let(_, _, _)
        | LetUninit(_, _)
        | Block(_, _)
        | IfElse(_, _, _)
        | If(_, _)
        | Seq(_)
        | While(_, _)
        | For(_, _, _)
        | ForNat(_, _, _)
        | Indep(_)
        | Sched(_) => panic!(
            "Trying to generate a statement where an expression is expected:\n{:?}",
            &expr
        ),
        Split(_) => {
            panic!("The split operator should have been descontructed by now.")
        }
        Range(_, _) => {
            panic!("Range should be deconstructed at a different place.")
        }
    }
}

fn gen_lambda_call(
    fun: &desc::Expr,
    args: &[desc::Expr],
    codegen_ctx: &mut CodegenCtx,
) -> cu::Expr {
    unimplemented!(
        "The only case in which this has to be generated is, when a lambda is called right\
    where it is created. There is no way to bind a lambda with let.\
    And no way for users to write a function that has function paramteres."
    )
}

fn gen_global_fn_call(
    fun: &desc::FunDef,
    gen_args: &[desc::ArgKinded],
    args: &[desc::Expr],
    codegen_ctx: &mut CodegenCtx,
) -> cu::Expr {
    // Make sure that we do not accidentally add views conflicting to fun,
    // because during type checking the order is: check fun first then do the arguments.
    codegen_ctx.push_scope();
    let cu_gen_args = gen_args_kinded(gen_args);
    let cu_args = gen_fn_call_args(args, codegen_ctx);
    codegen_ctx.drop_scope();

    let views = view_exprs_in_args(args, codegen_ctx);
    if let Some(mangled) = mangle_name(&fun.ident.name, &codegen_ctx.exec, &views) {
        if !codegen_ctx.inst_fn_ctx.contains_key(&mangled) {
            codegen_ctx.push_scope();
            bind_view_args_to_params(&fun.param_decls, args, codegen_ctx);
            codegen_ctx
                .exec_mapping
                .insert(&fun.exec_decl.ident.name, codegen_ctx.exec.clone());
            let mut new_fun_def = gen_fun_def(fun, codegen_ctx);
            new_fun_def.fn_sig.name = mangled.clone();
            codegen_ctx.drop_scope();
            codegen_ctx.inst_fn_ctx.insert(mangled.clone(), new_fun_def);
        }
        create_named_fn_call(mangled, cu_gen_args, cu_args)
    } else {
        create_named_fn_call(fun.ident.name.to_string(), cu_gen_args, cu_args)
    }
}

fn gen_fn_call_args(args: &[desc::Expr], codegen_ctx: &mut CodegenCtx) -> Vec<cu::Expr> {
    args.iter()
        .map(|arg| {
            if is_view_dty(arg.ty.as_ref().unwrap()) {
                gen_expr(
                    &basis_ref(&ShapeExpr::create_from(arg, &codegen_ctx)),
                    codegen_ctx,
                )
                .expr()
                .clone()
            } else {
                gen_expr(arg, codegen_ctx).expr().clone()
            }
        })
        .collect()
}

fn basis_ref(view: &ShapeExpr) -> desc::Expr {
    match view {
        ShapeExpr::ToView { ref_expr } => ref_expr.as_ref().clone(),
        ShapeExpr::SplitAt { shape, .. } => basis_ref(shape),
        ShapeExpr::Group { shape, .. } => basis_ref(shape),
        ShapeExpr::Join { shape, .. } => basis_ref(shape),
        ShapeExpr::Transpose { shape, .. } => basis_ref(shape),
        ShapeExpr::Tuple { shapes: elems } => {
            // maybe untrue
            todo!("this case should be removed")
        }
        ShapeExpr::Idx { shape, .. } => basis_ref(shape),
        ShapeExpr::Proj { shape, .. } => basis_ref(shape),
    }
}

fn view_exprs_in_args(args: &[desc::Expr], codegen_ctx: &CodegenCtx) -> Vec<ShapeExpr> {
    let (views, _): (Vec<_>, Vec<_>) = args
        .iter()
        .partition(|a| is_view_dty(a.ty.as_ref().unwrap()));
    views
        .iter()
        .map(|v| ShapeExpr::create_from(v, &codegen_ctx))
        .collect()
}

fn bind_view_args_to_params(
    param_decls: &[desc::ParamDecl],
    args: &[desc::Expr],
    codegen_ctx: &mut CodegenCtx,
) {
    let view_params_with_args = separate_view_params_with_args_from_rest(&param_decls, args);
    for (p, arg) in view_params_with_args {
        codegen_ctx
            .shape_ctx
            .insert(&p.ident.name, ShapeExpr::create_from(arg, &codegen_ctx));
    }
}

fn separate_view_params_with_args_from_rest<'a>(
    param_decls: &'a [desc::ParamDecl],
    args: &'a [desc::Expr],
) -> Vec<(&'a desc::ParamDecl, &'a desc::Expr)> {
    let (view_params_with_args, _): (Vec<_>, Vec<_>) = param_decls
        .iter()
        .zip(args.iter())
        .partition(|&(p, _)| is_view_dty(p.ty.as_ref().unwrap()));

    view_params_with_args
}

fn mangle_name(name: &str, exec: &desc::ExecExpr, views: &[ShapeExpr]) -> Option<String> {
    let mut mangled = name.to_string();
    mangled.push_str(&stringify_exec(exec));
    mangled.push_str(&stringify_views(views));

    if mangled != name {
        Some(mangled)
    } else {
        None
    }
}

fn stringify_exec(exec: &desc::ExecExpr) -> String {
    let mut str = String::with_capacity(10);
    for e in &exec.exec.path {
        match e {
            desc::ExecPathElem::Distrib(dim) => {
                str.push('D');
                str.push_str(&format!("{}", dim));
                str.push('_');
            }
            desc::ExecPathElem::SplitProj(split_proj) => {
                let s = format!(
                    "P{}S{}{}_",
                    split_proj.proj, split_proj.split_dim, &split_proj.pos,
                );
                str.push_str(&s);
            }
        }
    }
    str
}

fn stringify_views(views: &[ShapeExpr]) -> String {
    let mut str = String::with_capacity(16);
    let mut counter = 0;
    for v in views {
        str.push_str(&stringify_view(v, counter));
        counter += 1;
    }
    str
}

fn stringify_view(view: &ShapeExpr, c: u8) -> String {
    let mut str = String::with_capacity(32);
    match view {
        ShapeExpr::ToView { .. } => {
            str.push_str(&c.to_string());
        }
        ShapeExpr::Proj { shape, i } => {
            if let ShapeExpr::SplitAt { shape, .. } = shape.as_ref() {
                let s = format!("P{}S_{}", *i, &stringify_view(shape.as_ref(), c));
                str.push_str(&s);
            } else {
                unreachable!("A projection must always contain a split.")
            }
        }
        ShapeExpr::Idx { shape, .. } => {
            let s = format!("I{}_", &stringify_view(shape.as_ref(), c));
            str.push_str(&s);
        }
        ShapeExpr::Group { shape, .. } => {
            let s = format!("G{}", &stringify_view(shape.as_ref(), c));
            str.push_str(&s);
        }
        ShapeExpr::Join { shape, .. } => {
            str.push_str("J_");
            str.push_str(&stringify_view(shape.as_ref(), c));
        }
        ShapeExpr::Transpose { shape } => {
            str.push_str("T_");
            str.push_str(&stringify_view(shape.as_ref(), c))
        }
        ShapeExpr::SplitAt { .. } | ShapeExpr::Tuple { .. } => {
            unimplemented!("Maybe proj can contain tuples as well")
        }
    }
    str
}

fn create_named_fn_call(
    name: String,
    gen_args: Vec<cu::TemplateArg>,
    args: Vec<cu::Expr>,
) -> cu::Expr {
    create_fn_call(cu::Expr::Ident(name), gen_args, args)
}

fn create_fn_call(
    fun: cu::Expr,
    gen_args: Vec<cu::TemplateArg>,
    params: Vec<cu::Expr>,
) -> cu::Expr {
    cu::Expr::FunCall {
        fun: Box::new(fun),
        template_args: gen_args,
        args: params,
    }
}

fn gen_bin_op_expr(
    op: &desc::BinOp,
    lhs: &desc::Expr,
    rhs: &desc::Expr,
    codegen_ctx: &mut CodegenCtx,
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
        match (gen_expr(lhs, codegen_ctx), gen_expr(rhs, codegen_ctx)) {
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

fn extract_fn_ident(ident: &desc::Expr) -> desc::Ident {
    if let desc::ExprKind::PlaceExpr(pl_expr) = &ident.expr {
        if let desc::PlaceExprKind::Ident(ident) = &pl_expr.pl_expr {
            ident.clone()
        } else {
            panic!("Function cannot be a place expression besides identifier.")
        }
    } else {
        panic!("Generic function must be global and therefore be identifier place expression.")
    }
}

fn contains_shape_expr(pl_expr: &desc::PlaceExpr, shape_ctx: &ShapeCtx) -> bool {
    let (_, pl) = pl_expr.to_pl_ctx_and_most_specif_pl();
    shape_ctx.contains_key(&pl.ident.name)
}

fn gen_idx_into_shape(
    pl_expr: &desc::PlaceExpr,
    idx: &desc::Nat,
    codegen_ctx: &mut CodegenCtx,
) -> cu::Expr {
    let collec_shape = ShapeExpr::create_from(
        &desc::Expr::new(desc::ExprKind::PlaceExpr(Box::new(pl_expr.clone()))),
        &codegen_ctx,
    );
    gen_shape(
        &ShapeExpr::Idx {
            idx: idx.clone(),
            shape: Box::new(collec_shape),
        },
        vec![],
        codegen_ctx,
    )
}

fn gen_lit(l: desc::Lit) -> cu::Expr {
    match l {
        desc::Lit::Bool(b) => cu::Expr::Lit(cu::Lit::Bool(b)),
        desc::Lit::I32(i) => cu::Expr::Lit(cu::Lit::I32(i)),
        desc::Lit::U32(u) => cu::Expr::Lit(cu::Lit::U32(u)),
        desc::Lit::F32(f) => cu::Expr::Lit(cu::Lit::F32(f)),
        desc::Lit::F64(d) => cu::Expr::Lit(cu::Lit::F64(d)),
        desc::Lit::Unit => cu::Expr::Empty,
    }
}

fn gen_pl_expr(pl_expr: &desc::PlaceExpr, codegen_ctx: &mut CodegenCtx) -> cu::Expr {
    match &pl_expr {
        desc::PlaceExpr {
            pl_expr: desc::PlaceExprKind::Ident(ident),
            ..
        } => {
            if codegen_ctx.shape_ctx.contains_key(&ident.name) {
                gen_shape(
                    &codegen_ctx.shape_ctx.get(&ident.name).clone(),
                    vec![],
                    codegen_ctx,
                )
            } else {
                let is_pre_decl_fun = ty_check::pre_decl::fun_decls()
                    .iter()
                    .any(|(name, _)| &ident.name.as_ref() == name);
                let name = if is_pre_decl_fun {
                    format!("descend::{}", ident.name)
                } else {
                    ident.name.to_string()
                };
                cu::Expr::Ident(name)
            }
        }
        desc::PlaceExpr {
            pl_expr: desc::PlaceExprKind::Proj(pl, n),
            ..
        } => match pl_expr.to_place() {
            // FIXME this does not work when there are tuples inside of shape tuples
            Some(p) if codegen_ctx.shape_ctx.contains_key(&p.ident.name) => gen_shape(
                &codegen_ctx.shape_ctx.get(&p.ident.name).clone(),
                p.path.iter().map(|n| desc::Nat::Lit(*n)).collect(),
                codegen_ctx,
            ),
            _ => cu::Expr::Proj {
                tuple: Box::new(gen_pl_expr(pl.as_ref(), codegen_ctx)),
                n: *n,
            },
        },
        desc::PlaceExpr {
            pl_expr: desc::PlaceExprKind::Deref(ple),
            ..
        } => {
            // If an identifier that refers to an unwrapped shape expression is being dereferenced,
            // just generate from the shape expression and omit generating the dereferencing.
            // The dereferencing will happen through indexing.
            match ple.to_place() {
                Some(pl) if codegen_ctx.shape_ctx.contains_key(&pl.ident.name) => gen_shape(
                    &codegen_ctx.shape_ctx.get(&pl.ident.name).clone(),
                    pl.path.iter().map(|n| desc::Nat::Lit(*n)).collect(),
                    codegen_ctx,
                ),
                _ => cu::Expr::Deref(Box::new(gen_pl_expr(ple.as_ref(), codegen_ctx))),
            }
        }
    }
}

enum ParallRange {
    Range(desc::Nat, desc::Nat),
    SplitRange(desc::Nat, desc::Nat, desc::Nat),
}

fn gen_indep_branch_cond(
    dim_compo: desc::DimCompo,
    pos: &desc::Nat,
    exec: &desc::Exec,
) -> cu::Expr {
    cu::Expr::BinOp {
        op: cu::BinOp::Lt,
        lhs: Box::new(cu::Expr::Nat(parall_idx(
            dim_compo,
            // The condition must range over the elements within the execution resource.
            // Use Distrib to indicate this.
            &desc::ExecExpr::new(exec.clone().distrib(dim_compo)),
        ))),
        rhs: Box::new(cu::Expr::Nat(pos.clone())),
    }
}

fn gen_shape(
    shape_expr: &ShapeExpr,
    mut path: Vec<desc::Nat>,
    codegen_ctx: &mut CodegenCtx,
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
            index: index.simplify(),
        }
    }

    match (shape_expr, path.as_slice()) {
        (ShapeExpr::ToView { ref_expr }, _) => {
            path.reverse();
            gen_indexing(
                match gen_expr(ref_expr, codegen_ctx) {
                    CheckedExpr::Expr(e) => e,
                    CheckedExpr::ExprIdxCheck(_, _) => panic!("should never happen"),
                },
                &path,
            )
        }
        (ShapeExpr::Tuple { shapes }, [path @ .., prj]) => match prj.eval() {
            Ok(i) => match &shapes[i] {
                ViewOrExpr::V(shape_expr) => gen_shape(shape_expr, path.to_vec(), codegen_ctx),
                ViewOrExpr::E(expr) => gen_shape(
                    &ShapeExpr::ToView {
                        ref_expr: Box::new(expr.clone()),
                    },
                    path.to_vec(),
                    codegen_ctx,
                ), // gen_expr(expr, &mut HashMap::new(), shape_ctx, comp_unit),
            },
            Err(e) => panic!("{:?}", e),
        },
        (ShapeExpr::Idx { idx, shape }, _) => {
            path.push(idx.clone());
            gen_shape(shape, path, codegen_ctx)
        }
        (ShapeExpr::Proj { shape, i }, _) => {
            path.push(desc::Nat::Lit(*i));
            gen_shape(shape, path, codegen_ctx)
        }
        (ShapeExpr::SplitAt { pos, shape }, _) => {
            let proj = path.pop();
            let idx = path.pop();
            match (proj, idx) {
                (Some(pr), Some(i)) => match pr.eval() {
                    Ok(v) => {
                        if v == 0 {
                            path.push(i);
                            gen_shape(shape, path, codegen_ctx)
                        } else if v == 1 {
                            path.push(desc::Nat::BinOp(
                                desc::BinOpNat::Add,
                                Box::new(i),
                                Box::new(pos.clone()),
                            ));
                            gen_shape(shape, path, codegen_ctx)
                        } else {
                            panic!("split_at can only generate a 2-tuple shape.")
                        }
                    }
                    Err(m) => panic!("{:?}", m),
                },
                _ => panic!("Cannot create SplitAt shape. Index or projection missing."),
            }
        }
        (ShapeExpr::Group { size, shape }, _) => {
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
                    gen_shape(shape, path, codegen_ctx)
                }
                (Some(i), None) => {
                    path.push(desc::Nat::BinOp(
                        desc::BinOpNat::Mul,
                        Box::new(i),
                        Box::new(size.clone()),
                    ));
                    gen_shape(shape, path, codegen_ctx)
                }
                _ => panic!("Cannot generate Group shape. One or more indices missing."),
            }
        }
        (ShapeExpr::Join { group_size, shape }, _) => {
            let i = path.pop();
            match i {
                Some(i) => {
                    path.push(desc::Nat::BinOp(
                        desc::BinOpNat::Mod,
                        Box::new(i.clone()),
                        Box::new(group_size.clone()),
                    ));
                    path.push(desc::Nat::BinOp(
                        desc::BinOpNat::Div,
                        Box::new(i),
                        Box::new(group_size.clone()),
                    ));
                    gen_shape(shape, path, codegen_ctx)
                }
                None => panic!("Cannot generate Join shape. Indexing missing."),
            }
        }
        (ShapeExpr::Transpose { shape }, _) => {
            let i = path.pop();
            let j = path.pop();
            match (i, j) {
                (Some(i), Some(j)) => {
                    path.push(i);
                    path.push(j);
                    gen_shape(shape, path, codegen_ctx)
                }
                _ => panic!("Cannot generate Transpose shape. One or more indices missing."),
            }
        }
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
            param_name: name.to_string(),
            ty: cu::Ty::Scalar(cu::ScalarTy::SizeT),
        },
        desc::Kind::Memory => cu::TemplParam::Value {
            param_name: name.to_string(),
            ty: cu::Ty::Scalar(cu::ScalarTy::Memory),
        },
        desc::Kind::DataTy => cu::TemplParam::TyName {
            name: name.to_string(),
        },
        desc::Kind::Provenance => panic!(
            "Cannot generate template parameter for {:?}",
            desc::Kind::Provenance
        ),
    }
}

fn gen_param_decls(param_decls: &[desc::ParamDecl]) -> Vec<cu::ParamDecl> {
    param_decls.iter().map(gen_param_decl).collect()
}

fn gen_param_decl(param_decl: &desc::ParamDecl) -> cu::ParamDecl {
    let desc::ParamDecl { ident, ty, mutbl } = param_decl;
    cu::ParamDecl {
        name: ident.name.to_string(),
        ty: gen_ty(&ty.as_ref().unwrap().ty, *mutbl),
    }
}

fn gen_args_kinded(templ_args: &[desc::ArgKinded]) -> Vec<cu::TemplateArg> {
    templ_args.iter().filter_map(gen_arg_kinded).collect()
}

fn gen_arg_kinded(templ_arg: &desc::ArgKinded) -> Option<cu::TemplateArg> {
    match templ_arg {
        desc::ArgKinded::Nat(n) => Some(cu::TemplateArg::Expr(cu::Expr::Nat(n.clone()))),
        desc::ArgKinded::DataTy(dty) => Some(cu::TemplateArg::Ty(gen_ty(
            &desc::TyKind::Data(Box::new(dty.clone())),
            desc::Mutability::Mut,
        ))),
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
    use desc::DataTyKind as d;
    use desc::TyKind::*;

    let m = desc::Mutability::Mut;
    let cu_ty = match ty {
        Data(dty) => {
            match &dty.dty {
                d::Atomic(a) => match a {
                    desc::ScalarTy::Unit => cu::Ty::Atomic(cu::ScalarTy::Void),
                    desc::ScalarTy::I32 => cu::Ty::Atomic(cu::ScalarTy::I32),
                    desc::ScalarTy::U32 => cu::Ty::Atomic(cu::ScalarTy::U32),
                    desc::ScalarTy::F32 => cu::Ty::Atomic(cu::ScalarTy::F32),
                    desc::ScalarTy::F64 => cu::Ty::Atomic(cu::ScalarTy::F64),
                    desc::ScalarTy::Bool => cu::Ty::Atomic(cu::ScalarTy::Bool),
                    desc::ScalarTy::Gpu => cu::Ty::Atomic(cu::ScalarTy::Gpu),
                },
                d::Scalar(s) => match s {
                    desc::ScalarTy::Unit => cu::Ty::Scalar(cu::ScalarTy::Void),
                    desc::ScalarTy::I32 => cu::Ty::Scalar(cu::ScalarTy::I32),
                    desc::ScalarTy::U32 => cu::Ty::Scalar(cu::ScalarTy::U32),
                    desc::ScalarTy::F32 => cu::Ty::Scalar(cu::ScalarTy::F32),
                    desc::ScalarTy::F64 => cu::Ty::Scalar(cu::ScalarTy::F64),
                    desc::ScalarTy::Bool => cu::Ty::Scalar(cu::ScalarTy::Bool),
                    desc::ScalarTy::Gpu => cu::Ty::Scalar(cu::ScalarTy::Gpu),
                },
                d::Tuple(dtys) => cu::Ty::Tuple(
                    dtys.iter()
                        .map(|dt| gen_ty(&Data(Box::new(dt.clone())), m))
                        .collect(),
                ),
                d::Array(dt, n) => cu::Ty::Array(
                    Box::new(gen_ty(&Data(Box::new(dt.as_ref().clone())), m)),
                    n.clone(),
                ),
                d::At(dt, mem) => {
                    if let desc::Memory::GpuShared = mem {
                        let dty = match dt.as_ref() {
                            desc::DataTy {
                                dty: d::Array(dty, _),
                                ..
                            } => dty.clone(),
                            _ => dt.clone(),
                        };
                        cu::Ty::Ptr(
                            Box::new(gen_ty(&Data(dty), mutbl)),
                            Some(cu::GpuAddrSpace::Shared),
                        )
                    } else {
                        let buff_kind = match mem {
                            desc::Memory::CpuMem => cu::BufferKind::CpuMem,
                            desc::Memory::GpuGlobal => cu::BufferKind::GpuGlobal,
                            desc::Memory::Ident(ident) => {
                                cu::BufferKind::Ident(ident.name.to_string())
                            }
                            desc::Memory::GpuShared => unimplemented!(),
                            desc::Memory::GpuLocal => {
                                panic!(
                                    "GpuLocal is not valid for At types. Should never appear here."
                                )
                            }
                        };
                        cu::Ty::Buffer(Box::new(gen_ty(&Data(dt.clone()), m)), buff_kind)
                    }
                }
                d::Ref(reff) => {
                    let tty = Box::new(gen_ty(
                        &Data(match &reff.dty.dty {
                            // Pointers to arrays point to the element type.
                            d::Array(elem_ty, _) => elem_ty.clone(),
                            _ => reff.dty.clone(),
                        }),
                        m,
                    ));
                    if matches!(reff.own, desc::Ownership::Uniq) {
                        cu::Ty::Ptr(tty, None)
                    } else {
                        cu::Ty::PtrConst(tty, None)
                    }
                }
                d::RawPtr(dt) => {
                    let tty = Box::new(gen_ty(
                        &Data(match &dt.dty {
                            d::Array(_, _) => panic!("should never happen"),
                            _ => dt.clone(),
                        }),
                        desc::Mutability::Mut,
                    ));
                    cu::Ty::Ptr(tty, None)
                }
                // TODO is this correct. I guess we want to generate type identifiers in generic functions.
                d::Ident(ident) => cu::Ty::Ident(ident.name.to_string()),
                d::ArrayShape(dt, n) => cu::Ty::Array(
                    Box::new(gen_ty(&Data(Box::new(dt.as_ref().clone())), m)),
                    n.clone(),
                ),
                d::Dead(_) => {
                    panic!("Dead types are only for type checking and cannot be generated.")
                }
                desc::DataTyKind::Range => {
                    panic!("Cannot generate type for ThreadHierchy or Range")
                }
            }
        }
        FnTy(_) => unimplemented!("needed?"),
    };

    if matches!(mutbl, desc::Mutability::Mut) {
        cu_ty
    } else {
        cu::Ty::Const(Box::new(cu_ty))
    }
}

fn is_dev_fun(exec_ty: &desc::ExecTy) -> bool {
    match &exec_ty.ty {
        desc::ExecTyKind::GpuGrid(_, _)
        | desc::ExecTyKind::GpuBlock(_)
        | desc::ExecTyKind::GpuGlobalThreads(_)
        | desc::ExecTyKind::GpuBlockGrp(_, _)
        | desc::ExecTyKind::GpuThreadGrp(_)
        | desc::ExecTyKind::GpuThread => true,
        desc::ExecTyKind::CpuThread | desc::ExecTyKind::View => false,
    }
}

fn extract_size(ty: &desc::Ty) -> Option<desc::Nat> {
    match &ty.ty {
        desc::TyKind::Data(dty) => match &dty.dty {
            desc::DataTyKind::Array(_, n) => Some(n.clone()),
            desc::DataTyKind::Ref(reff) => match &reff.dty.dty {
                desc::DataTyKind::Array(_, n) => Some(n.clone()),
                desc::DataTyKind::ArrayShape(_, n) => Some(n.clone()),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
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
        shape: Box<ShapeExpr>,
    },
    Join {
        group_size: desc::Nat,
        shape: Box<ShapeExpr>,
    },
    Transpose {
        shape: Box<ShapeExpr>,
    },
}

impl ShapeExpr {
    // Precondition: Expression is a fully typed function application and has type ArrayView.
    fn create_from(expr: &desc::Expr, codegen_ctx: &CodegenCtx) -> ShapeExpr {
        match &expr.expr {
            // TODO this is assuming that f is an identifier
            desc::ExprKind::App(f, gen_args, args) => {
                if let desc::ExprKind::PlaceExpr(pl_expr) = &f.expr {
                    if let desc::PlaceExprKind::Ident(ident) = &pl_expr.pl_expr {
                        if ident.name.as_ref() == ty_check::pre_decl::TO_VIEW
                            || ident.name.as_ref() == ty_check::pre_decl::TO_VIEW_MUT
                        {
                            ShapeExpr::create_to_shape_shape(args)
                        } else if ident.name.as_ref() == ty_check::pre_decl::GROUP
                            || ident.name.as_ref() == ty_check::pre_decl::GROUP_MUT
                        {
                            ShapeExpr::create_group_shape(gen_args, args, codegen_ctx)
                        } else if ident.name.as_ref() == ty_check::pre_decl::JOIN
                            || ident.name.as_ref() == ty_check::pre_decl::JOIN_MUT
                        {
                            ShapeExpr::create_join_shape(gen_args, args, codegen_ctx)
                        } else if ident.name.as_ref() == ty_check::pre_decl::TRANSPOSE
                            || ident.name.as_ref() == ty_check::pre_decl::TRANSPOSE_MUT
                        {
                            ShapeExpr::create_transpose_shape(args, codegen_ctx)
                        } else if let Some(vf) = codegen_ctx
                            .comp_unit
                            .iter()
                            .find(|vf| vf.ident.name == ident.name)
                        {
                            ShapeExpr::applied_shape_fun(
                                vf.generic_params.iter().map(|g| g.ident.name.as_ref()),
                                gen_args,
                                vf.param_decls.iter().map(|p| p.ident.name.as_ref()),
                                args,
                                &vf.body_expr,
                                codegen_ctx,
                            )
                        } else {
                            unimplemented!("There exists no implementation for this view function.")
                        }
                    } else {
                        panic!("Non-globally defined shape functions do not exist.")
                    }
                } else if let desc::ExprKind::Lambda(params, _, _, body) = &f.expr {
                    ShapeExpr::applied_shape_fun(
                        std::iter::empty(),
                        &[],
                        params.iter().map(|p| p.ident.name.as_ref()),
                        args,
                        body,
                        codegen_ctx,
                    )
                } else {
                    panic!("Non-globally defined shape functions do not exist.")
                }
            }
            desc::ExprKind::Split(expr_split) => {
                if let desc::PlaceExpr {
                    pl_expr: desc::PlaceExprKind::Deref(shape),
                    ..
                } = expr_split.view.as_ref()
                {
                    ShapeExpr::create_split_at_shape(&expr_split.pos, shape.as_ref(), codegen_ctx)
                } else {
                    panic!(
                        "An error pointing out that only a value must be split by reborrowing \
                        should have been thrown before."
                    )
                }
            }
            desc::ExprKind::PlaceExpr(pl_expr) => {
                ShapeExpr::create_pl_expr_shape(pl_expr, codegen_ctx)
            }
            desc::ExprKind::Proj(expr, i) => ShapeExpr::Proj {
                shape: Box::new(ShapeExpr::create_from(expr, codegen_ctx)),
                i: *i,
            },
            desc::ExprKind::Tuple(elems) => ShapeExpr::create_tuple_shape(elems, codegen_ctx),
            desc::ExprKind::Ref(_, _, pl_expr) => {
                if let desc::PlaceExprKind::Deref(ple) = &pl_expr.pl_expr {
                    ShapeExpr::create_pl_expr_shape(ple.as_ref(), codegen_ctx)
                } else {
                    panic!("Taking a reference of a view means it must have been reborrowed.")
                }
            }
            desc::ExprKind::Index(pl_expr, idx) => ShapeExpr::Idx {
                idx: idx.clone(),
                shape: Box::new(ShapeExpr::create_from(
                    &desc::Expr::new(desc::ExprKind::PlaceExpr(pl_expr.clone())),
                    codegen_ctx,
                )),
            },
            desc::ExprKind::Select(_, pl_expr, ident_exec) => {
                let exec = codegen_ctx.exec_mapping.get(&ident_exec.name);
                let dim_compo = exec.exec.active_distrib_dim().unwrap();
                ShapeExpr::create_from(
                    &desc::Expr::new(desc::ExprKind::PlaceExpr(pl_expr.clone())),
                    codegen_ctx,
                )
                .par_distrib_shape(dim_compo, exec)
            }
            desc::ExprKind::Block(_, body) => ShapeExpr::create_from(body, codegen_ctx),
            _ => {
                panic!(
                    "Expected a function application, identifer or projection, but found {:?}",
                    expr.expr
                )
            }
        }
    }

    fn applied_shape_fun<'a, I, J>(
        gen_idents: I,
        gen_args: &[desc::ArgKinded],
        param_idents: J,
        args: &[desc::Expr],
        body: &desc::Expr,
        codegen_ctx: &CodegenCtx,
    ) -> ShapeExpr
    where
        I: Iterator<Item = &'a str>,
        J: Iterator<Item = &'a str>,
    {
        let generic_substs = HashMap::from_iter(gen_idents.zip(gen_args));
        let param_substs = HashMap::from_iter(param_idents.zip(args));
        let mut subst_body = body.clone();
        subst_body.subst_kinded_idents(&generic_substs);
        subst_body.subst_idents(&param_substs);
        ShapeExpr::create_from(&subst_body, codegen_ctx)
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

    fn create_pl_expr_shape(shape: &desc::PlaceExpr, codegen_ctx: &CodegenCtx) -> ShapeExpr {
        match shape {
            desc::PlaceExpr {
                pl_expr: desc::PlaceExprKind::Ident(ident),
                ..
            } => codegen_ctx.shape_ctx.get(&ident.name).clone(),
            desc::PlaceExpr {
                pl_expr: desc::PlaceExprKind::Proj(vv, i),
                ..
            } => ShapeExpr::Proj {
                shape: Box::new(ShapeExpr::create_pl_expr_shape(vv, codegen_ctx)),
                i: *i,
            },
            desc::PlaceExpr {
                pl_expr: desc::PlaceExprKind::Deref(_),
                ..
            } => {
                panic!("It is not possible to take references of shapes. This should never happen.")
            }
        }
    }

    fn create_tuple_shape(elems: &[desc::Expr], codegen_ctx: &CodegenCtx) -> ShapeExpr {
        ShapeExpr::Tuple {
            shapes: elems
                .iter()
                .map(|e| {
                    if is_view_dty(e.ty.as_ref().unwrap()) {
                        ViewOrExpr::V(ShapeExpr::create_from(e, codegen_ctx))
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
        codegen_ctx: &CodegenCtx,
    ) -> ShapeExpr {
        ShapeExpr::SplitAt {
            pos: s.clone(),
            shape: Box::new(ShapeExpr::create_from(
                &desc::Expr::new(desc::ExprKind::PlaceExpr(Box::new(shape.clone()))),
                codegen_ctx,
            )),
        }
    }

    fn create_group_shape(
        gen_args: &[desc::ArgKinded],
        args: &[desc::Expr],
        codegen_ctx: &CodegenCtx,
    ) -> ShapeExpr {
        if let (desc::ArgKinded::Nat(s), Some(v)) = (&gen_args[0], args.first()) {
            return ShapeExpr::Group {
                size: s.clone(),
                shape: Box::new(ShapeExpr::create_from(v, codegen_ctx)),
            };
        }
        panic!("Cannot create `group` from the provided arguments.");
    }

    fn create_join_shape(
        gen_args: &[desc::ArgKinded],
        args: &[desc::Expr],
        codegen_ctx: &CodegenCtx,
    ) -> ShapeExpr {
        if let (desc::ArgKinded::Nat(n), Some(v)) = (&gen_args[3], args.first()) {
            return ShapeExpr::Join {
                group_size: n.clone(),
                shape: Box::new(ShapeExpr::create_from(v, codegen_ctx)),
            };
        }
        panic!("Cannot create `to_view` from the provided arguments.");
    }

    fn create_transpose_shape(args: &[desc::Expr], codegen_ctx: &CodegenCtx) -> ShapeExpr {
        if let Some(v) = args.first() {
            return ShapeExpr::Transpose {
                shape: Box::new(ShapeExpr::create_from(v, codegen_ctx)),
            };
        }
        panic!("Cannot create `to_shape` from the provided arguments.");
    }

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
                    ref_expr.expr = desc::ExprKind::PlaceExpr(Box::new(desc::PlaceExpr::new(
                        desc::PlaceExprKind::Ident(desc::Ident::new(&new_name)),
                    )));
                    *count += 1;
                    vec
                }
                ShapeExpr::SplitAt { shape, .. } => {
                    collect_and_rename_input_exprs_rec(shape, count, vec)
                }
                ShapeExpr::Group { shape, .. } => {
                    collect_and_rename_input_exprs_rec(shape, count, vec)
                }
                ShapeExpr::Join { shape, .. } => {
                    collect_and_rename_input_exprs_rec(shape, count, vec)
                }
                ShapeExpr::Transpose { shape, .. } => {
                    collect_and_rename_input_exprs_rec(shape, count, vec)
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
                                expr.expr =
                                    desc::ExprKind::PlaceExpr(Box::new(desc::PlaceExpr::new(
                                        desc::PlaceExprKind::Ident(desc::Ident::new(&new_name)),
                                    )));
                                *count += 1;
                            }
                        }
                    }
                    renamed
                }
                ShapeExpr::Idx { shape, .. } => {
                    collect_and_rename_input_exprs_rec(shape, count, vec)
                }
                ShapeExpr::Proj { shape, .. } => {
                    collect_and_rename_input_exprs_rec(shape, count, vec)
                }
            }
        }
        let vec = vec![];
        let mut count = 0;
        collect_and_rename_input_exprs_rec(self, &mut count, vec)
    }

    fn par_distrib_shape(&self, dim: desc::DimCompo, exec: &desc::ExecExpr) -> Self {
        ShapeExpr::Idx {
            idx: parall_idx(dim, exec),
            shape: Box::new(self.clone()),
        }
    }
}

fn to_parall_indices(exec: &desc::ExecExpr) -> (desc::Nat, desc::Nat, desc::Nat) {
    let mut indices = match &exec.exec.base {
        desc::BaseExec::GpuGrid(_, _) => {
            (desc::Nat::GridIdx, desc::Nat::GridIdx, desc::Nat::GridIdx)
        }
        desc::BaseExec::Ident(_) | desc::BaseExec::CpuThread => unreachable!(),
    };
    for e in &exec.exec.path {
        match e {
            desc::ExecPathElem::SplitProj(split_proj) => {
                if split_proj.proj == 1 {
                    let shift_idx = |idx: desc::Nat| {
                        desc::Nat::BinOp(
                            desc::BinOpNat::Sub,
                            Box::new(idx),
                            Box::new(split_proj.pos.clone()),
                        )
                    };
                    match &split_proj.split_dim {
                        desc::DimCompo::X => indices.0 = shift_idx(indices.0),
                        desc::DimCompo::Y => indices.1 = shift_idx(indices.1),
                        desc::DimCompo::Z => indices.2 = shift_idx(indices.2),
                    }
                }
            }
            desc::ExecPathElem::Distrib(d) => match d {
                desc::DimCompo::X => match contained_par_idx(&indices.0) {
                    Some(desc::Nat::GridIdx) => indices.0 = desc::Nat::BlockIdx(desc::DimCompo::X),
                    Some(desc::Nat::BlockIdx(d)) if d == desc::DimCompo::X => {
                        indices.0 = desc::Nat::ThreadIdx(d)
                    }
                    _ => unreachable!(),
                },
                desc::DimCompo::Y => match contained_par_idx(&indices.1) {
                    Some(desc::Nat::GridIdx) => indices.1 = desc::Nat::BlockIdx(desc::DimCompo::Y),
                    Some(desc::Nat::BlockIdx(d)) if d == desc::DimCompo::Y => {
                        indices.1 = desc::Nat::ThreadIdx(d)
                    }
                    _ => unreachable!(),
                },
                desc::DimCompo::Z => match contained_par_idx(&indices.2) {
                    Some(desc::Nat::GridIdx) => indices.2 = desc::Nat::BlockIdx(desc::DimCompo::Z),
                    Some(desc::Nat::BlockIdx(d)) if d == desc::DimCompo::Z => {
                        indices.2 = desc::Nat::ThreadIdx(d)
                    }
                    _ => unreachable!(),
                },
            },
            // desc::ExecPathElem::ToThreadGrp(grid) => {
            //     assert!(matches!(&grid.exec, desc::ExecPathElem::GpuGrid(_, _)));
            //     let global_idx = |d| {
            //         desc::Nat::BinOp(
            //             desc::BinOpNat::Add,
            //             Box::new(desc::Nat::BinOp(
            //                 desc::BinOpNat::Mul,
            //                 Box::new(desc::Nat::BlockIdx(d)),
            //                 Box::new(desc::Nat::BlockDim(d)),
            //             )),
            //             Box::new(desc::Nat::ThreadIdx(d)),
            //         )
            //     };
            //     (
            //         global_idx(desc::DimCompo::X),
            //         global_idx(desc::DimCompo::Y),
            //         global_idx(desc::DimCompo::Z),
            //     )
            // }
            _ => unreachable!(),
        }
    }

    indices
}

fn contained_par_idx(n: &desc::Nat) -> Option<desc::Nat> {
    struct ContainedParIdx {
        par_idx: Option<desc::Nat>,
    }
    impl Visit for ContainedParIdx {
        fn visit_nat(&mut self, n: &desc::Nat) {
            match n {
                desc::Nat::GridIdx => self.par_idx = Some(n.clone()),
                desc::Nat::BlockIdx(_) => self.par_idx = Some(n.clone()),
                _ => desc::visit::walk_nat(self, n),
            }
        }
    }
    let mut contained = ContainedParIdx { par_idx: None };
    contained.visit_nat(n);
    contained.par_idx
}

fn parall_idx(dim: desc::DimCompo, exec: &desc::ExecExpr) -> desc::Nat {
    match dim {
        desc::DimCompo::X => to_parall_indices(exec).0,
        desc::DimCompo::Y => to_parall_indices(exec).1,
        desc::DimCompo::Z => to_parall_indices(exec).2,
    }
}

fn is_view_dty(ty: &desc::Ty) -> bool {
    match &ty.ty {
        desc::TyKind::Data(dty) => match &dty.dty {
            desc::DataTyKind::Ref(reff) => {
                matches!(
                    reff.dty.as_ref(),
                    desc::DataTy {
                        dty: desc::DataTyKind::ArrayShape(_, _),
                        ..
                    }
                )
            }
            desc::DataTyKind::Tuple(elem_dtys) => elem_dtys
                .iter()
                .all(|d| is_view_dty(&desc::Ty::new(desc::TyKind::Data(Box::new(d.clone()))))),
            _ => false,
        },
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
