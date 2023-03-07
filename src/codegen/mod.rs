mod cu_ast;
mod printer;

use crate::ast as desc;
use crate::ast::utils;
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
        .chain(initial_fns.into_iter())
        // mark kernel functions global
        .map(|mut f| {
            if let Some(ki) = codegen_ctx
                .kernel_infos
                .iter()
                .find(|ki| ki.name == f.fn_sig.name)
            {
                f.fn_sig.exec_kind = cu::ExecKind::Global;
                mv_shrd_mem_params_into_decls(f, &ki.unnamed_shrd_mem_decls, ki.num_shrd_mem_decls)
            } else {
                f
            }
        })
        .map(|f| cu::Item::FnDef(Box::new(f)))
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

fn mv_shrd_mem_params_into_decls(
    mut f: cu::FnDef,
    unnamed_shrd_mem_decls: &dyn Fn(&[String]) -> cu::Stmt,
    num_shared_mem_decls: usize,
) -> cu::FnDef {
    if let cu::Stmt::Block(stmt) = f.body {
        let shrd_mem_params = f
            .fn_sig
            .params
            .drain(f.fn_sig.params.len() - num_shared_mem_decls..)
            .into_iter()
            .map(|p| p.name)
            .collect::<Vec<_>>();
        let decl_seq = unnamed_shrd_mem_decls(&shrd_mem_params);
        let mut with_shrd_mem_decls = vec![decl_seq];
        with_shrd_mem_decls.push(*stmt);
        f.body = cu::Stmt::Block(Box::new(cu::Stmt::Seq(with_shrd_mem_decls)));
    } else {
        panic!("CUDA function was unexpectedly generated without an outer block.")
    };
    f
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
    kernel_infos: Vec<KernelInfo>,
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
            kernel_infos: vec![],
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

struct KernelInfo {
    name: String,
    unnamed_shrd_mem_decls: Box<dyn Fn(&[String]) -> cu::Stmt>,
    num_shrd_mem_decls: usize,
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
        body,
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
        if is_dev_fun(&exec_decl.ty) {
            cu::ExecKind::Device
        } else {
            cu::ExecKind::Host
        },
    );

    cu::FnDef::new(
        fn_sig,
        cu::Stmt::Block(Box::new(gen_stmt(
            &body.body,
            !matches!(
                ret_ty,
                desc::DataTy {
                    dty: desc::DataTyKind::Scalar(desc::ScalarTy::Unit),
                    ..
                }
            ),
            codegen_ctx,
        ))),
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
                                    Some(n.clone()),
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
                addr_space: None,
                expr: None,
                is_extern: false,
            }
        }
        Block(block) => {
            codegen_ctx.push_scope();
            let block_stmt = gen_stmt(&block.body, return_value, codegen_ctx);
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
                                is_extern: false,
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
                                is_extern: false,
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
                                is_extern: false,
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
        AppKernel(app_kernel) => gen_app_kernel(app_kernel, codegen_ctx),
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
                            match ty_check::proj_elem_dty(e.ty.as_ref().unwrap().dty(), i) {
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
            .insert(&ident.name, ShapeExpr::create_from(e, codegen_ctx));
        cu::Stmt::Skip
        // Let Expression
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
            is_extern: false,
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
        is_extern: false,
    };
    let i = cu::Expr::Ident(i_name.to_string());
    codegen_ctx.push_scope();
    codegen_ctx.shape_ctx.insert(
        &ident.name,
        ShapeExpr::Idx {
            idx: desc::Nat::Ident(desc::Ident::new(&i_name)),
            shape: Box::new(if is_view_dty(coll_expr.ty.as_ref().unwrap()) {
                ShapeExpr::create_from(coll_expr, codegen_ctx)
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
            is_extern: false,
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

fn gen_app_kernel(app_kernel: &desc::AppKernel, codegen_ctx: &mut CodegenCtx) -> cu::Stmt {
    let exec_kernel = match &app_kernel.fun.expr {
        desc::ExprKind::PlaceExpr(pl_expr) => {
            if let desc::PlaceExprKind::Ident(ident) = &pl_expr.pl_expr {
                let fn_def = codegen_ctx
                    .comp_unit
                    .iter()
                    .find(|f| &f.ident == ident)
                    .unwrap();
                let tmp_global_fn_call =
                    gen_global_fn_call(fn_def, &app_kernel.gen_args, &app_kernel.args, codegen_ctx);
                let fun_name = convert_to_fn_name(&tmp_global_fn_call.fun);
                let unnamed_shrd_mem_decls =
                    unnamed_shared_mem_decls(app_kernel.shared_mem_dtys.clone());
                let num_shrd_mem_decls = app_kernel.shared_mem_dtys.len();
                codegen_ctx.kernel_infos.push(KernelInfo {
                    name: fun_name.clone(),
                    unnamed_shrd_mem_decls,
                    num_shrd_mem_decls,
                });
                let shared_mem_bytes = count_bytes(&app_kernel.shared_mem_dtys);
                cu::ExecKernel {
                    fun_name,
                    template_args: tmp_global_fn_call.template_args.clone(),
                    grid_dim: Box::new(gen_dim3(&app_kernel.grid_dim)),
                    block_dim: Box::new(gen_dim3(&app_kernel.block_dim)),
                    shared_mem_bytes: Box::new(shared_mem_bytes),
                    args: tmp_global_fn_call.args,
                }
            } else {
                panic!("Unexpected syntactical construct with function type.")
            }
        }
        desc::ExprKind::Lambda(_, _, _, _) => {
            todo!("Is it really necessary and sensible to allow kernel execution of lambdas?")
            // If yes: use exec instead of cu::ExecKernel
            // create_named_fn_call("descend::exec".to_string(), vec![], full_arg_list)
        }
        _ => panic!("Unexpected syntactical construct with function type."),
    };
    cu::Stmt::ExecKernel(Box::new(exec_kernel))
}

fn convert_to_fn_name(f_expr: &cu::Expr) -> String {
    match f_expr {
        cu::Expr::Ident(f_name) => f_name.clone(),
        _ => panic!("The expression does not refer to a function by its identifier."),
    }
}

fn unnamed_shared_mem_decls(dtys: Vec<desc::DataTy>) -> Box<dyn Fn(&[String]) -> cu::Stmt> {
    // Multiple shared memory arrays and Alignments:
    // Memory accesses require that the address be aligned to a multiple of the access size.
    // The access size of a memory instruction is the total number of bytes accessed in memory.
    // There are several ways to make sure the alignment is correct:
    // Pointer P_i for i-th Type T_i based on Base-type B_i, is calculated by
    //     (only works for Arrays and base types):
    //   P_0 = shared_mem_ptr;
    //   P_i = div_rounded_up(P_{i-1} + size(T_{i-1}), size(B_i)) * size(B_i)
    //     where div_rounded_up(A, B) = (A+B-1)/B
    // Faster alignment computation, that works for unsigned offsets and alignments that are
    //  powers of 2:
    // padding = (align - (offset & (align - 1))) & (align - 1)
    //         = -offset & (align - 1)
    // aligned = (offset + (align - 1)) & ~(align - 1)
    //         = (offset + (align - 1)) & -align
    //
    // However, if it is possible to sort the declarations by decreasing natural alignment, then no
    // padding is necessary. The assumption is that the initial pointer is correctly aligned for
    // every data type and that all natural alignments are a power of 2.
    //  https://forums.developer.nvidia.com/t/dynamic-shared-memory-allocation/21671/2
    // Choose the last approach.
    Box::new(move |param_names: &[String]| {
        let buffer_name = "$buffer";
        let extern_shrd_mem_decl = cu::Stmt::VarDecl {
            name: buffer_name.to_string(),
            ty: cu::Ty::CArray(Box::new(cu::Ty::Scalar(cu::ScalarTy::Byte)), None),
            addr_space: Some(cu::GpuAddrSpace::Shared),
            expr: None,
            is_extern: true,
        };
        if param_names.len() != dtys.len() {
            panic!("Exepcted as many shared memory parameter names as data types.")
        }
        let mut names_with_natural_align = param_names
            .iter()
            .zip(&dtys)
            .map(|(name, dty)| {
                let (elem_ty, amount) = get_elem_ty_and_amount(&dty);
                let size_of_elem_dty = size_of_dty(elem_ty.dty());
                (size_of_elem_dty, name, elem_ty, amount)
            })
            .collect::<Vec<_>>();
        names_with_natural_align.sort_unstable_by(
            // sort descending
            |(elem_sizel, _, _, _), (elem_sizer, _, _, _)| elem_sizer.cmp(elem_sizel),
        );
        let mut prev_amount = desc::Nat::Lit(0);
        let mut prev_param_name = buffer_name.to_string();
        let mut decls = vec![extern_shrd_mem_decl];
        for (_, param_name, elem_ty, amount) in names_with_natural_align {
            let current_ptr = cu::Expr::Ref(Box::new(cu::Expr::ArraySubscript {
                array: Box::new(cu::Expr::Ident(prev_param_name.clone())),
                index: prev_amount.clone(),
            }));
            let cu_ty = cu::Ty::Ptr(Box::new(gen_ty(&elem_ty.ty, desc::Mutability::Mut)));
            let cast_current_ptr = cu::Expr::Cast(cu_ty.clone(), Box::new(current_ptr));
            let ptr_decl = cu::Stmt::VarDecl {
                name: param_name.clone(),
                ty: cu::Ty::Const(Box::new(cu_ty)),
                addr_space: None,
                expr: Some(cast_current_ptr),
                is_extern: false,
            };
            decls.push(ptr_decl);
            prev_amount = amount;
            prev_param_name = param_name.clone();
        }
        cu::Stmt::Seq(decls)
    })
}

fn size_of_dty(dty: &desc::DataTy) -> usize {
    match &dty.dty {
        desc::DataTyKind::Scalar(desc::ScalarTy::Bool) => 1,
        desc::DataTyKind::Scalar(desc::ScalarTy::U32)
        | desc::DataTyKind::Scalar(desc::ScalarTy::I32)
        | desc::DataTyKind::Scalar(desc::ScalarTy::F32) => 4,
        desc::DataTyKind::Scalar(desc::ScalarTy::U64)
        | desc::DataTyKind::Scalar(desc::ScalarTy::I64)
        | desc::DataTyKind::Scalar(desc::ScalarTy::F64) => 8,
        _ => panic!("unexpected data type"),
    }
}

fn get_elem_ty_and_amount(dty: &desc::DataTy) -> (desc::Ty, desc::Nat) {
    let nat_1 = desc::Nat::Lit(1);
    match &dty.dty {
        desc::DataTyKind::Scalar(desc::ScalarTy::Bool)
        | desc::DataTyKind::Scalar(desc::ScalarTy::U32)
        | desc::DataTyKind::Scalar(desc::ScalarTy::I32)
        | desc::DataTyKind::Scalar(desc::ScalarTy::F32)
        | desc::DataTyKind::Scalar(desc::ScalarTy::U64)
        | desc::DataTyKind::Scalar(desc::ScalarTy::I64)
        | desc::DataTyKind::Scalar(desc::ScalarTy::F64) => (
            desc::Ty::new(desc::TyKind::Data(Box::new(dty.clone()))),
            nat_1,
        ),
        desc::DataTyKind::Array(arr_elem_dty, n) => {
            let (elem_ty, amount) = get_elem_ty_and_amount(&arr_elem_dty);
            let multiplied_amount =
                desc::Nat::BinOp(desc::BinOpNat::Mul, Box::new(amount), Box::new(n.clone()));
            (elem_ty, multiplied_amount)
        }
        desc::DataTyKind::Scalar(desc::ScalarTy::Unit)
        | desc::DataTyKind::Scalar(desc::ScalarTy::Gpu) => panic!(),
        _ => todo!(),
    }
}

fn count_bytes(dtys: &[desc::DataTy]) -> desc::Nat {
    let mut bytes = desc::Nat::Lit(0);
    for dty in dtys {
        let (elem_ty, amount) = get_elem_ty_and_amount(dty);
        let mul = desc::Nat::BinOp(
            desc::BinOpNat::Mul,
            Box::new(desc::Nat::Lit(size_of_dty(elem_ty.dty()))),
            Box::new(amount),
        );
        bytes = desc::Nat::BinOp(desc::BinOpNat::Add, Box::new(bytes), Box::new(mul));
    }
    bytes
}

fn gen_indep(
    dim_compo: desc::DimCompo,
    pos: &desc::Nat,
    branch_bodies: &[desc::Expr],
    codegen_ctx: &mut CodegenCtx,
) -> cu::Stmt {
    let outer_exec = codegen_ctx.exec.clone();
    codegen_ctx.push_scope();
    codegen_ctx.exec = desc::ExecExpr::new(outer_exec.exec.clone().split_proj(
        dim_compo,
        pos.clone(),
        0,
    ));
    let fst_branch = gen_stmt(&branch_bodies[0], false, codegen_ctx);
    codegen_ctx.drop_scope();
    codegen_ctx.push_scope();
    codegen_ctx.exec = desc::ExecExpr::new(outer_exec.exec.clone().split_proj(
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
    let sync = cu::Stmt::Expr(cu::Expr::FnCall(cu::FnCall::new(
        cu::Expr::Ident("__syncthreads".to_string()),
        vec![],
        vec![],
    )));
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

fn gen_sched(sched: &desc::Sched, codegen_ctx: &mut CodegenCtx) -> cu::Stmt {
    codegen_ctx.push_scope();
    let inner_exec = desc::ExecExpr::new(codegen_ctx.exec.exec.clone().distrib(sched.dim));
    let outer_exec = codegen_ctx.exec.clone();
    if let Some(id) = &sched.inner_exec_ident {
        codegen_ctx
            .exec_mapping
            .insert(&id.name, inner_exec.clone());
    }
    codegen_ctx.exec = inner_exec;
    let stmt = gen_stmt(&sched.body.body, false, codegen_ctx);
    codegen_ctx.exec = outer_exec;
    codegen_ctx.drop_scope();
    cu::Stmt::Seq(vec![cu::Stmt::Block(Box::new(stmt))])
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
                    cu::Stmt::Expr(cu::Expr::FnCall(cu::FnCall::new(
                        cu::Expr::Ident("descend::atomic_set".to_string()),
                        gen_args_kinded(&[ArgKinded::DataTy(DataTy::new(DataTyKind::Scalar(
                            ScalarTy::I32,
                        )))]),
                        vec![
                            cu::Expr::Ident("global_failure".to_string()),
                            cu::Expr::Lit(cu::Lit::I32(incr_idx_check_counter())),
                        ],
                    ))),
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
        Lambda(params, exec_decl, dty, body) => CheckedExpr::Expr(cu::Expr::Lambda {
            captures: {
                // FIXME should list all captures not just generic arguments
                // free_idents(body)
                //     .iter()
                //     .map(|ki| ki.ident.clone())
                //     .collect()
                vec![]
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
                desc::PlaceExprKind::Ident(ident)
                    if ty_check::pre_decl::fun_decls()
                        .iter()
                        .any(|(name, _)| &ident.name.as_ref() == name) =>
                {
                    let pre_decl_ident = desc::Ident::new(&format!("descend::{}", ident.name));
                    CheckedExpr::Expr(cu::Expr::FnCall(create_fn_call(
                        cu::Expr::Ident(pre_decl_ident.name.to_string()),
                        gen_args_kinded(kinded_args),
                        gen_fn_call_args(args, codegen_ctx),
                    )))
                }
                desc::PlaceExprKind::Ident(ident)
                    if codegen_ctx.comp_unit.iter().any(|f| &f.ident == ident) =>
                {
                    CheckedExpr::Expr(cu::Expr::FnCall(gen_global_fn_call(
                        codegen_ctx
                            .comp_unit
                            .iter()
                            .find(|f| &f.ident == ident)
                            .unwrap(),
                        kinded_args,
                        args,
                        codegen_ctx,
                    )))
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
        Sync(exec) => CheckedExpr::Expr(cu::Expr::FnCall(cu::FnCall::new(
            cu::Expr::Ident("__syncthreads".to_string()),
            vec![],
            vec![],
        ))),
        Let(_, _, _)
        | LetUninit(_, _)
        | Block(_)
        | IfElse(_, _, _)
        | If(_, _)
        | Seq(_)
        | While(_, _)
        | For(_, _, _)
        | ForNat(_, _, _)
        | Indep(_)
        | Sched(_)
        | AppKernel(_) => panic!(
            "Trying to generate a statement where an expression is expected:\n{:?}",
            &expr
        ),
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
        "The only case for which this would have to be generated is, when a lambda is called right\
    where it is created. There is no way to bind a lambda with let.\
    And no way for users to write a function that has function parameters."
    )
}

fn gen_global_fn_call(
    fun: &desc::FunDef,
    gen_args: &[desc::ArgKinded],
    args: &[desc::Expr],
    codegen_ctx: &mut CodegenCtx,
) -> cu::FnCall {
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
                    &basis_ref(&ShapeExpr::create_from(arg, &codegen_ctx), &codegen_ctx),
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

fn basis_ref(view: &ShapeExpr, codegen_ctx: &CodegenCtx) -> desc::Expr {
    match view {
        ShapeExpr::ToView { ref_expr } => ref_expr.as_ref().clone(),
        ShapeExpr::SplitAt { shape, .. } => basis_ref(shape, codegen_ctx),
        ShapeExpr::Reverse { shape, .. } => basis_ref(shape, codegen_ctx),
        ShapeExpr::Group { shape, .. } => basis_ref(shape, codegen_ctx),
        ShapeExpr::Join { shape, .. } => basis_ref(shape, codegen_ctx),
        ShapeExpr::Transpose { shape, .. } => basis_ref(shape, codegen_ctx),
        ShapeExpr::Tuple { shapes: elems } => {
            // maybe untrue
            todo!("this case should be removed")
        }
        ShapeExpr::Idx { shape, .. } => basis_ref(shape, codegen_ctx),
        ShapeExpr::Proj { shape, .. } => basis_ref(shape, codegen_ctx),
        ShapeExpr::Map { shape_expr, .. } => basis_ref(
            &ShapeExpr::create_from(shape_expr, codegen_ctx),
            codegen_ctx,
        ),
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
            desc::ExecPathElem::ToThreads(dim) => {
                str.push('T');
                str.push_str(&format!("{}", dim));
                str.push('_');
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
        ShapeExpr::Reverse { shape, .. } => {
            let s = format!("R{}", &stringify_view(shape.as_ref(), c));
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
            str.push_str(&stringify_view(shape.as_ref(), c));
        }
        ShapeExpr::Map { .. } => {
            str.push_str(&desc::utils::fresh_name("M"));
            str.push('_');
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
) -> cu::FnCall {
    create_fn_call(cu::Expr::Ident(name), gen_args, args)
}

fn create_fn_call(
    fun: cu::Expr,
    gen_args: Vec<cu::TemplateArg>,
    params: Vec<cu::Expr>,
) -> cu::FnCall {
    cu::FnCall {
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
        codegen_ctx,
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
    let (_, most_spec_pl) = pl_expr.to_pl_ctx_and_most_specif_pl();
    if codegen_ctx.shape_ctx.contains_key(&most_spec_pl.ident.name) {
        let shape = &ShapeExpr::create_from(
            &desc::Expr::new(desc::ExprKind::PlaceExpr(Box::new(pl_expr.clone()))),
            codegen_ctx,
        );
        gen_shape(shape, vec![], codegen_ctx)
    } else {
        match &pl_expr.pl_expr {
            desc::PlaceExprKind::Ident(ident) => {
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
            desc::PlaceExprKind::SplitAt(_, pl_expr) => gen_pl_expr(pl_expr, codegen_ctx),
            desc::PlaceExprKind::Proj(pl, n) => //match pl_expr.to_place() {
                // // FIXME this does not work when there are tuples inside of shape tuples
                // Some(p) if codegen_ctx.shape_ctx.contains_key(&p.ident.name) => gen_shape(
                //     &codegen_ctx.shape_ctx.get(&p.ident.name).clone(),
                //     p.path.iter().map(|n| desc::Nat::Lit(*n)).collect(),
                //     codegen_ctx,
                // ),
                // _ =>
                cu::Expr::Proj {
                    tuple: Box::new(gen_pl_expr(pl.as_ref(), codegen_ctx)),
                    n: *n,
                },
            desc::PlaceExprKind::Deref(ple) => {
                cu::Expr::Deref(Box::new(gen_pl_expr(ple.as_ref(), codegen_ctx)))
            }
            desc::PlaceExprKind::Select(ple, exec_idents) => {
                let ple = gen_pl_expr(ple.as_ref(), codegen_ctx);
                exec_idents.iter().fold(ple, |expr, i| {
                    let exec = codegen_ctx.exec_mapping.get(&i.name);
                    let dim_compo = exec.exec.active_distrib_dim().unwrap();
                    cu::Expr::ArraySubscript {
                        array: Box::new(expr),
                        index: parall_idx(
                            dim_compo,
                            codegen_ctx.exec_mapping.get(&i.name),
                        ),
                    }
                })
            }
        }
    }
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
        (ShapeExpr::Reverse { size, shape }, _) => {
            let i = path.pop();
            match i {
                Some(i) => {
                    path.push(desc::Nat::BinOp(
                        desc::BinOpNat::Sub,
                        Box::new(desc::Nat::BinOp(
                            desc::BinOpNat::Sub,
                            Box::new(size.clone()),
                            Box::new(desc::Nat::Lit(1)),
                        )),
                        Box::new(i),
                    ));
                    gen_shape(shape, path, codegen_ctx)
                }
                None => panic!("Cannot generate Reverse shape. Index missing."),
            }
        }
        (ShapeExpr::Map { f, shape_expr }, _) => {
            let i = path.pop();
            match i {
                Some(i) => {
                    let idx = desc::Expr::new(desc::ExprKind::Idx(
                        Box::new(shape_expr.as_ref().clone()),
                        i,
                    ));
                    match &f.expr {
                        desc::ExprKind::PlaceExpr(pl_expr) => {
                            if let desc::PlaceExprKind::Ident(ident) = &pl_expr.pl_expr {
                                if let Some(vf) = codegen_ctx
                                    .comp_unit
                                    .iter()
                                    .find(|vf| vf.ident.name == ident.name)
                                {
                                    let app_f = ShapeExpr::applied_shape_fun(
                                        std::iter::empty(),
                                        std::iter::empty(),
                                        vf.param_decls.iter().map(|p| p.ident.name.as_ref()),
                                        &[idx],
                                        &vf.body.body,
                                        codegen_ctx,
                                    );
                                    gen_shape(&app_f, path, codegen_ctx)
                                } else {
                                    panic!("Function definition not found.")
                                }
                            } else {
                                panic!(
                                    "Unexpected syntax construct,\
                                        that should not have a function type."
                                )
                            }
                        }
                        desc::ExprKind::Lambda(param_decl, _, _, body) => {
                            let app_f = ShapeExpr::applied_shape_fun(
                                std::iter::empty(),
                                std::iter::empty(),
                                param_decl.iter().map(|p| p.ident.name.as_ref()),
                                &[idx],
                                body,
                                codegen_ctx,
                            );
                            gen_shape(&app_f, path, codegen_ctx)
                        }
                        _ => panic!(
                            "Unexpected syntax construct,\
                                that should not have a function type."
                        ),
                    }
                }
                None => panic!("Cannot generate Map shape. Index missing."),
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
                    desc::ScalarTy::U32 => cu::Ty::Atomic(cu::ScalarTy::U32),
                    desc::ScalarTy::I32 => cu::Ty::Atomic(cu::ScalarTy::I32),
                    desc::ScalarTy::U64 => cu::Ty::Atomic(cu::ScalarTy::U64),
                    desc::ScalarTy::I64 => cu::Ty::Atomic(cu::ScalarTy::I64),
                    desc::ScalarTy::F32 => cu::Ty::Atomic(cu::ScalarTy::F32),
                    desc::ScalarTy::F64 => cu::Ty::Atomic(cu::ScalarTy::F64),
                    desc::ScalarTy::Bool => cu::Ty::Atomic(cu::ScalarTy::Bool),
                    desc::ScalarTy::Gpu => cu::Ty::Atomic(cu::ScalarTy::Gpu),
                },
                d::Scalar(s) => match s {
                    desc::ScalarTy::Unit => cu::Ty::Scalar(cu::ScalarTy::Void),
                    desc::ScalarTy::U32 => cu::Ty::Scalar(cu::ScalarTy::U32),
                    desc::ScalarTy::U64 => cu::Ty::Scalar(cu::ScalarTy::U64),
                    desc::ScalarTy::I32 => cu::Ty::Scalar(cu::ScalarTy::I32),
                    desc::ScalarTy::I64 => cu::Ty::Scalar(cu::ScalarTy::I64),
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
                        cu::Ty::Ptr(Box::new(gen_ty(&Data(dty), mutbl)))
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
                        cu::Ty::Ptr(tty)
                    } else {
                        cu::Ty::PtrConst(tty)
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
                    cu::Ty::Ptr(tty)
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
    Reverse {
        size: desc::Nat,
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
    Map {
        f: Box<desc::Expr>,
        shape_expr: Box<desc::Expr>,
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
                        } else if ident.name.as_ref() == ty_check::pre_decl::REVERSE
                            || ident.name.as_ref() == ty_check::pre_decl::REVERSE_MUT
                        {
                            ShapeExpr::create_reverse_shape(gen_args, args, codegen_ctx)
                        } else if ident.name.as_ref() == ty_check::pre_decl::MAP
                            || ident.name.as_ref() == ty_check::pre_decl::MAP_MUT
                        {
                            ShapeExpr::create_map_shape(args)
                        } else if let Some(vf) = codegen_ctx
                            .comp_unit
                            .iter()
                            .find(|vf| vf.ident.name == ident.name)
                        {
                            ShapeExpr::applied_shape_fun(
                                vf.generic_params.iter(),
                                gen_args.iter(),
                                vf.param_decls.iter().map(|p| p.ident.name.as_ref()),
                                args,
                                &vf.body.body,
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
                        std::iter::empty(),
                        params.iter().map(|p| p.ident.name.as_ref()),
                        args,
                        body,
                        codegen_ctx,
                    )
                } else {
                    panic!("Non-globally defined shape functions do not exist.")
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
                ShapeExpr::create_pl_expr_shape(pl_expr, codegen_ctx)
            }
            desc::ExprKind::Index(pl_expr, idx) => ShapeExpr::Idx {
                idx: idx.clone(),
                shape: Box::new(ShapeExpr::create_from(
                    &desc::Expr::new(desc::ExprKind::PlaceExpr(pl_expr.clone())),
                    codegen_ctx,
                )),
            },
            desc::ExprKind::Idx(expr, idx) => ShapeExpr::Idx {
                idx: idx.clone(),
                shape: Box::new(ShapeExpr::create_from(expr, codegen_ctx)),
            },
            desc::ExprKind::Block(block) => ShapeExpr::create_from(&block.body, codegen_ctx),
            _ => {
                panic!(
                    "Expected a function application, identifer or projection, but found {:?}",
                    expr.expr
                )
            }
        }
    }

    fn applied_shape_fun<'a, I, J, K>(
        gen_idents: I,
        gen_args: J,
        param_idents: K,
        args: &[desc::Expr],
        body: &desc::Expr,
        codegen_ctx: &CodegenCtx,
    ) -> ShapeExpr
    where
        I: Iterator<Item = &'a desc::IdentKinded>,
        J: Iterator<Item = &'a desc::ArgKinded>,
        K: Iterator<Item = &'a str>,
    {
        let mut subst_body = body.clone();
        utils::subst_idents_kinded(gen_idents, gen_args, &mut subst_body);
        let param_substs = HashMap::from_iter(param_idents.zip(args));
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
                pl_expr: desc::PlaceExprKind::SplitAt(pos, pl_expr),
                ..
            } => Self::create_split_at_shape(pos, pl_expr, codegen_ctx),
            desc::PlaceExpr {
                pl_expr: desc::PlaceExprKind::Select(pl_expr, exec_idents),
                ..
            } => {
                let pl_shape = ShapeExpr::create_from(
                    &desc::Expr::new(desc::ExprKind::PlaceExpr(pl_expr.clone())),
                    codegen_ctx,
                );
                exec_idents.iter().fold(pl_shape, |s, i| {
                    let exec = codegen_ctx.exec_mapping.get(&i.name);
                    let dim_compo = exec.exec.active_distrib_dim().unwrap();
                    s.par_distrib_shape(dim_compo, exec)
                })
            }
            desc::PlaceExpr {
                pl_expr: desc::PlaceExprKind::Deref(ple),
                ..
            } => {
                // If an identifier that refers to an unwrapped shape expression is being dereferenced,
                // just generate from the shape expression and omit generating the dereferencing.
                // The dereferencing will happen through indexing.
                ShapeExpr::create_pl_expr_shape(ple, codegen_ctx)
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

    fn create_reverse_shape(
        gen_args: &[desc::ArgKinded],
        args: &[desc::Expr],
        codegen_ctx: &CodegenCtx,
    ) -> ShapeExpr {
        if let (desc::ArgKinded::Nat(n), Some(v)) = (&gen_args[0], args.first()) {
            return ShapeExpr::Reverse {
                size: n.clone(),
                shape: Box::new(ShapeExpr::create_from(v, codegen_ctx)),
            };
        }
        panic!("Cannot create `reverse` from the provided arguments.");
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

    fn create_map_shape(args: &[desc::Expr]) -> ShapeExpr {
        if let (Some(f), Some(shape_expr)) = (args.first(), args.get(1)) {
            return ShapeExpr::Map {
                f: Box::new(f.clone()),
                shape_expr: Box::new(shape_expr.clone()),
            };
        }
        panic!("Cannot create `map` from provided arguments.");
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
    let mut split_shift = desc::Nat::Lit(0);
    for e in &exec.exec.path {
        match e {
            desc::ExecPathElem::SplitProj(split_proj) => {
                if split_proj.proj == 1 {
                    split_shift = desc::Nat::BinOp(
                        desc::BinOpNat::Add,
                        Box::new(split_shift),
                        Box::new(split_proj.pos.clone()),
                    )
                }
            }
            desc::ExecPathElem::Distrib(d) => match d {
                desc::DimCompo::X => match contained_par_idx(&indices.0) {
                    Some(desc::Nat::GridIdx) => {
                        set_distrib_idx(
                            &mut indices.0,
                            desc::Nat::BlockIdx(desc::DimCompo::X),
                            &mut split_shift,
                        );
                    }
                    Some(desc::Nat::BlockIdx(d)) if d == desc::DimCompo::X => {
                        set_distrib_idx(&mut indices.0, desc::Nat::ThreadIdx(d), &mut split_shift);
                    }
                    _ => unreachable!(),
                },
                desc::DimCompo::Y => match contained_par_idx(&indices.1) {
                    Some(desc::Nat::GridIdx) => set_distrib_idx(
                        &mut indices.1,
                        desc::Nat::BlockIdx(desc::DimCompo::Y),
                        &mut split_shift,
                    ),
                    Some(desc::Nat::BlockIdx(d)) if d == desc::DimCompo::Y => {
                        set_distrib_idx(&mut indices.1, desc::Nat::ThreadIdx(d), &mut split_shift);
                    }
                    _ => unreachable!(),
                },
                desc::DimCompo::Z => match contained_par_idx(&indices.2) {
                    Some(desc::Nat::GridIdx) => set_distrib_idx(
                        &mut indices.2,
                        desc::Nat::BlockIdx(desc::DimCompo::Z),
                        &mut split_shift,
                    ),
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

fn set_distrib_idx(idx: &mut desc::Nat, parall_idx: desc::Nat, shift: &mut desc::Nat) {
    *idx = shift_idx_by(parall_idx, shift.clone());
    *shift = desc::Nat::Lit(0);
}

fn shift_idx_by(idx: desc::Nat, shift: desc::Nat) -> desc::Nat {
    desc::Nat::BinOp(desc::BinOpNat::Sub, Box::new(idx), Box::new(shift))
}

fn parall_idx(dim: desc::DimCompo, exec: &desc::ExecExpr) -> desc::Nat {
    match dim {
        desc::DimCompo::X => to_parall_indices(exec).0,
        desc::DimCompo::Y => to_parall_indices(exec).1,
        desc::DimCompo::Z => to_parall_indices(exec).2,
    }
}

fn gen_dim3(dim: &desc::Dim) -> cu::Expr {
    let one = desc::Nat::Lit(1);
    let (nx, ny, nz) = match dim {
        desc::Dim::X(n) => (n.0.clone(), one.clone(), one),
        desc::Dim::Y(n) => (one.clone(), n.0.clone(), one),
        desc::Dim::Z(n) => (one.clone(), one, n.0.clone()),
        desc::Dim::XY(n) => (n.0.clone(), n.1.clone(), one),
        desc::Dim::XZ(n) => (n.0.clone(), one, n.1.clone()),
        desc::Dim::YZ(n) => (one, n.0.clone(), n.1.clone()),
        desc::Dim::XYZ(n) => (n.0.clone(), n.1.clone(), n.2.clone()),
    };
    let args = vec![cu::Expr::Nat(nx), cu::Expr::Nat(ny), cu::Expr::Nat(nz)];
    cu::Expr::FnCall(cu::FnCall {
        fun: Box::new(cu::Expr::Ident("dim3".to_string())),
        template_args: vec![],
        args,
    })
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
