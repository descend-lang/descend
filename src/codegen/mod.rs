mod cu_ast;
mod printer;

use crate::ast as desc;
use crate::ast::{
    Expr, Ident, Lit, Memory, Mutability, Nat, PlaceExpr, Provenance, ScalarData, Ty,
};
use cu_ast as cu;
use std::collections::HashMap;

// Precondition. all function defitions are successfully typechecked and
// therefore every subexpression stores a type
pub fn gen(program: &desc::GlobalCtx) -> String {
    let cu_program = gen_cuda(program);
    printer::print(&cu_program)
}

fn gen_cuda(program: &desc::GlobalCtx) -> cu::CuProgram {
    let fun_defs = program.fun_defs();
    fun_defs.map(gen_fun_def).collect::<cu::CuProgram>()
}

fn gen_fun_def(gl_fun: &desc::GlobalFunDef) -> cu::Item {
    let desc::GlobalFunDef {
        name,
        ty_idents,
        params,
        ret_ty,
        exec,
        prv_rels: _,
        body_expr,
        fun_ty,
    } = gl_fun;

    cu::Item::FunDef {
        name: name.clone(),
        templ_params: gen_templ_params(ty_idents),
        params: gen_param_decls(params),
        ret_ty: gen_ty(ret_ty, desc::Mutability::Mut),
        body: gen_stmt_expr(body_expr, &mut HashMap::new()).stmt(),
        is_dev_fun: is_dev_fun(*exec),
    }
}

fn gen_stmt_expr(expr: &desc::Expr, view_ctx: &mut HashMap<Ident, View>) -> StmtOrExpr {
    use desc::ExprKind::*;
    use StmtOrExpr::*;
    match &expr.expr {
        GlobalFunIdent(name) => Expr(cu::Expr::Ident(name.clone())),
        Lit(l) => Expr(gen_lit(*l)),
        PlaceExpr(pl_expr) => Expr(gen_pl_expr(pl_expr)),
        Index(pl_expr, n) => Expr(cu::Expr::ArraySubscript {
            array: Box::new(gen_pl_expr(pl_expr)),
            index: n.clone(),
        }),
        Ref(_, _, pl_expr) => Expr(cu::Expr::Ref(Box::new(gen_pl_expr(pl_expr)))),
        BorrowIndex(_, _, pl_expr, n) => Expr(cu::Expr::Ref(Box::new(cu::Expr::ArraySubscript {
            array: Box::new(gen_pl_expr(pl_expr)),
            index: n.clone(),
        }))),
        Assign(pl_expr, expr) => Expr(cu::Expr::Assign {
            lhs: Box::new(gen_pl_expr(pl_expr)),
            rhs: Box::new(gen_stmt_expr(expr, view_ctx).expr()),
        }),
        Let(mutbl, ident, ty, e1, e2) => Stmt(cu::Stmt::Seq(
            Box::new(cu::Stmt::VarDecl {
                name: ident.name.clone(),
                ty: gen_ty(ty, *mutbl),
                expr: Some(gen_stmt_expr(e1, view_ctx).expr()),
            }),
            Box::new(gen_stmt_expr(e2, view_ctx).stmt()),
        )),
        // e1 ; e2
        Seq(e1, e2) => Stmt(cu::Stmt::Seq(
            Box::new(gen_stmt_expr(e1, view_ctx).stmt()),
            Box::new(gen_stmt_expr(e2, view_ctx).stmt()),
        )),
        Lambda(params, exec, ty, expr) => Expr(cu::Expr::Lambda {
            params: gen_param_decls(params.as_slice()),
            body: gen_stmt_expr(expr, view_ctx).stmt(),
            is_dev_fun: is_dev_fun(*exec),
        }),
        DepLambda(params, exec, expr) => unimplemented!(),
        App(fun, args) => Expr(cu::Expr::FunCall {
            fun: Box::new(gen_stmt_expr(fun, view_ctx).expr),
            template_args: gen_templ_args(kind_vals),
            args: args
                .iter()
                .map(|e| gen_stmt_expr(e, view_ctx).expr())
                .collect::<Vec<_>>(),
        }),
        DepApp(dfun, args) => unimplemented!(),
        IfElse(cond, e_tt, e_ff) => unimplemented!(),
        Array(elems) => Expr(cu::Expr::FunCall {
            fun: Box::new(cu::Expr::Ident("descend::create_array".to_string())),
            template_args: vec![],
            args: elems
                .iter()
                .map(|e| gen_stmt_expr(e, view_ctx).expr())
                .collect::<Vec<_>>(),
        }),
        Tuple(elems) => Expr(cu::Expr::Tuple(
            elems
                .iter()
                .map(|el| gen_stmt_expr(el, view_ctx))
                .collect::<Vec<_>>(),
        )),
        For(ident, coll_expr, body) => {
            let i_decl = cu::Stmt::VarDecl {
                name: "_i_".to_string(),
                ty: cu::Ty::Scalar(cu::ScalarTy::SizeT),
                expr: Some(cu::Expr::Lit(cu::Lit::I32(0))),
            };
            let i = cu::Expr::Ident("_i_".to_string());
            Stmt(cu::Stmt::ForLoop {
                init: Box::new(i_decl),
                cond: cu::Expr::BinOp {
                    op: cu::BinOp::Lt,
                    lhs: Box::new(i.clone()),
                    rhs: Box::new(cu::Expr::Nat(
                        coll_size(coll_expr.ty.as_ref().unwrap()).unwrap(),
                    )),
                },
                iter: cu::Expr::Assign {
                    lhs: Box::new(i.clone()),
                    rhs: Box::new(cu::Expr::BinOp {
                        op: cu::BinOp::Add,
                        lhs: Box::new(i.clone()),
                        rhs: Box::new(cu::Expr::Lit(cu::Lit::I32(1))),
                    }),
                },
                // TODO in body: substitute x for fitting expr including _i_
                stmt: Box::new(gen_stmt_expr(body, view_ctx).stmt()),
            })
        }
        ParForSync(ident, view_expr, parall_config_expr, body) => cu::Expr::FunCall {
            fun: Box::new(cu::Expr::Ident("descend::par_for".to_string())),
            template_args: vec![],
            args: elems
                .iter()
                .map(|e| gen_stmt_expr(e, view_ctx).expr())
                .collect::<Vec<_>>(),
        },
        Binary(op, lhs, rhs) => unimplemented!(),
        Unary(op, arg) => unimplemented!(),
    }
}

enum StmtOrExpr {
    Stmt(cu::Stmt),
    Expr(cu::Expr),
}

impl StmtOrExpr {
    fn stmt(self) -> cu::Stmt {
        match self {
            StmtOrExpr::Stmt(stmt) => stmt,
            _ => panic!("Expected Stmt but found Expr."),
        }
    }

    fn expr(self) -> cu::Expr {
        match self {
            StmtOrExpr::Expr(expr) => expr,
            _ => panic!("Expected Expr but found Stmt"),
        }
    }
}

// TODO move to a higher module and make sure that this is the only place at which
//  View has to be extended
pub enum View {
    ToView {
        r: Provenance,
        mem: Memory,
        n: Nat,
        ty: Ty,
        expr: Expr,
    },
    Group {
        size: Nat,
        n: Nat,
        ty: Ty,
        view: Box<View>,
    },
    Split {
        pos: Nat,
        rest: Nat,
        ty: Ty,
        view: Box<View>,
    },
    Join {
        m: Nat,
        n: Nat,
        ty: Ty,
        view: Box<View>,
    },
    Transpose {
        m: Nat,
        n: Nat,
        ty: Ty,
        view: Box<View>,
    },
    Zip {
        n: Nat,
        fst_ty: Ty,
        snd_ty: Ty,
        fst: Box<View>,
        snd: Box<View>,
    },
    Take {
        num: Nat,
        n: Nat,
        ty: Ty,
        view: Box<View>,
    },
    Drop {
        num: Nat,
        n: Nat,
        ty: Ty,
        view: Box<View>,
    },
}

fn gen_lit(l: Lit) -> cu::Expr {
    match l {
        Lit::Unit => cu::Expr::Lit(cu::Lit::Void),
        Lit::Bool(b) => cu::Expr::Lit(cu::Lit::Bool(b)),
        Lit::I32(i) => cu::Expr::Lit(cu::Lit::I32(i)),
        Lit::F32(f) => cu::Expr::Lit(cu::Lit::F32(f)),
    }
}

fn gen_pl_expr(pl_expr: &PlaceExpr) -> cu::Expr {
    match pl_expr {
        PlaceExpr::Proj(pl, n) => cu::Expr::Proj {
            tuple: Box::new(gen_pl_expr(pl.as_ref())),
            n: n.clone(),
        },
        PlaceExpr::Deref(pl) => cu::Expr::Deref(Box::new(gen_pl_expr(pl.as_ref()))),
        PlaceExpr::Var(ident) => cu::Expr::Ident(ident.name.clone()),
    }
}

fn gen_templ_params(ty_idents: &[desc::IdentKinded]) -> Vec<cu::TemplParam> {
    // ty_idents.iter().filter
    unimplemented!()
}

fn gen_param_decls(params: &[desc::IdentTyped]) -> Vec<cu::ParamDecl> {
    unimplemented!()
}

fn gen_ty(ty: &desc::Ty, mutbl: desc::Mutability) -> cu::Ty {
    unimplemented!()
}

fn is_dev_fun(exec: desc::ExecLoc) -> bool {
    match exec {
        // TODO correct?
        desc::ExecLoc::GpuGroup | desc::ExecLoc::GpuThread => true,
        desc::ExecLoc::CpuThread => false,
    }
}

fn coll_size(ty: &desc::Ty) -> Option<Nat> {
    match ty {
        desc::Ty::Array(_, n) => Some(n.clone()),
        _ => None,
    }
}
