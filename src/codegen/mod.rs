mod cu_ast;
mod printer;

use crate::ast as desc;
use crate::ast::Mutability;
use cu_ast as cu;
use std::collections::HashMap;

// Precondition. all function defitions are successfully typechecked and
// therefore every subexpression stores a type
pub fn gen(comp_unit: &desc::CompilUnit) -> String {
    let cu_program = comp_unit.iter().map(gen_fun_def).collect::<cu::CuProgram>();
    printer::print(&cu_program)
}

fn gen_fun_def(gl_fun: &desc::GlobalFunDef) -> cu::Item {
    let desc::GlobalFunDef {
        name,
        generic_params: ty_idents,
        params,
        ret_ty,
        exec,
        prv_rels: _,
        body_expr,
        ..
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

fn gen_stmt_expr(expr: &desc::Expr, view_ctx: &mut HashMap<desc::Ident, View>) -> StmtOrExpr {
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
            ret_ty: gen_ty(ty, Mutability::Mut),
            is_dev_fun: is_dev_fun(*exec),
        }),
        App(fun, kinded_args, args) => Expr(cu::Expr::FunCall {
            fun: Box::new(gen_stmt_expr(fun, view_ctx).expr),
            template_args: gen_kinded_args(kinded_args),
            args: args
                .iter()
                .map(|e| gen_stmt_expr(e, view_ctx).expr())
                .collect::<Vec<_>>(),
        }),
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
            let i_name = crate::utils::fresh_name("_i_");
            let i_decl = cu::Stmt::VarDecl {
                name: i_name.clone(),
                ty: cu::Ty::Scalar(cu::ScalarTy::SizeT),
                expr: Some(cu::Expr::Lit(cu::Lit::I32(0))),
            };
            let i = cu::Expr::Ident(i_name);
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
        ParForSync(ident, view_expr, parall_config_expr, body) => unimplemented!(),
        //     cu::Expr::FunCall {
        //     fun: Box::new(cu::Expr::Ident("descend::par_for".to_string())),
        //     template_args: vec![],
        //     args: elems
        //         .iter()
        //         .map(|e| gen_stmt_expr(e, view_ctx).expr())
        //         .collect::<Vec<_>>(),
        // },
        Binary(op, lhs, rhs) => unimplemented!(),
        Unary(op, arg) => unimplemented!(),
    }
}

// TODO move to a higher module and make sure that this is the only place at which
//  View has to be extended
//  or Lower Module, which ever fits better. Also then remove the paths in front of Types
pub enum View {
    ToView {
        r: desc::Provenance,
        mem: desc::Memory,
        n: desc::Nat,
        ty: desc::Ty,
        expr: desc::Expr,
    },
    Group {
        size: desc::Nat,
        n: desc::Nat,
        ty: desc::Ty,
        view: Box<View>,
    },
    Split {
        pos: desc::Nat,
        rest: desc::Nat,
        ty: desc::Ty,
        view: Box<View>,
    },
    Join {
        m: desc::Nat,
        n: desc::Nat,
        ty: desc::Ty,
        view: Box<View>,
    },
    Transpose {
        m: desc::Nat,
        n: desc::Nat,
        ty: desc::Ty,
        view: Box<View>,
    },
    Zip {
        n: desc::Nat,
        fst_ty: desc::Ty,
        snd_ty: desc::Ty,
        fst: Box<View>,
        snd: Box<View>,
    },
    Take {
        num: desc::Nat,
        n: desc::Nat,
        ty: desc::Ty,
        view: Box<View>,
    },
    Drop {
        num: desc::Nat,
        n: desc::Nat,
        ty: desc::Ty,
        view: Box<View>,
    },
}

fn gen_lit(l: desc::Lit) -> cu::Expr {
    match l {
        desc::Lit::Bool(b) => cu::Expr::Lit(cu::Lit::Bool(b)),
        desc::Lit::I32(i) => cu::Expr::Lit(cu::Lit::I32(i)),
        desc::Lit::F32(f) => cu::Expr::Lit(cu::Lit::F32(f)),
        desc::Lit::Unit => unimplemented!(
            "How to deal with this? \
            (provide custom unit type in C or do not allow () literals)"
        ),
    }
}

fn gen_pl_expr(pl_expr: &desc::PlaceExpr) -> cu::Expr {
    match pl_expr {
        desc::PlaceExpr::Proj(pl, n) => cu::Expr::Proj {
            tuple: Box::new(gen_pl_expr(pl.as_ref())),
            n: n.clone(),
        },
        desc::PlaceExpr::Deref(pl) => cu::Expr::Deref(Box::new(gen_pl_expr(pl.as_ref()))),
        desc::PlaceExpr::Var(ident) => cu::Expr::Ident(ident.name.clone()),
    }
}

fn gen_templ_params(ty_idents: &[desc::IdentKinded]) -> Vec<cu::TemplParam> {
    ty_idents
        .iter()
        .filter(|desc::IdentKinded { ident, kind }| {
            !(matches!(kind, desc::Kind::Frame)
                || matches!(kind, desc::Kind::Provenance)
                || matches!(kind, desc::Kind::Own))
        })
        .map(gen_templ_param)
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
        ty: gen_ty(ty, *mutbl),
    }
}

fn gen_kinded_args(templ_args: &[desc::KindedArg]) -> Vec<cu::TemplateArg> {
    templ_args.iter().map(gen_kinded_arg).collect()
}

fn gen_kinded_arg(templ_arg: &desc::KindedArg) -> cu::TemplateArg {
    match templ_arg {
        // TODO think about this:
        //  this mistreats typename identifiers as Expr. The generated code should still be correct
        //  though.
        desc::KindedArg::Ident(ident) => cu::TemplateArg::Expr(cu::Expr::Ident(ident.name.clone())),
        desc::KindedArg::Nat(n) => cu::TemplateArg::Expr(cu::Expr::Nat(n.clone())),
        desc::KindedArg::Memory(mem) => cu::TemplateArg::Expr(cu::Expr::Ident(match mem {
            desc::Memory::Ident(ident) => ident.name.clone(),
            desc::Memory::GpuGlobal => "Memory::GpuGlobal".to_string(),
            desc::Memory::GpuShared => unimplemented!("TODO!"),
            desc::Memory::CpuHeap => "Memory::CpuHeap".to_string(),
            desc::Memory::CpuStack => {
                panic!("CpuStack is not valid for At types. Should never appear here.")
            }
        })),
        desc::KindedArg::Ty(ty) => cu::TemplateArg::Ty(gen_ty(ty, desc::Mutability::Mut)),
        desc::KindedArg::Provenance(_) => {
            panic!("Provenances are only used for type checking and cannot be generated.")
        }
    }
}

// Param mutbl is not strictly necessary because every const type can just be wrapped
// in cu::Ty::Const. However, the formalism uses this, because it shows the generated code
// as opposed to a Cuda-AST and there, the order of the const is odd
// when it comes to pointers (C things).
fn gen_ty(ty: &desc::Ty, mutbl: desc::Mutability) -> cu::Ty {
    let m = desc::Mutability::Mut;
    let cu_ty = match ty {
        desc::Ty::Scalar(s) => match s {
            desc::ScalarTy::Unit => cu::Ty::Scalar(cu::ScalarTy::Void),
            desc::ScalarTy::I32 => cu::Ty::Scalar(cu::ScalarTy::I32),
            desc::ScalarTy::F32 => cu::Ty::Scalar(cu::ScalarTy::I32),
            desc::ScalarTy::Bool => cu::Ty::Scalar(cu::ScalarTy::Bool),
        },
        desc::Ty::Tuple(tys) => cu::Ty::Tuple(tys.iter().map(|ty| gen_ty(ty, m)).collect()),
        desc::Ty::Array(ty, n) => cu::Ty::Array(Box::new(gen_ty(ty, m)), n.clone()),
        desc::Ty::ArrayView(_, _) => {
            panic!("This type has no C representation and should be compiled away.")
        }
        desc::Ty::At(ty, mem) => {
            let buff_kind = match mem {
                desc::Memory::CpuHeap => cu::BufferKind::Heap,
                desc::Memory::GpuGlobal => cu::BufferKind::Gpu,
                desc::Memory::Ident(ident) => cu::Ty::Ident(ident.name.clone()),
                desc::Memory::GpuShared => unimplemented!("big TODO!"),
                desc::Memory::CpuStack => {
                    panic!("CpuStack is not valid for At types. Should never appear here.")
                }
            };
            cu::Ty::Buffer(Box::new(gen_ty(ty, m)), buff_kind)
        }
        desc::Ty::Fn(_, _, _, _, _) => unimplemented!("needed?"),
        desc::Ty::Dead(_) => {
            panic!("Dead types are only for type checking and cannot be generated.")
        }
        desc::Ty::Ref(_, own, _, ty) => {
            let cty = Box::new(gen_ty(ty, m));
            if matches!(own, desc::Ownership::Uniq) {
                cu::Ty::Ptr(cty)
            } else {
                cu::Ty::PtrConst(cty)
            }
        }
        desc::Ty::Gpu => unimplemented!("needs changes"),
        // TODO is this correct. I guess we want to generate type identifiers in generic functions.
        desc::Ty::Ident(ident) => cu::Ty::Ident(ident.name.clone()),
    };

    if matches!(mutbl, desc::Mutability::Mut) {
        cu_ty
    } else {
        cu::Ty::Const(Box::new(cu_ty))
    }
}

fn is_dev_fun(exec: desc::ExecLoc) -> bool {
    match exec {
        // TODO correct?
        desc::ExecLoc::GpuGroup | desc::ExecLoc::GpuThread => true,
        desc::ExecLoc::CpuThread => false,
    }
}

fn coll_size(ty: &desc::Ty) -> Option<desc::Nat> {
    match ty {
        desc::Ty::Array(_, n) => Some(n.clone()),
        _ => None,
    }
}
