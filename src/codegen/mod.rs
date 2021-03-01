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

#[derive(Debug)]
enum StmtOrExpr {
    Stmt(cu::Stmt),
    Expr(cu::Expr),
}

impl StmtOrExpr {
    fn stmt(self) -> cu::Stmt {
        match self {
            StmtOrExpr::Stmt(stmt) => stmt,
            StmtOrExpr::Expr(e) => panic!("Expected Stmt but found Expr\n {:?}", e),
        }
    }

    fn expr(self) -> cu::Expr {
        match self {
            StmtOrExpr::Expr(expr) => expr,
            StmtOrExpr::Stmt(s) => panic!("Expected Expr but found Stmt\n {:?}", s),
        }
    }
}

// TODO how to deal with return values from descend to cuda. Last expr of sequence not a statement.
fn gen_stmt_expr(expr: &desc::Expr, view_ctx: &mut HashMap<String, ViewExpr>) -> StmtOrExpr {
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
        LetProv(_, expr) => gen_stmt_expr(expr, view_ctx),
        BorrowIndex(_, _, pl_expr, n) => Expr(cu::Expr::Ref(Box::new(cu::Expr::ArraySubscript {
            array: Box::new(gen_pl_expr(pl_expr)),
            index: n.clone(),
        }))),
        Assign(pl_expr, expr) => Expr(cu::Expr::Assign {
            lhs: Box::new(gen_pl_expr(pl_expr)),
            rhs: Box::new(gen_stmt_expr(expr, view_ctx).expr()),
        }),
        Let(mutbl, ident, ty, e1, e2) => {
            let e2_stmt = gen_ret_if_not_sequenced(e2, view_ctx);
            // Let ArrayView
            if matches!(ty, desc::Ty::ArrayView(_, _)) {
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
                Stmt(e2_stmt)
            // Let Expression
            } else {
                Stmt(cu::Stmt::Seq(
                    Box::new(cu::Stmt::VarDecl {
                        name: ident.name.clone(),
                        ty: gen_ty(ty, *mutbl),
                        expr: Some(gen_stmt_expr(e1, view_ctx).expr()),
                    }),
                    Box::new(e2_stmt),
                ))
            }
        }
        // e1 ; e2
        Seq(e1, e2) => Stmt(
            // TODO this is weird. Assumptions are, that left side has no seq nor let (so no sequencing) or every sequence ends in
            //  a stmt. Currently, with unit type it is possible to create a sequence by function
            //  composition. However, we never generate code that really returns a unit value. Can still
            //  be generated. Think about this.
            cu::Stmt::Seq(
                Box::new(gen_stmt_expr(e1, view_ctx).stmt()),
                Box::new(gen_ret_if_not_sequenced(e2, view_ctx)),
            ),
        ),
        Lambda(params, exec, ty, expr) => Expr(cu::Expr::Lambda {
            params: gen_param_decls(params.as_slice()),
            body: Box::new(gen_stmt_expr(expr, view_ctx).stmt()),
            ret_ty: gen_ty(ty, desc::Mutability::Mut),
            is_dev_fun: is_dev_fun(*exec),
        }),
        App(fun, kinded_args, args) => Expr(cu::Expr::FunCall {
            fun: Box::new(gen_stmt_expr(fun, view_ctx).expr()),
            template_args: gen_args_kinded(kinded_args),
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
                .map(|el| gen_stmt_expr(el, view_ctx).expr())
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
        ParForSync(ident, view_expr, glb_cfg_expr, body) => {
            let v = ViewExpr::create_from(view_expr, view_ctx);
            let source_pl_exprs = v.collect_pl_exprs();
            let param_decls: Vec<_> = source_pl_exprs
                .iter()
                .enumerate()
                .map(|(i, pl_expr)| cu::ParamDecl {
                    name: format!("p{}", i),
                    ty: gen_ty(pl_expr.ty.as_ref().unwrap(), Mutability::Const),
                })
                .collect();
            let idx = cu::Expr::BinOp {
                op: cu::BinOp::Add,
                lhs: Box::new(cu::Expr::BinOp {
                    op: cu::BinOp::Mul,
                    lhs: Box::new(cu::Expr::Ident("blockIdx.x".to_string())),
                    rhs: Box::new(cu::Expr::Ident("blockDim.x".to_string())),
                }),
                rhs: Box::new(cu::Expr::Ident("threadIdx.x".to_string())),
            };
            let res = view_ctx.insert(
                ident.name.clone(),
                ViewExpr::Idx {
                    idx,
                    view: Box::new(v),
                },
            );
            if res.is_some() {
                panic!(
                    "Conflicting names. View variable `{}` used twice.",
                    ident.name
                )
            }
            let glb_cfg = gen_stmt_expr(glb_cfg_expr, &mut HashMap::new()).expr();
            let loop_body = cu::Expr::Lambda {
                params: param_decls,
                body: Box::new(gen_stmt_expr(body, view_ctx).stmt()),
                ret_ty: cu::Ty::Scalar(cu::ScalarTy::Void),
                is_dev_fun: true,
            };
            let mut input: Vec<_> = source_pl_exprs
                .iter()
                .map(|e| gen_stmt_expr(e, view_ctx).expr())
                .collect();
            let mut args: Vec<cu::Expr> = vec![loop_body, glb_cfg];
            args.append(&mut input);
            Stmt(cu::Stmt::Expr(cu::Expr::FunCall {
                fun: Box::new(cu::Expr::Ident("descend::par_for".to_string())),
                template_args: vec![],
                args,
            }))
        }
        BinOp(op, lhs, rhs) => Expr(cu::Expr::BinOp {
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
            lhs: Box::new(gen_stmt_expr(lhs, view_ctx).expr()),
            rhs: Box::new(gen_stmt_expr(rhs, view_ctx).expr()),
        }),
        UnOp(op, arg) => Expr(cu::Expr::UnOp {
            op: match op {
                desc::UnOp::Deref => cu::UnOp::Deref,
                desc::UnOp::Not => cu::UnOp::Not,
                desc::UnOp::Neg => cu::UnOp::Neg,
            },
            arg: Box::new(gen_stmt_expr(arg, view_ctx).expr()),
        }),
    }
}

// TODO related to cu::Expr::Empty.
//  This is an ad-hoc solution for dealing with unit type and its value.
fn gen_ret_if_not_sequenced(e: &desc::Expr, view_ctx: &mut HashMap<String, ViewExpr>) -> cu::Stmt {
    let e_stmt_or_expr = gen_stmt_expr(e, view_ctx);
    match (&e.expr, &e.ty) {
        (desc::ExprKind::Seq(_, _), _) | (desc::ExprKind::Let(_, _, _, _, _), _) => {
            e_stmt_or_expr.stmt()
        }
        (desc::ExprKind::Lit(_), Some(desc::Ty::Scalar(desc::ScalarTy::Unit)))
        | (desc::ExprKind::App(_, _, _), Some(desc::Ty::Scalar(desc::ScalarTy::Unit))) => {
            cu::Stmt::Return(Some(e_stmt_or_expr.expr()))
        }
        (_, Some(desc::Ty::Scalar(desc::ScalarTy::Unit))) => e_stmt_or_expr.stmt(),
        _ => cu::Stmt::Return(Some(e_stmt_or_expr.expr())),
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

fn gen_pl_expr(pl_expr: &desc::PlaceExpr) -> cu::Expr {
    match pl_expr {
        desc::PlaceExpr::Proj(pl, n) => cu::Expr::Proj {
            tuple: Box::new(gen_pl_expr(pl.as_ref())),
            n: n.clone(),
        },
        desc::PlaceExpr::Deref(pl) => cu::Expr::Deref(Box::new(gen_pl_expr(pl.as_ref()))),
        desc::PlaceExpr::Ident(ident) => cu::Expr::Ident(ident.name.clone()),
    }
}

fn gen_templ_params(ty_idents: &[desc::IdentKinded]) -> Vec<cu::TemplParam> {
    ty_idents
        .iter()
        .filter_map(|ty_ident| {
            if !(matches!(ty_ident.kind, desc::Kind::Frame)
                || matches!(ty_ident.kind, desc::Kind::Provenance))
            {
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
        ty: gen_ty(ty, *mutbl),
    }
}

fn gen_args_kinded(templ_args: &[desc::ArgKinded]) -> Vec<cu::TemplateArg> {
    templ_args
        .iter()
        .filter_map(|ka| match ka {
            desc::ArgKinded::Provenance(_) | desc::ArgKinded::Frame(_) => None,
            _ => Some(gen_arg_kinded(ka)),
        })
        .collect()
}

fn gen_arg_kinded(templ_arg: &desc::ArgKinded) -> cu::TemplateArg {
    match templ_arg {
        // TODO think about this:
        desc::ArgKinded::Ident(ident) => cu::TemplateArg::Ty(cu::Ty::Ident(ident.name.clone())),
        desc::ArgKinded::Nat(n) => cu::TemplateArg::Expr(cu::Expr::Nat(n.clone())),
        desc::ArgKinded::Memory(mem) => cu::TemplateArg::Expr(cu::Expr::Ident(match mem {
            desc::Memory::Ident(ident) => ident.name.clone(),
            desc::Memory::GpuGlobal => "Memory::GpuGlobal".to_string(),
            desc::Memory::GpuShared => unimplemented!("TODO!"),
            desc::Memory::CpuHeap => "Memory::CpuHeap".to_string(),
            desc::Memory::CpuStack => {
                panic!("CpuStack is not valid for At types. Should never appear here.")
            }
        })),
        desc::ArgKinded::Ty(ty) => cu::TemplateArg::Ty(gen_ty(ty, desc::Mutability::Mut)),
        // TODO the panic message is not entirely true. Exec IS important when it appears in a type
        //  in order to determine __device__ annotations. However, there is no way to generate
        //  an Exec::Ident which means these must not be used by users and are only for
        desc::ArgKinded::Exec(_) => panic!(
            "This should not be allowed and is currently a problem \
        with the design of execution locations. See Issue #3."
        ),
        desc::ArgKinded::Provenance(_) | desc::ArgKinded::Frame(_) => panic!(
            "Provenances and Frames are only used for type checking and cannot be generated."
        ),
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
            desc::ScalarTy::Gpu => cu::Ty::Scalar(cu::ScalarTy::Gpu),
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
                desc::Memory::Ident(ident) => cu::BufferKind::Ident(ident.name.clone()),
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
        // TODO is this correct. I guess we want to generate type identifiers in generic functions.
        desc::Ty::Ident(ident) => cu::Ty::Ident(ident.name.clone()),
    };

    if matches!(mutbl, desc::Mutability::Mut) {
        cu_ty
    } else {
        cu::Ty::Const(Box::new(cu_ty))
    }
}

// TODO correct?
fn is_dev_fun(exec: desc::ExecLoc) -> bool {
    match exec {
        desc::ExecLoc::GpuGroup | desc::ExecLoc::GpuThread => true,
        desc::ExecLoc::CpuThread | desc::ExecLoc::View => false,
    }
}

fn coll_size(ty: &desc::Ty) -> Option<desc::Nat> {
    match ty {
        desc::Ty::Array(_, n) => Some(n.clone()),
        _ => None,
    }
}

// Views are parsed as normal predeclared functions so that it is possible to infer types.
// ----- After typechecking the AST is updated to contain views instead of function applications of
// ----- predeclard view functions. (first idea)
// +++++ During code generation view function applications are converted to View Variants and used
// +++++ to generate Indices.
#[derive(Debug, Clone)]
enum ViewExpr {
    ToView {
        // only needed for type checking
        // r: desc::Provenance,
        // mem: desc::Memory,
        // TODO are the nat and type needed?
        n: desc::Nat,
        ty: desc::Ty,
        // box to reduce variant's size
        pl_expr: Box<desc::Expr>,
    },
    Idx {
        // TODO Nat or something else?
        idx: cu::Expr,
        view: Box<ViewExpr>,
    },
    Group {
        size: desc::Nat,
        n: desc::Nat,
        ty: desc::Ty,
        view: Box<ViewExpr>,
    },
    Join {
        m: desc::Nat,
        n: desc::Nat,
        ty: desc::Ty,
        view: Box<ViewExpr>,
    },
    Transpose {
        m: desc::Nat,
        n: desc::Nat,
        ty: desc::Ty,
        view: Box<ViewExpr>,
    },
    // Split {
    //     pos: desc::Nat,
    //     rest: desc::Nat,
    //     ty: desc::Ty,
    //     view: Box<ViewExpr>,
    // },
    // Zip {
    //     n: desc::Nat,
    //     fst_ty: desc::Ty,
    //     snd_ty: desc::Ty,
    //     fst: Box<ViewExpr>,
    //     snd: Box<ViewExpr>,
    // },
    // Take {
    //     num: desc::Nat,
    //     n: desc::Nat,
    //     ty: desc::Ty,
    //     view: Box<ViewExpr>,
    // },
    // Drop {
    //     num: desc::Nat,
    //     n: desc::Nat,
    //     ty: desc::Ty,
    //     view: Box<ViewExpr>,
    // },
}

impl ViewExpr {
    // Precondition: Expression is a fully typed function application and has type ArrayView.
    fn create_from(expr: &desc::Expr, view_ctx: &HashMap<String, ViewExpr>) -> ViewExpr {
        if !matches!(expr.ty, Some(desc::Ty::ArrayView(_, _))) {
            panic!(
                "Expected expression of type ArrayView, but found {:?}",
                expr.ty
            );
        }

        match &expr.expr {
            // TODO this is assuming that f is an identifier
            //  We have to redesign Views to not be data types...
            desc::ExprKind::App(f, gen_args, args) => {
                if let desc::ExprKind::GlobalFunIdent(name) = &f.expr {
                    if name == crate::ty_check::pre_decl::TO_VIEW {
                        ViewExpr::create_to_view_view(gen_args, args)
                    } else if name == crate::ty_check::pre_decl::GROUP {
                        ViewExpr::create_group_view(gen_args, args, view_ctx)
                    } else if name == crate::ty_check::pre_decl::JOIN {
                        ViewExpr::create_join_view(gen_args, args, view_ctx)
                    } else if name == crate::ty_check::pre_decl::TRANSPOSE {
                        ViewExpr::create_transpose_view(gen_args, args, view_ctx)
                    } else {
                        unimplemented!()
                    }
                } else {
                    panic!("Non-globally defined view functions do not exist.")
                }
            }
            desc::ExprKind::PlaceExpr(desc::PlaceExpr::Ident(ident)) => {
                view_ctx.get(&ident.name).unwrap().clone()
            }
            _ => panic!("Expected a function application, but found {:?}", expr.expr),
        }
    }

    fn create_to_view_view(gen_args: &[desc::ArgKinded], args: &[desc::Expr]) -> ViewExpr {
        if let (desc::ArgKinded::Nat(n), desc::ArgKinded::Ty(ty), Some(pl_expr)) =
            (&gen_args[2], &gen_args[3], args.first())
        {
            // e cannot contain views, so the view_ctx can be empty
            return ViewExpr::ToView {
                n: n.clone(),
                ty: ty.clone(),
                pl_expr: Box::new(pl_expr.clone()),
            };
        }
        panic!("Cannot create `to_view` from the provided arguments.");
    }

    fn create_group_view(
        gen_args: &[desc::ArgKinded],
        args: &[desc::Expr],
        view_ctx: &HashMap<String, ViewExpr>,
    ) -> ViewExpr {
        if let (
            desc::ArgKinded::Nat(s),
            desc::ArgKinded::Nat(n),
            desc::ArgKinded::Ty(ty),
            Some(v),
        ) = (&gen_args[0], &gen_args[1], &gen_args[2], args.first())
        {
            return ViewExpr::Group {
                size: s.clone(),
                n: n.clone(),
                ty: ty.clone(),
                view: Box::new(ViewExpr::create_from(v, view_ctx)),
            };
        }
        panic!("Cannot create `to_view` from the provided arguments.");
    }

    fn create_join_view(
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
            return ViewExpr::Join {
                m: m.clone(),
                n: n.clone(),
                ty: ty.clone(),
                view: Box::new(ViewExpr::create_from(v, view_ctx)),
            };
        }
        panic!("Cannot create `to_view` from the provided arguments.");
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
                ty: ty.clone(),
                view: Box::new(ViewExpr::create_from(v, view_ctx)),
            };
        }
        panic!("Cannot create `to_view` from the provided arguments.");
    }

    fn collect_pl_exprs(&self) -> Vec<desc::Expr> {
        fn collect_pl_exprs_rec(v: &ViewExpr, mut vec: Vec<desc::Expr>) -> Vec<desc::Expr> {
            match v {
                ViewExpr::ToView { pl_expr, .. } => {
                    vec.push(pl_expr.as_ref().clone());
                    vec
                }
                ViewExpr::Group { view, .. } => collect_pl_exprs_rec(view.as_ref(), vec),
                ViewExpr::Join { view, .. } => collect_pl_exprs_rec(view.as_ref(), vec),
                ViewExpr::Transpose { view, .. } => collect_pl_exprs_rec(view.as_ref(), vec),
                _ => unimplemented!(),
            }
        }
        let vec = vec![];
        collect_pl_exprs_rec(&self, vec)
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::ExprKind::GlobalFunIdent;
    use crate::codegen::gen_fun_def;

    #[test]
    fn scalar_mult_on_vec() {
        use crate::ast::*;
        let scalar_mult_fun = GlobalFunDef {
            name: "scalar_mult".to_string(),
            generic_params: vec![
                IdentKinded {
                    ident: Ident::new("a"),
                    kind: Kind::Provenance,
                },
                IdentKinded {
                    ident: Ident::new("n"),
                    kind: Kind::Nat,
                },
            ],
            params: vec![ParamDecl {
                ident: Ident::new("h_array"),
                ty: Ty::Ref(
                    Provenance::Ident(Ident::new("a")),
                    Ownership::Uniq,
                    Memory::CpuHeap,
                    Box::new(Ty::Array(
                        Box::new(Ty::Scalar(ScalarTy::I32)),
                        Nat::Ident(Ident::new("n")),
                    )),
                ),
                mutbl: Mutability::Const,
            }],
            ret_ty: Ty::Scalar(ScalarTy::Unit),
            exec: ExecLoc::CpuThread,
            prv_rels: vec![],
            body_expr: Expr {
                expr: ExprKind::LetProv(
                    vec!["a".to_string()],
                    Box::new(Expr {
                        expr: ExprKind::Let(
                            Mutability::Const,
                            Ident::new("gpu"),
                            Ty::Scalar(ScalarTy::Gpu),
                            Box::new(Expr {
                                expr: ExprKind::GlobalFunIdent("gpu".to_string()),
                                ty: Some(Ty::Scalar(ScalarTy::Gpu)),
                            }),
                            Box::new(Expr {
                                expr: ExprKind::Lit(Lit::Unit),
                                ty: Some(Ty::Scalar(ScalarTy::Unit)),
                            }),
                        ),
                        ty: Some(Ty::Scalar(ScalarTy::Unit)),
                    }),
                ),
                ty: Some(Ty::Scalar(ScalarTy::Unit)),
            },
        };

        let compil_unit: CompilUnit = vec![scalar_mult_fun];
        print!("{}", super::gen(&compil_unit));
    }
}
