mod cu_ast;
mod printer;

use crate::ast as desc;
use crate::ast::PlaceExpr;
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

    let mut kind_ctx: HashMap<String, desc::Kind> = ty_idents
        .iter()
        .map(|desc::IdentKinded { ident, kind }| (ident.name.clone(), kind.clone()))
        .collect();

    cu::Item::FunDef {
        name: name.clone(),
        templ_params: gen_templ_params(ty_idents),
        params: gen_param_decls(params),
        ret_ty: gen_ty(ret_ty, desc::Mutability::Mut),
        body: gen_stmt(
            body_expr,
            !matches!(ret_ty, desc::Ty::Scalar(desc::ScalarTy::Unit)),
            &mut HashMap::new(),
            &mut kind_ctx,
        ),
        is_dev_fun: is_dev_fun(*exec),
    }
}

fn gen_stmt(
    expr: &desc::Expr,
    return_value: bool,
    view_ctx: &mut HashMap<String, ViewExpr>,
    kind_ctx: &mut HashMap<String, desc::Kind>,
) -> cu::Stmt {
    use desc::ExprKind::*;
    match &expr.expr {
        Let(mutbl, ident, _, e1, e2) => {
            // Let ArrayView
            if matches!(e1.ty.as_ref().unwrap(), desc::Ty::ArrayView(_, _)) {
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
                gen_stmt(e2, return_value, view_ctx, kind_ctx)
            // Let Expression
            } else {
                cu::Stmt::Seq(
                    Box::new(cu::Stmt::VarDecl {
                        name: ident.name.clone(),
                        ty: gen_ty(e1.ty.as_ref().unwrap(), *mutbl),
                        expr: Some(gen_expr(e1, view_ctx, kind_ctx)),
                    }),
                    Box::new(gen_stmt(e2, return_value, view_ctx, kind_ctx)),
                )
            }
        }
        LetProv(prv_idents, expr) => {
            let mut inner_kind_ctx = kind_ctx.clone();
            inner_kind_ctx.extend(
                prv_idents
                    .iter()
                    .map(|id| (id.clone(), desc::Kind::Provenance)),
            );
            gen_stmt(expr, return_value, view_ctx, &mut inner_kind_ctx)
        }
        // e1 ; e2
        Seq(e1, e2) => cu::Stmt::Seq(
            Box::new(gen_stmt(e1, false, view_ctx, kind_ctx)),
            Box::new(gen_stmt(e2, return_value, view_ctx, kind_ctx)),
        ),
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
                // TODO in body: substitute x for fitting expr including _i_?
                stmt: Box::new(gen_stmt(body, false, view_ctx, kind_ctx)),
            }
        }
        ParForSync(ident, view_expr, glb_cfg_expr, body) => {
            gen_par_for_sync(ident, view_expr, glb_cfg_expr, body, view_ctx, kind_ctx)
        }
        _ if return_value => cu::Stmt::Return(Some(gen_expr(&expr, view_ctx, kind_ctx))),
        _ => cu::Stmt::Expr(gen_expr(&expr, view_ctx, kind_ctx)),
    }
}

fn gen_par_for_sync(
    ident: &desc::Ident,
    view_expr: &desc::Expr,
    glb_cfg_expr: &desc::Expr,
    body: &desc::Expr,
    view_ctx: &mut HashMap<String, ViewExpr>,
    kind_ctx: &mut HashMap<String, desc::Kind>,
) -> cu::Stmt {
    let mut v = ViewExpr::create_from(view_expr, view_ctx);
    let name_to_pl_exprs = v.collect_and_rename_pl_exprs();
    let param_decls: Vec<_> = name_to_pl_exprs
        .iter()
        .map(|(name, pl_expr)| cu::ParamDecl {
            name: name.clone(),
            ty: gen_ty(pl_expr.ty.as_ref().unwrap(), desc::Mutability::Const),
        })
        .collect();
    let global_id = desc::Nat::BinOp(
        desc::BinOpNat::Add,
        Box::new(desc::Nat::BinOp(
            desc::BinOpNat::Mul,
            Box::new(desc::Nat::Ident(desc::Ident::new("blockIdx.x"))),
            Box::new(desc::Nat::Ident(desc::Ident::new("blockDim.x"))),
        )),
        Box::new(desc::Nat::Ident(desc::Ident::new("threadIdx.x"))),
    );
    let mut scope_view_ctx: HashMap<String, ViewExpr> = HashMap::new();
    let res = scope_view_ctx.insert(
        ident.name.clone(),
        ViewExpr::Idx {
            idx: global_id,
            view: Box::new(v),
        },
    );
    if res.is_some() {
        panic!(
            "Conflicting names. View variable `{}` used twice.",
            ident.name
        )
    }
    let glb_cfg = cu::Expr::Ref(Box::new(gen_expr(
        glb_cfg_expr,
        &mut HashMap::new(),
        kind_ctx,
    )));
    let loop_body = cu::Expr::Lambda {
        params: param_decls,
        body: Box::new(gen_stmt(body, false, &mut scope_view_ctx, kind_ctx)),
        ret_ty: cu::Ty::Scalar(cu::ScalarTy::Void),
        is_dev_fun: true,
    };
    let mut input: Vec<_> = name_to_pl_exprs
        .iter()
        .map(|(_, pl_expr)| gen_expr(pl_expr, &mut HashMap::new(), kind_ctx))
        .collect();
    let mut args: Vec<cu::Expr> = vec![glb_cfg, loop_body];
    args.append(&mut input);
    cu::Stmt::Expr(cu::Expr::FunCall {
        fun: Box::new(cu::Expr::Ident("descend::par_for".to_string())),
        template_args: vec![],
        args,
    })
}

fn gen_expr(
    expr: &desc::Expr,
    view_ctx: &mut HashMap<String, ViewExpr>,
    kind_ctx: &mut HashMap<String, desc::Kind>,
) -> cu::Expr {
    use desc::ExprKind::*;
    match &expr.expr {
        GlobalFunIdent(ident) => {
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
            lhs: Box::new(gen_expr(lhs, view_ctx, kind_ctx)),
            rhs: Box::new(gen_expr(rhs, view_ctx, kind_ctx)),
        },
        UnOp(op, arg) => cu::Expr::UnOp {
            op: match op {
                desc::UnOp::Deref => cu::UnOp::Deref,
                desc::UnOp::Not => cu::UnOp::Not,
                desc::UnOp::Neg => cu::UnOp::Neg,
            },
            arg: Box::new(gen_expr(arg, view_ctx, kind_ctx)),
        },
        Index(pl_expr, n) => cu::Expr::ArraySubscript {
            array: Box::new(gen_pl_expr(pl_expr, view_ctx)),
            index: n.clone(),
        },
        Ref(_, _, pl_expr) => cu::Expr::Ref(Box::new(gen_pl_expr(pl_expr, view_ctx))),
        BorrowIndex(_, _, pl_expr, n) => cu::Expr::Ref(Box::new(cu::Expr::ArraySubscript {
            array: Box::new(gen_pl_expr(pl_expr, view_ctx)),
            index: n.clone(),
        })),
        Assign(pl_expr, expr) => cu::Expr::Assign {
            lhs: Box::new(gen_pl_expr(pl_expr, view_ctx)),
            rhs: Box::new(gen_expr(expr, view_ctx, kind_ctx)),
        },
        Lambda(params, exec, ty, expr) => cu::Expr::Lambda {
            params: gen_param_decls(params.as_slice()),
            body: Box::new(gen_stmt(
                expr,
                !matches!(ty, desc::Ty::Scalar(desc::ScalarTy::Unit)),
                view_ctx,
                kind_ctx,
            )),
            ret_ty: gen_ty(ty, desc::Mutability::Mut),
            is_dev_fun: is_dev_fun(*exec),
        },
        App(fun, kinded_args, args) => cu::Expr::FunCall {
            fun: Box::new(gen_expr(fun, view_ctx, kind_ctx)),
            template_args: gen_args_kinded(kinded_args, &kind_ctx),
            args: args
                .iter()
                .map(|e| gen_expr(e, view_ctx, kind_ctx))
                .collect::<Vec<_>>(),
        },
        IfElse(cond, e_tt, e_ff) => unimplemented!(),
        Array(elems) => cu::Expr::FunCall {
            fun: Box::new(cu::Expr::Ident("descend::create_array".to_string())),
            template_args: vec![],
            args: elems
                .iter()
                .map(|e| gen_expr(e, view_ctx, kind_ctx))
                .collect::<Vec<_>>(),
        },
        Tuple(elems) => cu::Expr::Tuple(
            elems
                .iter()
                .map(|el| gen_expr(el, view_ctx, kind_ctx))
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
    match pl_expr {
        desc::PlaceExpr::Proj(pl, n) => cu::Expr::Proj {
            tuple: Box::new(gen_pl_expr(pl.as_ref(), view_ctx)),
            n: n.clone(),
        },
        desc::PlaceExpr::Deref(pl) => {
            // If an identifier that refers to an unwrapped view expression is being dereferenced,
            // just generate from the view expression and omit generating the dereferencing.
            // The dereferencing will happen through indexing.
            if let desc::PlaceExpr::Ident(ident) = pl.as_ref() {
                if view_ctx.contains_key(&ident.name) {
                    return gen_from_view(view_ctx.get(&ident.name).unwrap());
                }
            }
            cu::Expr::Deref(Box::new(gen_pl_expr(pl.as_ref(), view_ctx)))
        }
        desc::PlaceExpr::Ident(ident) => cu::Expr::Ident(ident.name.clone()),
    }
}

fn gen_from_view(view_expr: &ViewExpr) -> cu::Expr {
    match view_expr {
        ViewExpr::ToView { ref_expr, .. } => {
            gen_expr(ref_expr, &mut HashMap::new(), &mut HashMap::new())
        }
        ViewExpr::Idx { idx, view } => cu::Expr::ArraySubscript {
            array: Box::new(gen_from_view(view)),
            index: idx.clone(),
        },
        ViewExpr::Join { m, n, ty, view } => unimplemented!(),
        ViewExpr::Group { size, n, ty, view } => unimplemented!(),
        ViewExpr::Transpose { m, n, ty, view } => unimplemented!(),
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

fn gen_args_kinded(
    templ_args: &[desc::ArgKinded],
    ctx: &HashMap<String, desc::Kind>,
) -> Vec<cu::TemplateArg> {
    templ_args
        .iter()
        .filter_map(|ka| gen_arg_kinded(ka, ctx))
        .collect()
}

fn gen_arg_kinded(
    templ_arg: &desc::ArgKinded,
    ctx: &HashMap<String, desc::Kind>,
) -> Option<cu::TemplateArg> {
    match templ_arg {
        desc::ArgKinded::Ident(ident) => match ctx.get(&ident.name).unwrap() {
            desc::Kind::Ty => Some(cu::TemplateArg::Ty(cu::Ty::Ident(ident.name.clone()))),
            desc::Kind::Nat => Some(cu::TemplateArg::Expr(cu::Expr::Nat(desc::Nat::Ident(
                ident.clone(),
            )))),
            desc::Kind::Memory | desc::Kind::Provenance | desc::Kind::Frame | desc::Kind::Exec => {
                None
            }
        },
        desc::ArgKinded::Nat(n) => Some(cu::TemplateArg::Expr(cu::Expr::Nat(n.clone()))),
        desc::ArgKinded::Ty(ty) => Some(cu::TemplateArg::Ty(gen_ty(ty, desc::Mutability::Mut))),
        // cu::TemplateArg::Expr(cu::Expr::Ident(match mem {
        //     desc::Memory::Ident(ident) => panic!("TODO This variant should probably not exist."),
        //     desc::Memory::GpuGlobal => "Memory::GpuGlobal".to_string(),
        //     desc::Memory::GpuShared => unimplemented!("TODO!"),
        //     desc::Memory::CpuHeap => "Memory::CpuHeap".to_string(),
        //     desc::Memory::CpuStack => "Memory::CpuStack".to_string(),
        // })),
        desc::ArgKinded::Memory(_)
        | desc::ArgKinded::Exec(_)
        | desc::ArgKinded::Provenance(_)
        | desc::ArgKinded::Frame(_) => None,
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
            let tty = Box::new(gen_ty(
                match ty.as_ref() {
                    // Pointers to arrays point to the element type.
                    desc::Ty::Array(elem_ty, _) => elem_ty,
                    _ => ty,
                },
                m,
            ));
            if matches!(own, desc::Ownership::Uniq) {
                cu::Ty::Ptr(tty)
            } else {
                cu::Ty::PtrConst(tty)
            }
        }
        // TODO is this correct. I guess we want to generate type identifiers in generic functions.
        desc::Ty::Ident(ident) => cu::Ty::Ident(ident.name.clone()),
        desc::Ty::GridConfig(num_blocks, num_threads) => {
            cu::Ty::GridConfig(num_blocks.clone(), num_threads.clone())
        }
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

fn extract_size(ty: &desc::Ty) -> Option<desc::Nat> {
    match ty {
        desc::Ty::Array(_, n) => Some(n.clone()),
        _ => None,
    }
}

// Views are parsed as normal predeclared functions so that it is possible to infer types.
// During code generation view function applications are converted to View Variants and used
// to generate Indices.
#[derive(Debug, Clone)]
enum ViewExpr {
    ToView {
        // TODO are the nat and type needed?
        n: desc::Nat,
        ty: desc::Ty,
        ref_expr: Box<desc::Expr>,
    },
    Idx {
        idx: desc::Nat,
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
                if let desc::ExprKind::GlobalFunIdent(ident) = &f.expr {
                    if ident.name == crate::ty_check::pre_decl::TO_VIEW
                        || ident.name == crate::ty_check::pre_decl::TO_VIEW_MUT
                    {
                        ViewExpr::create_to_view_view(gen_args, args)
                    } else if ident.name == crate::ty_check::pre_decl::GROUP {
                        ViewExpr::create_group_view(gen_args, args, view_ctx)
                    } else if ident.name == crate::ty_check::pre_decl::JOIN {
                        ViewExpr::create_join_view(gen_args, args, view_ctx)
                    } else if ident.name == crate::ty_check::pre_decl::TRANSPOSE {
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
        if let (desc::ArgKinded::Nat(n), desc::ArgKinded::Ty(ty), Some(e)) =
            (&gen_args[2], &gen_args[3], args.first())
        {
            // e cannot contain views, so the view_ctx can be empty
            return ViewExpr::ToView {
                n: n.clone(),
                ty: ty.clone(),
                ref_expr: Box::new(e.clone()),
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

    fn collect_and_rename_pl_exprs(&mut self) -> Vec<(String, desc::Expr)> {
        fn collect_and_rename_pl_exprs_rec(
            v: &mut ViewExpr,
            count: &mut u32,
            mut vec: Vec<(String, desc::Expr)>,
        ) -> Vec<(String, desc::Expr)> {
            match v {
                ViewExpr::ToView {
                    ref_expr: pl_expr, ..
                } => {
                    let new_name = format!("p{}", *count);
                    vec.push((new_name.clone(), pl_expr.as_ref().clone()));
                    pl_expr.expr =
                        desc::ExprKind::PlaceExpr(PlaceExpr::Ident(desc::Ident::new(&new_name)));
                    *count = *count + 1;
                    vec
                }
                ViewExpr::Group { view, .. } => collect_and_rename_pl_exprs_rec(view, count, vec),
                ViewExpr::Join { view, .. } => collect_and_rename_pl_exprs_rec(view, count, vec),
                ViewExpr::Transpose { view, .. } => {
                    collect_and_rename_pl_exprs_rec(view, count, vec)
                }
                _ => unimplemented!(),
            }
        }
        let vec = vec![];
        let mut count = 0;
        collect_and_rename_pl_exprs_rec(self, &mut count, vec)
    }

    // fn substitute_pl_exprs(&mut self, expr_name_map: &[(PlaceExpr, String)]) -> {
    //     match self {
    //         ViewExpr::Idx { pl_expr, .. } =>
    //     }
    // }
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
