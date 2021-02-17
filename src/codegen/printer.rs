use super::cu_ast::{
    BinOp, Expr, Item, ParamDecl, ScalarTy, Stmt, TemplParam, TemplateArg, Ty, UnOp,
};
use crate::codegen::cu_ast::Lit;
use std::fmt::Formatter;
use std::fmt::Write;

// function cuda_fmt takes Formatter and recursively formats
// trait CudaFormat has function cuda_fmt so that cuda_fmt_vec can be implemented (alias for fmt_vec)
// implement Display for CuAst by calling cuda_fmt in fmt passing the formatter and completely handing
// over the computation

pub(super) fn print(program: &[Item]) -> String {
    let mut code = String::new();
    for i in program {
        let res = writeln!(&mut code, "{}", i);
        if res.is_err() {
            panic!("{:?}", res);
        }
    }
    code
}

impl std::fmt::Display for Item {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Item::Include(path) => write!(f, "#include \"{}\"", path),
            Item::FunDef {
                name,
                templ_params,
                params,
                ret_ty,
                body,
                is_dev_fun,
            } => {
                if !templ_params.is_empty() {
                    write!(f, "template<")?;
                    fmt_vec(f, templ_params, ", ")?;
                    writeln!(f, ">")?;
                }
                writeln!(
                    f,
                    "{} auto {}(",
                    if *is_dev_fun { "__device__" } else { "" },
                    name
                )?;
                fmt_vec(f, params, ",\n")?;
                writeln!(f, "\n) -> {} {{", ret_ty)?;
                write!(f, "{}", body)?;
                writeln!(f, "\n}}")
            }
        }
    }
}

impl std::fmt::Display for Stmt {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Stmt::*;
        match self {
            VarDecl { name, ty, expr } => {
                if let Some(ty) = ty {
                    write!(f, "{} ", ty)?;
                } else {
                    write!(f, "auto ")?;
                }
                write!(f, "{}", name)?;
                if let Some(expr) = expr {
                    write!(f, " = {}", expr)?;
                }
                write!(f, ";")
            }
            Block(stmts) => {
                writeln!(f, "{{")?;
                fmt_vec(f, stmts, "\n")?;
                writeln!(f)?;
                writeln!(f, "}}")
            }
            Seq(stmts) => fmt_vec(f, stmts, ";\n"),
            Expr(expr) => write!(f, "{};", expr),
            If { cond, body } => {
                writeln!(f, "if ({})", cond)?;
                write!(f, "{}", body)
            }
            IfElse {
                cond,
                true_body,
                false_body,
            } => {
                write!(f, "if ({}) ", cond)?;
                write!(f, "{} else {}", true_body, false_body)
            }
            ForLoop {
                init,
                cond,
                iter,
                stmt,
            } => write!(f, "for ({}; {}; {}) {}", init, cond, iter, stmt),
            Return(expr) => {
                write!(f, "return")?;
                if let Some(e) = expr {
                    write!(f, " {}", e)?;
                }
                write!(f, ";")
            }
        }
    }
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Expr::*;
        match self {
            Ident(name) => write!(f, "{}", name),
            Lit(l) => write!(f, "{}", l),
            Assign {
                lhs: l_val,
                rhs: r_val,
            } => write!(f, "{} = {}", l_val, r_val),
            Lambda { params, body } => {
                writeln!(f, "[] __device__ (")?;
                fmt_vec(f, &params, ",\n")?;
                writeln!(f, ") {{")?;
                fmt_vec(f, &body, ",\n")?;
                writeln!(f, "\n}}")
            }
            FunCall {
                fun,
                template_args,
                args,
            } => {
                write!(f, "{}", fun)?;
                if !template_args.is_empty() {
                    write!(f, "<")?;
                    fmt_vec(f, template_args, ", ")?;
                    write!(f, ">")?;
                }
                write!(f, ".(")?;
                fmt_vec(f, args, ", ")?;
                write!(f, ")")
            }
            UnOp { op, arg } => write!(f, "{}{}", op, arg),
            BinOp { op, lhs, rhs } => write!(f, "{} {} {}", lhs, op, rhs),
            ArraySubscript { array, index } => write!(f, "{}[{}]", array, index),
            Proj { tuple, n } => write!(f, "{}.{}", tuple, n),
            Ref(expr) => write!(f, "&{}", expr),
            Deref(expr) => write!(f, "*{}", expr),
        }
    }
}

impl std::fmt::Display for Lit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Lit::Void => write!(f, "void"),
            Lit::Bool(b) => write!(f, "{}", b),
            Lit::I32(i) => write!(f, "{}", i),
            Lit::F32(fl) => write!(f, "{}", fl),
        }
    }
}

impl std::fmt::Display for ParamDecl {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.name, self.ty)
    }
}

impl std::fmt::Display for TemplateArg {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TemplateArg::Expr(expr) => write!(f, "{}", expr),
            TemplateArg::Ty(ty) => write!(f, "{}", ty),
        }
    }
}

impl std::fmt::Display for TemplParam {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TemplParam::NonType { param_name, ty } => write!(f, "{} {}", ty, param_name),
            TemplParam::Ty(ty_name) => write!(f, "typename {}", ty_name),
        }
    }
}

impl std::fmt::Display for UnOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            UnOp::Ref => write!(f, "&"),
            UnOp::DeRef => write!(f, "*"),
        }
    }
}

impl std::fmt::Display for BinOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            BinOp::Add => write!(f, "+"),
            BinOp::Mult => write!(f, "*"),
        }
    }
}

impl std::fmt::Display for Ty {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Ty::*;
        match self {
            Ptr(ty) => write!(f, "{} *", ty),
            ConstPtr(ty) => write!(f, "const {} *", ty),
            Const(ty) => match ty.as_ref() {
                Ptr(_) => write!(f, "{} const", ty),
                ConstPtr(_) => write!(f, "{} const", ty),
                _ => write!(f, "const {}", ty),
            },
            Array(ty, size) => write!(f, "descend::array<{}, {}>", ty, size),
            Tuple(tys) => {
                write!(f, "descend::tuple<")?;
                fmt_vec(f, tys, ", ")?;
                write!(f, ">")
            }
            Buffer(ty, buff_kind) => match buff_kind {
                super::cu_ast::BufferKind::Heap => write!(f, "HeapBuffer<{}>", ty),
                super::cu_ast::BufferKind::Gpu => write!(f, "GpuBuffer<{}>", ty),
            },
            Scalar(sty) => write!(f, "{}", sty),
        }
    }
}

impl std::fmt::Display for ScalarTy {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use ScalarTy::*;
        match self {
            Auto => write!(f, "auto"),
            Void => write!(f, "void"),
            I32 => write!(f, "descend::i32"),
            F32 => write!(f, "descend::f32"),
            SizeT => write!(f, "std::size_t"),
        }
    }
}

fn fmt_vec<D: std::fmt::Display>(f: &mut Formatter<'_>, v: &[D], sep: &str) -> std::fmt::Result {
    if let Some((last, leading)) = v.split_last() {
        for p in leading {
            write!(f, "{}{}", p, sep)?;
        }
        write!(f, "{}", last)
    } else {
        Ok(())
    }
}

#[test]
fn test_print_program() -> std::fmt::Result {
    use Ty::*;
    let program = vec![
        Item::Include("descend.cuh".to_string()),
        Item::FunDef {
            name: "test_fun".to_string(),
            templ_params: vec![TemplParam::NonType {
                param_name: "n".to_string(),
                ty: Scalar(ScalarTy::SizeT),
            }],
            params: vec![
                ParamDecl {
                    name: "a".to_string(),
                    ty: Const(Box::new(ConstPtr(Box::new(Scalar(ScalarTy::I32))))),
                },
                ParamDecl {
                    name: "b".to_string(),
                    ty: Ptr(Box::new(Scalar(ScalarTy::I32))),
                },
            ],
            ret_ty: Scalar(ScalarTy::Void),
            body: Stmt::Seq(vec![Stmt::VarDecl {
                name: "a_f".to_string(),
                ty: None,
                expr: Some(Expr::Ident("a".to_string())),
            }]),
            is_dev_fun: true,
        },
    ];
    let code = print(&program);
    print!("{}", code);
    Ok(())
}
