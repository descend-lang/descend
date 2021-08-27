use super::cu_ast::{
    BinOp, BufferKind, Expr, Item, ParamDecl, ScalarTy, Stmt, TemplParam, TemplateArg, Ty, UnOp,
};
use crate::codegen::cu_ast::{GpuAddrSpace, Lit};
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
    clang_format(&code)
}

fn clang_format(code: &str) -> String {
    use std::process::{Command, Stdio};
    let mut echo_cmd = Command::new("echo")
        .arg(code)
        .stdout(Stdio::piped())
        .spawn()
        .expect("failed to execute `echo`");
    let echo_stdout = echo_cmd.stdout.take().expect("failed to open stdout");
    let clang_fmt_cmd = Command::new("clang-format")
        .stdin(echo_stdout)
        .stdout(Stdio::piped())
        .spawn()
        .expect("failed to execute `clang-format`");
    let clang_fmt_output = clang_fmt_cmd
        .wait_with_output()
        .expect("failed to execute `clang-format`");
    String::from_utf8(clang_fmt_output.stdout).expect("cannot read clang-format output as String")
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
                    "{}auto {}(",
                    if *is_dev_fun { "__device__ " } else { "" },
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
            VarDecl {
                name,
                ty,
                addr_space,
                expr,
            } => {
                //  if let Ty::Const(_) = ty {
                //      write!(f, "const ")?
                //  }
                //  write!(f, "auto {}", name)?;
                if let Some(addrs) = addr_space {
                    write!(f, "{} ", addrs)?;
                }
                write!(f, "{} {}", ty, name)?;
                if let Ty::CArray(_, n) = ty {
                    write!(f, "[{}]", n)?;
                }
                if let Some(expr) = expr {
                    write!(f, " = {}", expr)?;
                }
                write!(f, ";")
            }
            Block(stmt) => {
                writeln!(f, "{{")?;
                writeln!(f, "{}", stmt)?;
                write!(f, "}}")
            }
            Seq { check1, stmt1, check2, stmt2 } => {
                if !matches!(*check1.as_ref(), EmptyCheck) {
                    writeln!(f, "{}", check1)?;
                }
                writeln!(f, "{}", stmt1)?;
                if !matches!(*check2.as_ref(), EmptyCheck) {
                    writeln!(f, "{}", check2)?;
                }
                write!(f, "{}", stmt2)
            }
            Expr(expr) => {
                if let super::cu_ast::Expr::Empty = expr {
                    Ok(())
                } else {
                    write!(f, "{};", expr)
                }
            }
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
            While { cond, stmt } => {
                writeln!(f, "while ({})", cond)?;
                write!(f, "{}", stmt)
            }
            ForLoop {
                init,
                cond,
                iter,
                stmt,
            } => write!(f, "for ({} {}; {}) {}", init, cond, iter, stmt),
            EmptyCheck => {
                Ok(())
            }
            IndexCheck { arr, ind } => {
                writeln!(f,"if ({} < 0 && {}.size() > {}) {{", ind, arr, ind)?;
                writeln!(f,"\x2F\x2F out of bounds case")?;
                write!(f, "}}")
            }
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
            Empty => Ok(()),
            Ident(name) => write!(f, "{}", name),
            Lit(l) => write!(f, "{}", l),
            Assign {
                lhs: l_val,
                rhs: r_val,
            } => write!(f, "{} = {}", l_val, r_val),
            Lambda {
                params,
                body,
                ret_ty,
                is_dev_fun,
            } => {
                let dev_qual = if *is_dev_fun { "__device__" } else { "" };
                writeln!(f, "[] {} (", dev_qual)?;
                fmt_vec(f, &params, ",\n")?;
                writeln!(f, ") -> {} {{", ret_ty)?;
                writeln!(f, "{}", &body)?;
                write!(f, "}}")
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
                write!(f, "(")?;
                fmt_vec(f, args, ", ")?;
                write!(f, ")")
            }
            UnOp { op, arg } => write!(f, "{}{}", op, arg),
            BinOp { op, lhs, rhs } => write!(f, "{} {} {}", lhs, op, rhs),
            ArraySubscript { array, index } => write!(f, "{}[{}]", array, index),
            Proj { tuple, n } => write!(f, "{}.{}", tuple, n),
            InitializerList { elems } => {
                write!(f, "{{")?;
                fmt_vec(f, elems, ", ")?;
                write!(f, "}}")
            }
            Ref(expr) => write!(f, "&{}", expr),
            Deref(expr) => write!(f, "*{}", expr),
            Tuple(elems) => {
                write!(f, "descend::tuple{{")?;
                fmt_vec(f, elems, ", ")?;
                write!(f, "}}")
            }
            Nat(n) => write!(f, "{}", n),
        }
    }
}

impl std::fmt::Display for Lit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Lit::Void => Ok(()),
            Lit::Bool(b) => write!(f, "{}", b),
            Lit::I32(i) => write!(f, "{}", i),
            Lit::U32(u) => write!(f, "{}", u),
            Lit::F32(fl) => write!(f, "{}", fl),
        }
    }
}

impl std::fmt::Display for ParamDecl {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", self.ty, self.name)
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
            TemplParam::Value { param_name, ty } => write!(f, "{} {}", ty, param_name),
            TemplParam::TyName { name } => write!(f, "typename {}", name),
        }
    }
}

impl std::fmt::Display for UnOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Ref => write!(f, "&"),
            Self::Deref => write!(f, "*"),
            Self::Not => write!(f, "!"),
            Self::Neg => write!(f, "-"),
        }
    }
}

impl std::fmt::Display for BinOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::Mod => "%",
            Self::And => "&&",
            Self::Or => "||",
            Self::Eq => "=",
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Gt => ">",
            Self::Ge => ">=",
            Self::Neq => "!=",
        };
        write!(f, "{}", str)
    }
}

impl std::fmt::Display for GpuAddrSpace {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            GpuAddrSpace::Global => write!(f, ""),
            GpuAddrSpace::Shared => write!(f, "__shared__"),
            GpuAddrSpace::Constant => write!(f, "__constant__"),
        }
    }
}

impl std::fmt::Display for Ty {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Ty::*;
        match self {
            // TODO print __restrict__
            Ptr(ty, Some(addr_space)) => write!(f, "{} {} *", addr_space, ty),
            Ptr(ty, None) => write!(f, "{} *", ty),
            PtrConst(ty, Some(addr_space)) => write!(f, "{} const {} *", addr_space, ty),
            PtrConst(ty, None) => write!(f, "const {} *", ty),
            Const(ty) => match ty.as_ref() {
                Ptr(_, _) => write!(f, "{} const", ty),
                PtrConst(_, _) => write!(f, "{} const", ty),
                _ => write!(f, "const {}", ty),
            },
            Array(ty, size) => write!(f, "descend::array<{}, {}>", ty, size),
            // Does not print the entire type because that would be impossible since C arrays
            //  are declared by appending the size to a variable.
            CArray(ty, _) => write!(f, "{}", ty),
            Tuple(tys) => {
                write!(f, "descend::tuple<")?;
                fmt_vec(f, tys, ", ")?;
                write!(f, ">")
            }
            Buffer(ty, buff_kind) => match buff_kind {
                BufferKind::CpuHeap => write!(f, "HeapBuffer<{}>", ty),
                BufferKind::GpuGlobal => write!(f, "GpuBuffer<{}>", ty),
                BufferKind::Ident(name) => write!(f, "{}", name),
            },
            Scalar(sty) => write!(f, "{}", sty),
            Atomic(at) => write!(f, "{}", at),
            Ident(name) => write!(f, "{}", name),
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
            U32 => write!(f, "descend::u32"),
            F32 => write!(f, "descend::f32"),
            SizeT => write!(f, "std::size_t"),
            Bool => write!(f, "bool"),
            Memory => write!(f, "descend::Memory"),
            Gpu => write!(f, "descend::Gpu"),
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
            templ_params: vec![TemplParam::Value {
                param_name: "n".to_string(),
                ty: Scalar(ScalarTy::SizeT),
            }],
            params: vec![
                ParamDecl {
                    name: "a".to_string(),
                    ty: Const(Box::new(PtrConst(
                        Box::new(Scalar(ScalarTy::I32)),
                        Some(GpuAddrSpace::Shared),
                    ))),
                },
                ParamDecl {
                    name: "b".to_string(),
                    ty: Ptr(Box::new(Scalar(ScalarTy::I32)), None),
                },
            ],
            ret_ty: Scalar(ScalarTy::Void),
            body: Stmt::VarDecl {
                name: "a_f".to_string(),
                ty: Ty::Scalar(ScalarTy::Auto),
                addr_space: None,
                expr: Some(Expr::Ident("a".to_string())),
            },
            is_dev_fun: true,
        },
    ];
    let code = print(&program);
    print!("{}", code);
    Ok(())
}
