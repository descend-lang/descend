use crate::ast::Nat;

pub(super) enum Item<'a> {
    Include(String),
    FunDecl(&'a FnSig),
    FnDef(Box<FnDef>),
    MultiLineComment(String),
}

#[derive(Clone)]
pub(super) struct FnSig {
    pub(super) name: String,
    pub(super) templ_params: Vec<TemplParam>,
    pub(super) params: Vec<ParamDecl>,
    pub(super) ret_ty: Ty,
    pub(super) exec_kind: ExecKind,
}

impl FnSig {
    pub(super) fn new(
        name: String,
        templ_params: Vec<TemplParam>,
        params: Vec<ParamDecl>,
        ret_ty: Ty,
        exec_kind: ExecKind,
    ) -> Self {
        FnSig {
            name,
            templ_params,
            params,
            ret_ty,
            exec_kind,
        }
    }
}

#[derive(Clone)]
pub(super) enum ExecKind {
    Host,
    Global,
    Device,
}

#[derive(Clone)]
pub(super) struct FnDef {
    pub(super) fn_sig: FnSig,
    pub(super) body: Stmt,
}

impl FnDef {
    pub(super) fn new(fn_sig: FnSig, body: Stmt) -> Self {
        FnDef { fn_sig, body }
    }
}

#[derive(Clone, Debug)]
pub(super) struct ParamDecl {
    pub(super) name: String,
    pub(super) ty: Ty,
}

#[derive(Clone, Debug)]
pub(super) enum Stmt {
    Skip,
    VarDecl {
        name: String,
        ty: Ty,
        addr_space: Option<GpuAddrSpace>,
        expr: Option<Expr>,
        is_extern: bool,
    },
    Block(Box<Stmt>),
    Seq(Vec<Stmt>),
    Expr(Expr),
    If {
        cond: Expr,
        body: Box<Stmt>,
    },
    IfElse {
        cond: Expr,
        true_body: Box<Stmt>,
        false_body: Box<Stmt>,
    },
    While {
        cond: Expr,
        stmt: Box<Stmt>,
    },
    ForLoop {
        init: Box<Stmt>,
        cond: Expr,
        iter: Expr,
        stmt: Box<Stmt>,
    },
    Return(Option<Expr>),
    ExecKernel(Box<ExecKernel>),
}

#[derive(Clone, Debug)]
pub(super) struct ExecKernel {
    pub fun_name: String,
    pub template_args: Vec<TemplateArg>,
    pub grid_dim: Box<Expr>,
    pub block_dim: Box<Expr>,
    pub shared_mem_bytes: Box<Nat>,
    pub args: Vec<Expr>,
}

#[derive(Clone, Debug)]
pub(super) enum Expr {
    Empty,
    Ident(String),
    Lit(Lit),
    Assign {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Lambda {
        captures: Vec<crate::ast::Ident>,
        params: Vec<ParamDecl>,
        body: Box<Stmt>,
        ret_ty: Ty,
        is_dev_fun: bool,
    },
    FnCall(FnCall),
    UnOp {
        op: UnOp,
        arg: Box<Expr>,
    },
    BinOp {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    ArraySubscript {
        array: Box<Expr>,
        index: Nat,
    },
    Proj {
        tuple: Box<Expr>,
        n: usize,
    },
    InitializerList {
        elems: Vec<Expr>,
    },
    Ref(Box<Expr>),
    Deref(Box<Expr>),
    Tuple(Vec<Expr>),
    Cast(Ty, Box<Expr>),
    // The current plan for Nats is to simply print them with C syntax.
    // Instead generate a C/Cuda expression?
    Nat(Nat),
}

#[derive(Clone, Debug)]
pub(super) struct FnCall {
    pub fun: Box<Expr>,
    pub template_args: Vec<TemplateArg>,
    pub args: Vec<Expr>,
}

impl FnCall {
    pub fn new(fun: Expr, template_args: Vec<TemplateArg>, args: Vec<Expr>) -> Self {
        FnCall {
            fun: Box::new(fun),
            template_args,
            args,
        }
    }
}

#[derive(Clone, Debug)]
pub(super) enum Lit {
    Bool(bool),
    I32(i32),
    U32(u32),
    F32(f32),
    F64(f64),
}

#[derive(Clone, Debug)]
pub(super) enum UnOp {
    Not,
    Neg,
}

#[derive(Clone, Debug)]
pub(super) enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    And,
    Or,
    Eq,
    Lt,
    Le,
    Gt,
    Ge,
    Neq,
}

#[derive(Clone)]
pub(super) enum TemplParam {
    Value { param_name: String, ty: Ty },
    TyName { name: String },
}

#[derive(Clone, Debug)]
pub(super) enum TemplateArg {
    Expr(Expr),
    Ty(Ty),
}

#[derive(Clone, Debug)]
pub(super) enum GpuAddrSpace {
    // Device,
    Shared,
    // Constant,
}

#[derive(Clone, Debug)]
pub(super) enum Ty {
    Scalar(ScalarTy),
    Atomic(ScalarTy),
    Tuple(Vec<Ty>),
    Array(Box<Ty>, Nat),
    CArray(Box<Ty>, Option<Nat>),
    Buffer(Box<Ty>, BufferKind),
    // for now assume every pointer to be __restrict__ qualified
    // http://www.open-std.org/JTC1/SC22/WG14/www/docs/n1256.pdf#page=122&zoom=auto,-205,535
    Ptr(Box<Ty>),
    // The pointer itself is mutable, but the underlying data is not.
    PtrConst(Box<Ty>),
    // const in a parameter declaration changes the parameter type in a definition but not
    // "necessarily" the function signature ... https://abseil.io/tips/109
    // Top-level const
    Const(Box<Ty>),
    // Template parameter identifer
    Ident(String),
}

#[derive(Clone, Debug)]
pub(super) enum BufferKind {
    CpuMem,
    GpuGlobal,
    Ident(String),
}

#[derive(Clone, Debug)]
pub(super) enum ScalarTy {
    Auto,
    Void,
    Byte,
    U32,
    U64,
    I32,
    I64,
    F32,
    F64,
    Bool,
    SizeT,
    Memory,
    Gpu,
}
