use crate::arena_ast::Nat;

pub(super) enum Item<'a> {
    Include(String),
    FunDecl(&'a FnSig<'a>),
    FnDef(Box<FnDef<'a>>),
    MultiLineComment(String),
}

#[derive(Clone)]
pub(super) struct FnSig<'a> {
    pub(super) name: String,
    pub(super) templ_params: Vec<TemplParam<'a>>,
    pub(super) params: Vec<ParamDecl<'a>>,
    pub(super) ret_ty: Ty<'a>,
    pub(super) exec_kind: ExecKind,
}

impl<'a> FnSig<'a> {
    pub(super) fn new(
        name: String,
        templ_params: Vec<TemplParam<'a>>,
        params: Vec<ParamDecl<'a>>,
        ret_ty: Ty<'a>,
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
pub(super) struct FnDef<'a> {
    pub(super) fn_sig: FnSig<'a>,
    pub(super) body: Stmt<'a>,
}

impl<'a> FnDef<'a> {
    pub(super) fn new(fn_sig: FnSig<'a>, body: Stmt<'a>) -> Self {
        FnDef { fn_sig, body }
    }
}

#[derive(Clone, Debug)]
pub(super) struct ParamDecl<'a> {
    pub(super) name: String,
    pub(super) ty: Ty<'a>,
}

#[derive(Clone, Debug)]
pub(super) enum Stmt<'a> {
    Skip,
    VarDecl {
        name: String,
        ty: Ty<'a>,
        addr_space: Option<GpuAddrSpace>,
        expr: Option<Expr<'a>>,
        is_extern: bool,
    },
    Block(Box<Stmt<'a>>),
    Seq(Vec<Stmt<'a>>),
    Expr(Expr<'a>),
    If {
        cond: Expr<'a>,
        body: Box<Stmt<'a>>,
    },
    IfElse {
        cond: Expr<'a>,
        true_body: Box<Stmt<'a>>,
        false_body: Box<Stmt<'a>>,
    },
    While {
        cond: Expr<'a>,
        stmt: Box<Stmt<'a>>,
    },
    ForLoop {
        init: Box<Stmt<'a>>,
        cond: Expr<'a>,
        iter: Expr<'a>,
        stmt: Box<Stmt<'a>>,
    },
    Return(Option<Expr<'a>>),
    ExecKernel(Box<ExecKernel<'a>>),
}

#[derive(Clone, Debug)]
pub(super) struct ExecKernel<'a> {
    pub fun_name: String,
    pub template_args: Vec<TemplateArg<'a>>,
    pub grid_dim: Box<Expr<'a>>,
    pub block_dim: Box<Expr<'a>>,
    pub shared_mem_bytes: Box<Nat<'a>>,
    pub args: Vec<Expr<'a>>,
}

#[derive(Clone, Debug)]
pub(super) enum Expr<'a> {
    Empty,
    Ident(String),
    Lit(Lit),
    Assign {
        lhs: Box<Expr<'a>>,
        rhs: Box<Expr<'a>>,
    },
    Lambda {
        captures: Vec<crate::arena_ast::Ident<'a>>,
        params: Vec<ParamDecl<'a>>,
        body: Box<Stmt<'a>>,
        ret_ty: Ty<'a>,
        is_dev_fun: bool,
    },
    FnCall(FnCall<'a>),
    UnOp {
        op: UnOp,
        arg: Box<Expr<'a>>,
    },
    BinOp {
        op: BinOp,
        lhs: Box<Expr<'a>>,
        rhs: Box<Expr<'a>>,
    },
    Cast {
        expr: Box<Expr<'a>>,
        ty: Ty<'a>,
    },
    ArraySubscript {
        array: Box<Expr<'a>>,
        index: Nat<'a>,
    },
    Proj {
        tuple: Box<Expr<'a>>,
        n: usize,
    },
    FieldProj {
        struct_expr: Box<Expr<'a>>,
        field_name: String,
    },
    InitializerList {
        elems: Vec<Expr<'a>>,
    },
    AtomicRef {
        expr: Box<Expr<'a>>,
        base_ty: Ty<'a>,
    },
    Ref(Box<Expr<'a>>),
    Deref(Box<Expr<'a>>),
    Tuple(Vec<Expr<'a>>),
    // The current plan for Nats is to simply print them with C syntax.
    // Instead generate a C/Cuda expression?
    Nat(Nat<'a>),
}

#[derive(Clone, Debug)]
pub(super) struct FnCall<'a> {
    pub fun: Box<Expr<'a>>,
    pub template_args: Vec<TemplateArg<'a>>,
    pub args: Vec<Expr<'a>>,
}

impl<'a> FnCall<'a> {
    pub fn new(fun: Expr<'a>, template_args: Vec<TemplateArg<'a>>, args: Vec<Expr<'a>>) -> Self {
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
    U8(u8),
    U32(u32),
    U64(u64),
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
    Shl,
    Shr,
    BitOr,
    BitAnd,
}

#[derive(Clone)]
pub(super) enum TemplParam<'a> {
    Value { param_name: String, ty: Ty<'a> },
    TyName { name: String },
}

#[derive(Clone, Debug)]
pub(super) enum TemplateArg<'a> {
    Expr(Expr<'a>),
    Ty(Ty<'a>),
}

#[derive(Clone, Debug)]
pub(super) enum GpuAddrSpace {
    // Device,
    Shared,
    // Constant,
}

#[derive(Clone, Debug)]
pub(super) enum Ty<'a> {
    Scalar(ScalarTy),
    Tuple(Vec<Ty<'a>>),
    Array(Box<Ty<'a>>, Nat<'a>),
    CArray(Box<Ty<'a>>, Option<Nat<'a>>),
    Buffer(Box<Ty<'a>>, BufferKind),
    // for now assume every pointer to be __restrict__ qualified
    // http://www.open-std.org/JTC1/SC22/WG14/www/docs/n1256.pdf#page=122&zoom=auto,-205,535
    Ptr(Box<Ty<'a>>),
    // The pointer itself is mutable, but the underlying data is not.
    PtrConst(Box<Ty<'a>>),
    // const in a parameter declaration changes the parameter type in a definition but not
    // "necessarily" the function signature ... https://abseil.io/tips/109
    // Top-level const
    Const(Box<Ty<'a>>),
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
    U8,
    U32,
    U64,
    Byte,
    I32,
    I64,
    F32,
    F64,
    Bool,
    SizeT,
    Memory,
    Gpu,
    Warp,
}
