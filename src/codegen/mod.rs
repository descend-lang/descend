mod cu_ast;
pub mod printer;

// TODO proper access modifiers such that this is contained in codegen only

pub enum Item {
    Include(String),
    FunDef {
        name: String,
        templ_params: Vec<TemplateParam>,
        params: Vec<ParamDecl>,
        ret_ty: Ty,
        body: Vec<Stmt>,
    },
}

pub enum Stmt {
    VarDecl {
        name: String,
        ty: Option<Ty>,
        expr: Option<Expr>,
    },
    Block(Vec<Stmt>),
    ExprStmt(Expr),
    If {
        cond: Expr,
        body: Box<Stmt>,
    },
    IfElse {
        cond: Expr,
        true_body: Box<Stmt>,
        false_body: Box<Stmt>,
    },
    ForLoop {
        init: Box<Stmt>,
        cond: Expr,
        iter: Expr,
        stmt: Box<Stmt>,
    },
    Return(Option<Expr>),
}

pub struct ParamDecl {
    name: String,
    ty: Ty,
}

pub enum Expr {
    Ident(String),
    Literal, // TODO
    Assign {
        l_val: Box<Expr>,
        r_val: Box<Expr>,
    },
    DeviceLambda {
        params: Vec<ParamDecl>,
        body: Vec<Stmt>,
    },
    FunCall {
        fun: Box<Expr>,
        template_args: Vec<TemplateArg>,
        args: Vec<Expr>,
    },
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
        index: Box<Expr>,
    },
}

pub enum UnOp {
    Ref,
    DeRef,
}

pub enum BinOp {
    Add,
    Mult,
}

pub enum TemplateParam {
    NonType { param_name: String, ty: Ty },
    Ty(Ty),
}

pub enum TemplateArg {
    Expr(Expr),
    Ty(Ty),
}

pub enum Ty {
    // for now assume every pointer to be __restrict__ qualified
    // http://www.open-std.org/JTC1/SC22/WG14/www/docs/n1256.pdf#page=122&zoom=auto,-205,535
    Ptr(Box<Ty>),
    // The pointer itself is mutable, but the underlying data is not.
    ConstPtr(Box<Ty>),
    // TODO In C++ const is a type qualifier (as opposed to qualifying an identifier).
    //  However the way we generate code let's us treat const as an identifier qualifier (we would
    //  not return a const value from a function for example, but e.g., a non-const const pointer).
    //  Should the AST be changed to reflect this?
    // const in a parameter declaration changes the parameter type in a definition but not
    // "necessarily" the function signature ... https://abseil.io/tips/109
    // Top-level const
    Const(Box<Ty>),
    Array(Box<Ty>, usize),
    Tuple(Vec<Ty>),
    Buffer(Box<Ty>, BufferKind),
    Scalar(ScalarTy),
}

pub enum BufferKind {
    Heap,
    Gpu,
}

pub enum ScalarTy {
    Auto,
    Void,
    I32,
    F32,
    SizeT,
}
