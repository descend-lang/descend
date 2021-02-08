pub enum Item {
    FunDef {
        name: String,
        templ_params: Vec<TemplateParam>,
        params: Vec<ParamDecl>,
        ret_ty: Ty,
        body: Vec<Stmt>,
    },
}

pub struct Ident {
    name: String,
}

pub enum Stmt {
    VarDecl {
        name: String,
        expr: Option<Expr>,
    },
    Block(Vec<Stmt>),
    ExprStmt(Expr),
    If {
        cond: Expr,
        body: Vec<Stmt>,
    },
    IfElse {
        cond: Expr,
        true_body: Vec<Stmt>,
        false_body: Vec<Stmt>,
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
    Ident {
        name: String,
        prefix: String,
    },
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
    NonType { name: Ty },
    Type { name: String },
}

pub enum TemplateArg {
    Expr(Expr),
    Ty(Ty),
}

pub enum Ty {
    Int,
    Float,
    Double,
    Array {},
    Tuple,
    Ptr { elem_ty: Box<Ty> },
}
