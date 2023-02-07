use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;

use descend_derive::span_derive;
pub use span::*;

use crate::ast::visit_mut::VisitMut;
use crate::parser::SourceCode;

pub mod internal;

mod span;
pub mod utils;
#[allow(dead_code)]
pub mod visit;
#[allow(dead_code)]
pub mod visit_mut;

#[derive(Clone, Debug)]
pub struct CompilUnit<'a> {
    pub fun_defs: Vec<FunDef>,
    pub source: &'a SourceCode<'a>,
}

impl<'a> CompilUnit<'a> {
    pub fn new(fun_defs: Vec<FunDef>, source: &'a SourceCode<'a>) -> Self {
        CompilUnit { fun_defs, source }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunDef {
    pub ident: Ident,
    pub generic_params: Vec<IdentKinded>,
    pub param_decls: Vec<ParamDecl>,
    pub ret_dty: DataTy,
    pub exec_decl: IdentExec,
    pub prv_rels: Vec<PrvRel>,
    pub body: Box<Block>,
}

impl FunDef {
    pub fn fn_ty(&self) -> FnTy {
        let param_tys: Vec<_> = self
            .param_decls
            .iter()
            .map(|p_decl| p_decl.ty.as_ref().unwrap().clone())
            .collect();
        FnTy {
            generics: self.generic_params.clone(),
            param_tys,
            exec_ty: self.exec_decl.ty.as_ref().clone(),
            ret_ty: Box::new(Ty::new(TyKind::Data(Box::new(self.ret_dty.clone())))),
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IdentExec {
    pub ident: Ident,
    pub ty: Box<ExecTy>,
}

impl IdentExec {
    pub fn new(ident: Ident, exec_ty: ExecTy) -> Self {
        IdentExec {
            ident,
            ty: Box::new(exec_ty),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParamDecl {
    pub ident: Ident,
    pub ty: Option<Ty>,
    pub mutbl: Mutability,
}

#[span_derive(PartialEq)]
#[derive(Debug, Clone)]
pub struct Expr {
    pub expr: ExprKind,
    pub ty: Option<Box<Ty>>,
    #[span_derive_ignore]
    pub span: Option<Span>,
}

impl Expr {
    pub fn new(expr: ExprKind) -> Expr {
        Expr {
            expr,
            ty: None,
            span: None,
        }
    }

    pub fn with_span(expr: ExprKind, span: Span) -> Expr {
        Expr {
            expr,
            ty: None,
            span: Some(span),
        }
    }

    pub fn with_type(expr: ExprKind, ty: Ty) -> Expr {
        Expr {
            expr,
            ty: Some(Box::new(ty)),
            span: None,
        }
    }

    pub fn subst_idents(&mut self, subst_map: &HashMap<&str, &Expr>) {
        fn pl_expr_contains_name_in<'a, I>(pl_expr: &PlaceExpr, mut idents: I) -> bool
        where
            I: Iterator<Item = &'a &'a str>,
        {
            match &pl_expr.pl_expr {
                PlaceExprKind::Ident(ident) => idents.any(|name| ident.name.as_ref() == *name),
                PlaceExprKind::Proj(tuple, _) => pl_expr_contains_name_in(tuple, idents),
                PlaceExprKind::Deref(deref) => pl_expr_contains_name_in(deref, idents),
            }
        }

        struct SubstIdents<'a> {
            subst_map: &'a HashMap<&'a str, &'a Expr>,
        }
        impl VisitMut for SubstIdents<'_> {
            fn visit_pl_expr(&mut self, pl_expr: &mut PlaceExpr) {
                if pl_expr_contains_name_in(pl_expr, self.subst_map.keys()) {
                    match &pl_expr.pl_expr {
                        PlaceExprKind::Ident(ident) => {
                            let subst_expr =
                                self.subst_map.get::<str>(ident.name.as_ref()).unwrap();
                            if let ExprKind::PlaceExpr(pl_e) = &subst_expr.expr {
                                *pl_expr = pl_e.as_ref().clone();
                            } else {
                                // TODO can this happen?
                                panic!("How did this happen?")
                            }
                        }
                        _ => visit_mut::walk_pl_expr(self, pl_expr),
                    }
                }
            }

            fn visit_expr(&mut self, expr: &mut Expr) {
                match &expr.expr {
                    ExprKind::PlaceExpr(pl_expr) => {
                        if pl_expr_contains_name_in(pl_expr, self.subst_map.keys()) {
                            match &pl_expr.pl_expr {
                                PlaceExprKind::Ident(ident) => {
                                    if let Some(&subst_expr) =
                                        self.subst_map.get::<str>(ident.name.as_ref())
                                    {
                                        *expr = subst_expr.clone();
                                    }
                                }
                                PlaceExprKind::Proj(tuple, i) => {
                                    let mut tuple_expr = Expr::new(ExprKind::PlaceExpr(Box::new(
                                        tuple.as_ref().clone(),
                                    )));
                                    self.visit_expr(&mut tuple_expr);
                                    *expr = Expr::new(ExprKind::Proj(Box::new(tuple_expr), *i));
                                }
                                PlaceExprKind::Deref(deref_expr) => {
                                    let mut ref_expr = Expr::new(ExprKind::PlaceExpr(Box::new(
                                        deref_expr.as_ref().clone(),
                                    )));
                                    self.visit_expr(&mut ref_expr);
                                    *expr = Expr::new(ExprKind::Deref(Box::new(ref_expr)));
                                }
                            }
                        }
                    }
                    _ => visit_mut::walk_expr(self, expr),
                }
            }
        }
        let mut subst_idents = SubstIdents { subst_map };
        subst_idents.visit_expr(self);
    }

    pub fn subst_ident(&mut self, ident: &str, subst_expr: &Expr) {
        let mut subst_map = HashMap::with_capacity(1);
        subst_map.insert(ident, subst_expr);
        self.subst_idents(&subst_map);
    }

    pub fn subst_kinded_idents(&mut self, subst_map: &HashMap<&str, &ArgKinded>) {
        struct SubstKindedIdents<'a> {
            subst_map: &'a HashMap<&'a str, &'a ArgKinded>,
        }
        impl VisitMut for SubstKindedIdents<'_> {
            fn visit_nat(&mut self, nat: &mut Nat) {
                match nat {
                    Nat::Ident(ident) => {
                        if let Some(ArgKinded::Nat(nat_arg)) =
                            self.subst_map.get::<str>(ident.name.as_ref())
                        {
                            *nat = nat_arg.clone()
                        }
                    }
                    _ => visit_mut::walk_nat(self, nat),
                }
            }

            fn visit_mem(&mut self, mem: &mut Memory) {
                match mem {
                    Memory::Ident(ident) => {
                        if let Some(ArgKinded::Memory(mem_arg)) =
                            self.subst_map.get::<str>(ident.name.as_ref())
                        {
                            *mem = mem_arg.clone()
                        }
                    }
                    _ => visit_mut::walk_mem(self, mem),
                }
            }

            fn visit_prv(&mut self, prv: &mut Provenance) {
                match prv {
                    Provenance::Ident(ident) => {
                        if let Some(ArgKinded::Provenance(prv_arg)) =
                            self.subst_map.get::<str>(ident.name.as_ref())
                        {
                            *prv = prv_arg.clone()
                        }
                    }
                    _ => visit_mut::walk_prv(self, prv),
                }
            }

            fn visit_dty(&mut self, dty: &mut DataTy) {
                match &mut dty.dty {
                    DataTyKind::Ident(ident) => {
                        if let Some(ArgKinded::DataTy(dty_arg)) =
                            self.subst_map.get::<str>(ident.name.as_ref())
                        {
                            *dty = dty_arg.clone()
                        }
                    }
                    _ => visit_mut::walk_dty(self, dty),
                }
            }
        }

        let mut subst_kinded_idents = SubstKindedIdents { subst_map };
        subst_kinded_idents.visit_expr(self)
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct Sched {
    pub dim: DimCompo,
    pub inner_exec_ident: Option<Ident>,
    pub sched_exec: Ident,
    pub body: Box<Block>,
}

impl Sched {
    pub fn new(
        dim: DimCompo,
        inner_exec_ident: Option<Ident>,
        sched_exec: Ident,
        body: Block,
    ) -> Self {
        Sched {
            dim,
            inner_exec_ident,
            sched_exec,
            body: Box::new(body),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct ExprSplit {
    pub lrgn: Option<String>,
    pub rrgn: Option<String>,
    pub own: Ownership,
    pub pos: Nat,
    pub view: Box<PlaceExpr>,
}

impl ExprSplit {
    pub fn new(
        lrgn: Option<String>,
        rrgn: Option<String>,
        own: Ownership,
        pos: Nat,
        view: PlaceExpr,
    ) -> Self {
        ExprSplit {
            lrgn,
            rrgn,
            own,
            pos,
            view: Box::new(view),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct Indep {
    pub dim_compo: DimCompo,
    pub pos: Nat,
    pub split_exec_ident: Ident,
    pub branch_idents: Vec<Ident>,
    pub branch_bodies: Vec<Expr>,
}

impl Indep {
    pub fn new(
        dim_compo: DimCompo,
        pos: Nat,
        split_exec_ident: Ident,
        branch_idents: Vec<Ident>,
        branch_bodies: Vec<Expr>,
    ) -> Self {
        Indep {
            dim_compo,
            pos,
            split_exec_ident,
            branch_idents,
            branch_bodies,
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct Block {
    pub prvs: Vec<String>,
    pub body: Box<Expr>,
}

impl Block {
    pub fn new(body: Expr) -> Self {
        Block {
            prvs: vec![],
            body: Box::new(body),
        }
    }

    pub fn with_prvs(prvs: Vec<String>, body: Expr) -> Self {
        Block {
            prvs,
            body: Box::new(body),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct AppKernel {
    pub grid_dim: Dim,
    pub block_dim: Dim,
    pub shared_mem_dtys: Vec<DataTy>,
    pub shared_mem_prvs: Vec<String>,
    pub fun: Box<Expr>,
    pub gen_args: Vec<ArgKinded>,
    pub args: Vec<Expr>,
}

#[derive(PartialEq, Debug, Clone)]
pub enum ExprKind {
    Lit(Lit),
    // An l-value equivalent: *p, p.n, x
    PlaceExpr(Box<PlaceExpr>),
    // Index into array, e.g., arr[i]
    Index(Box<PlaceExpr>, Nat),
    // Projection, e.g. e.1, for non place expressions, e.g. f(x).1
    Proj(Box<Expr>, usize),
    // e.g., [1, 2 + 3, 4]
    Array(Vec<Expr>),
    Tuple(Vec<Expr>),
    // Borrow Expressions
    Ref(Option<String>, Ownership, Box<PlaceExpr>),
    BorrowIndex(Option<String>, Ownership, Box<PlaceExpr>, Nat),
    Block(Block),
    // Variable declaration
    // let mut x: ty;
    LetUninit(Ident, Box<Ty>),
    // Variable declaration, assignment and sequencing
    // let w x: ty = e1
    Let(Pattern, Option<Box<Ty>>, Box<Expr>),
    // Assignment to existing place [expression]
    Assign(Box<PlaceExpr>, Box<Expr>),
    // e1[i] = e2
    IdxAssign(Box<PlaceExpr>, Nat, Box<Expr>),
    // e1 ; e2
    Seq(Vec<Expr>),
    // Anonymous function which can capture its surrounding context
    // | x_n: d_1, ..., x_n: d_n | [exec]-> d_r { e }
    // TODO body expression should always be block?! No but treated like one.
    Lambda(Vec<ParamDecl>, IdentExec, Box<DataTy>, Box<Expr>),
    // Function application
    // e_f(e_1, ..., e_n)
    App(Box<Expr>, Vec<ArgKinded>, Vec<Expr>),
    // TODO remove
    DepApp(Box<Expr>, Vec<ArgKinded>),
    AppKernel(Box<AppKernel>),
    // TODO branches must be blocks
    IfElse(Box<Expr>, Box<Expr>, Box<Expr>),
    // TODO branch must be block
    If(Box<Expr>, Box<Expr>),
    // For-each loop.
    // for x in e_1 { e_2 }
    // TODO body must be block
    For(Ident, Box<Expr>, Box<Expr>),
    // for n in range(..) { e }
    // TODO body must be block
    ForNat(Ident, Nat, Box<Expr>),
    // while( e_1 ) { e_2 }
    // TODO body must be block
    While(Box<Expr>, Box<Expr>),
    BinOp(BinOp, Box<Expr>, Box<Expr>),
    UnOp(UnOp, Box<Expr>),
    // TODO branches must be blocks or treated like blocks
    Indep(Box<Indep>),
    Sched(Box<Sched>),
    Select(Option<String>, Box<PlaceExpr>, Box<Ident>),
    Split(Box<ExprSplit>),
    Sync,
    Range(Box<Expr>, Box<Expr>),
    // Deref a non place expression; ONLY for codegen
    Deref(Box<Expr>),
    // Index into an array; ONLY for codegen
    Idx(Box<Expr>, Nat),
}

#[span_derive(PartialEq, Eq, Hash)]
#[derive(Clone, Debug)]
pub struct Ident {
    // Identifier names never change. Instead a new identifier is created. Therefore it is not
    // necessary to keep the capacity that is stored in a String for efficient appending.
    pub name: Box<str>,
    #[span_derive_ignore]
    pub span: Option<Span>,
    pub is_implicit: bool,
}

impl Ident {
    pub fn new(name: &str) -> Self {
        Self {
            name: Box::from(name),
            span: None,
            is_implicit: false,
        }
    }

    pub fn new_impli(name: &str) -> Self {
        Self {
            name: Box::from(name),
            span: None,
            is_implicit: true,
        }
    }

    pub fn with_span(name: &str, span: Span) -> Self {
        Self {
            name: Box::from(name),
            span: Some(span),
            is_implicit: false,
        }
    }
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    Ident(Mutability, Ident),
    Tuple(Vec<Pattern>),
    Wildcard,
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Lit {
    Unit,
    Bool(bool),
    I32(i32),
    U32(u32),
    F32(f32),
    F64(f64),
}

// impl PartialEq for Lit{
//     fn eq(&self, other:&Self) -> bool {
//         let b = match (self, other) {
//             (Self::Unit, Self::Unit) => true,
//             (Self::Bool(x), Self::Bool(y)) => if x == y {true} else {false},
//             (Self::Int(x), Self::Int(y)) => if x == y {true} else {false},
//             (Self::Float(x), Self::Float(y)) => if x == y {true} else {false},
//             _ => false
//         };
//         b
//     }
// }

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Unit => write!(f, "()"),
            Self::Bool(b) => write!(f, "{}", b),
            Self::I32(i) => write!(f, "{}", i),
            Self::U32(u) => write!(f, "{}", u),
            Self::F32(fl) => write!(f, "{}f", fl),
            Self::F64(d) => write!(f, "{}", d),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Mutability {
    Const,
    Mut,
}

impl fmt::Display for Mutability {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let str = match self {
            Self::Const => "const",
            Self::Mut => "mut",
        };
        write!(f, "{}", str)
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Copy, Clone)]
pub enum Ownership {
    Shrd,
    Uniq,
}

impl fmt::Display for Ownership {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let str = match self {
            Self::Shrd => "shrd",
            Self::Uniq => "uniq",
        };
        write!(f, "{}", str)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum UnOp {
    Not,
    Neg,
}

impl fmt::Display for UnOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let str = match self {
            Self::Not => "!",
            Self::Neg => "-",
        };
        write!(f, "{}", str)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum BinOp {
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

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
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

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub enum Kind {
    Nat,
    Memory,
    DataTy,
    Provenance,
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let str = match self {
            Kind::Nat => "nat",
            Kind::Memory => "mem",
            Kind::DataTy => "dty",
            Kind::Provenance => "prv",
        };
        write!(f, "{}", str)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArgKinded {
    Ident(Ident),
    Nat(Nat),
    Memory(Memory),
    DataTy(DataTy),
    Provenance(Provenance),
}

impl ArgKinded {
    pub fn kind(&self) -> Kind {
        match self {
            ArgKinded::Ident(_) => {
                panic!("Unexpected: unkinded identifier should have been removed after parsing")
            }
            ArgKinded::DataTy(_) => Kind::DataTy,
            ArgKinded::Provenance(_) => Kind::Provenance,
            ArgKinded::Memory(_) => Kind::Memory,
            ArgKinded::Nat(_) => Kind::Nat,
        }
    }
}

#[span_derive(PartialEq, Eq, Hash)]
#[derive(Debug, Clone)]
pub struct PlaceExpr {
    pub pl_expr: PlaceExprKind,
    pub ty: Option<Box<Ty>>,
    // for borrow checking
    pub split_tag_path: Vec<SplitTag>,
    #[span_derive_ignore]
    pub span: Option<Span>,
}

#[derive(PartialEq, Eq, Hash, Debug, Copy, Clone)]
pub enum SplitTag {
    Fst,
    Snd,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum PlaceExprKind {
    Proj(Box<PlaceExpr>, usize),
    Deref(Box<PlaceExpr>),
    Ident(Ident),
}

impl PlaceExpr {
    pub fn new(pl_expr: PlaceExprKind) -> Self {
        PlaceExpr {
            pl_expr,
            ty: None,
            split_tag_path: vec![],
            span: None,
        }
    }

    pub fn with_span(pl_expr: PlaceExprKind, span: Span) -> Self {
        PlaceExpr {
            pl_expr,
            ty: None,
            split_tag_path: vec![],
            span: Some(span),
        }
    }

    pub fn is_place(&self) -> bool {
        match &self.pl_expr {
            PlaceExprKind::Proj(ple, _) => ple.is_place(),
            PlaceExprKind::Ident(_) => true,
            PlaceExprKind::Deref(_) => false,
        }
    }

    // The inner constructs are prefixes of the outer constructs.
    pub fn prefix_of(&self, other: &Self) -> bool {
        if self != other {
            match &other.pl_expr {
                PlaceExprKind::Proj(pl_expr, _) => self.prefix_of(pl_expr),
                PlaceExprKind::Deref(pl_expr) => self.prefix_of(pl_expr),
                PlaceExprKind::Ident(_) => false,
            }
        } else {
            true
        }
    }

    // TODO refactor. Places are only needed during typechecking and codegen
    pub fn to_place(&self) -> Option<internal::Place> {
        if self.is_place() {
            Some(self.to_pl_ctx_and_most_specif_pl().1)
        } else {
            None
        }
    }

    // TODO refactor see to_place
    pub fn to_pl_ctx_and_most_specif_pl(&self) -> (internal::PlaceCtx, internal::Place) {
        match &self.pl_expr {
            PlaceExprKind::Deref(inner_ple) => {
                let (pl_ctx, pl) = inner_ple.to_pl_ctx_and_most_specif_pl();
                (internal::PlaceCtx::Deref(Box::new(pl_ctx)), pl)
            }
            PlaceExprKind::Proj(inner_ple, n) => {
                let (pl_ctx, mut pl) = inner_ple.to_pl_ctx_and_most_specif_pl();
                match pl_ctx {
                    internal::PlaceCtx::Hole => {
                        pl.path.push(*n);
                        (pl_ctx, internal::Place::new(pl.ident, pl.path))
                    }
                    _ => (internal::PlaceCtx::Proj(Box::new(pl_ctx), *n), pl),
                }
            }
            PlaceExprKind::Ident(ident) => (
                internal::PlaceCtx::Hole,
                internal::Place::new(ident.clone(), vec![]),
            ),
        }
    }

    pub fn equiv(&'_ self, place: &'_ internal::Place) -> bool {
        if let (internal::PlaceCtx::Hole, pl) = self.to_pl_ctx_and_most_specif_pl() {
            &pl == place
        } else {
            false
        }
    }
}

impl fmt::Display for PlaceExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.pl_expr {
            PlaceExprKind::Proj(pl_expr, n) => write!(f, "{}.{}", pl_expr, n),
            PlaceExprKind::Deref(pl_expr) => write!(f, "*{}", pl_expr),
            PlaceExprKind::Ident(ident) => write!(f, "{}", ident),
        }
    }
}

#[span_derive(PartialEq, Eq, Hash)]
#[derive(Debug, Clone)]
pub struct ExecExpr {
    pub exec: Box<Exec>,
    pub ty: Option<Box<ExecTy>>,
    #[span_derive_ignore]
    pub span: Option<Span>,
}

impl ExecExpr {
    pub fn new(exec: Exec) -> Self {
        ExecExpr {
            exec: Box::new(exec),
            ty: None,
            span: None,
        }
    }

    pub fn is_sub_exec_of(&self, exec: &ExecExpr) -> bool {
        if self.exec.base == exec.exec.base {
            if self.exec.path.len() < exec.exec.path.len() {
                return false;
            }

            for (l, r) in self.exec.path.iter().zip(&exec.exec.path) {
                if l != r {
                    return false;
                }
            }
            true
        } else {
            false
        }
    }
}

impl fmt::Display for ExecExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.exec)
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct SplitProj {
    pub split_dim: DimCompo,
    pub pos: Nat,
    pub proj: u8,
}

impl SplitProj {
    pub fn new(split_dim: DimCompo, pos: Nat, proj: u8) -> Self {
        SplitProj {
            split_dim,
            pos,
            proj,
        }
    }
}

impl fmt::Display for SplitProj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "split({}, {}).{}", self.split_dim, self.pos, self.proj)
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct Exec {
    pub base: BaseExec,
    pub path: Vec<ExecPathElem>,
}

impl Exec {
    pub fn new(base: BaseExec) -> Self {
        Exec { base, path: vec![] }
    }
    //
    // pub fn with_path(base: BaseExec, path: Vec<ExecPathElem>) -> Self {
    //     Exec { base, path }
    // }
    //
    // pub fn append(mut self, path: Vec<ExecPathElem>) -> Self {
    //     self.path.append(&mut path);
    //     self
    // }

    pub fn split_proj(mut self, dim_compo: DimCompo, pos: Nat, proj: u8) -> Self {
        self.path
            .push(ExecPathElem::SplitProj(Box::new(SplitProj::new(
                dim_compo, pos, proj,
            ))));
        self
    }

    pub fn distrib(mut self, dim_compo: DimCompo) -> Self {
        self.path.push(ExecPathElem::Distrib(dim_compo));
        self
    }

    pub fn active_distrib_dim(&self) -> Option<DimCompo> {
        for e in self.path.iter().rev() {
            if let ExecPathElem::Distrib(dim) = e {
                return Some(*dim);
            }
        }
        None
    }
}

impl fmt::Display for Exec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.base)?;
        for e in &self.path {
            write!(f, ".{}", e)?;
        }
        Ok(())
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum BaseExec {
    Ident(Ident),
    CpuThread,
    GpuGrid(Dim, Dim),
}

impl fmt::Display for BaseExec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ident(ident) => write!(f, "{}", ident),
            Self::CpuThread => write!(f, "cpu.thread"),
            Self::GpuGrid(gsize, bsize) => write!(f, "gpu.grid<{}, {}>", gsize, bsize),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum ExecPathElem {
    SplitProj(Box<SplitProj>),
    Distrib(DimCompo),
    ToThreads(DimCompo),
}

impl fmt::Display for ExecPathElem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SplitProj(split_proj) => write!(
                f,
                "split_proj_{}({}, {})",
                split_proj.proj, split_proj.split_dim, split_proj.pos
            ),
            Self::Distrib(dim_compo) => write!(f, "distrib({})", dim_compo),
            Self::ToThreads(dim_compo) => write!(f, "to_threads({})", dim_compo),
        }
    }
}

#[span_derive(PartialEq, Eq, Hash)]
#[derive(Debug, Clone)]
pub struct Ty {
    pub ty: TyKind,
    #[span_derive_ignore]
    pub span: Option<Span>,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct FnTy {
    pub generics: Vec<IdentKinded>,
    pub param_tys: Vec<Ty>,
    pub exec_ty: ExecTy,
    pub ret_ty: Box<Ty>,
}

impl FnTy {
    pub fn new(
        generics: Vec<IdentKinded>,
        param_tys: Vec<Ty>,
        exec_ty: ExecTy,
        ret_ty: Ty,
    ) -> Self {
        FnTy {
            generics,
            param_tys,
            exec_ty,
            ret_ty: Box::new(ret_ty),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum TyKind {
    Data(Box<DataTy>),
    // <x:k,..>(ty..) -[x:exec]-> ty
    FnTy(Box<FnTy>),
}

// TODO remove
#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub enum Constraint {
    Copyable,
}

impl Ty {
    pub fn new(ty: TyKind) -> Self {
        Ty { ty, span: None }
    }

    pub fn with_span(ty: TyKind, span: Span) -> Ty {
        Ty {
            ty,
            span: Some(span),
        }
    }

    pub fn dty(&self) -> &DataTy {
        match &self.ty {
            TyKind::Data(dty) => dty,
            _ => panic!("Expected data type but found {:?}", self),
        }
    }

    pub fn dty_mut(&mut self) -> &mut DataTy {
        if !matches!(&mut self.ty, TyKind::Data(_)) {
            panic!("Expected data type but found {:?}", self)
        }
        if let TyKind::Data(dty) = &mut self.ty {
            dty
        } else {
            panic!("cannot reach")
        }
    }

    pub fn copyable(&self) -> bool {
        match &self.ty {
            TyKind::Data(dty) => dty.copyable(),
            TyKind::FnTy(_) => true,
        }
    }

    pub fn is_fully_alive(&self) -> bool {
        match &self.ty {
            TyKind::Data(dty) => dty.is_fully_alive(),
            TyKind::FnTy(_) => true,
        }
    }

    pub fn contains_ref_to_prv(&self, prv_val_name: &str) -> bool {
        match &self.ty {
            TyKind::Data(dty) => dty.contains_ref_to_prv(prv_val_name),
            TyKind::FnTy(fn_ty) => {
                fn_ty
                    .param_tys
                    .iter()
                    .any(|param_ty| param_ty.contains_ref_to_prv(prv_val_name))
                    || fn_ty.ret_ty.contains_ref_to_prv(prv_val_name)
            }
        }
    }

    pub fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Self {
        match &self.ty {
            // TODO mutate and do not create a new type (also this drops the span).
            TyKind::Data(dty) => Ty::new(TyKind::Data(Box::new(
                dty.subst_ident_kinded(ident_kinded, with),
            ))),
            TyKind::FnTy(fn_ty) => Ty::new(TyKind::FnTy(Box::new(FnTy::new(
                fn_ty.generics.clone(),
                fn_ty
                    .param_tys
                    .iter()
                    .map(|param| param.subst_ident_kinded(ident_kinded, with))
                    .collect(),
                fn_ty.exec_ty.clone(),
                fn_ty.ret_ty.subst_ident_kinded(ident_kinded, with),
            )))),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct Dim1d(pub Nat);
impl Dim1d {
    pub fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Self {
        Dim1d(self.0.subst_ident_kinded(ident_kinded, with))
    }
}
#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct Dim2d(pub Nat, pub Nat);
impl Dim2d {
    pub fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Self {
        Dim2d(
            self.0.subst_ident_kinded(ident_kinded, with),
            self.1.subst_ident_kinded(ident_kinded, with),
        )
    }
}
#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct Dim3d(pub Nat, pub Nat, pub Nat);
impl Dim3d {
    pub fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Self {
        Dim3d(
            self.0.subst_ident_kinded(ident_kinded, with),
            self.1.subst_ident_kinded(ident_kinded, with),
            self.2.subst_ident_kinded(ident_kinded, with),
        )
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum Dim {
    XYZ(Box<Dim3d>),
    XY(Box<Dim2d>),
    XZ(Box<Dim2d>),
    YZ(Box<Dim2d>),
    X(Box<Dim1d>),
    Y(Box<Dim1d>),
    Z(Box<Dim1d>),
}

impl Dim {
    pub fn new_3d(n1: Nat, n2: Nat, n3: Nat) -> Self {
        Dim::XYZ(Box::new(Dim3d(n1, n2, n3)))
    }

    pub fn new_2d<F: Fn(Box<Dim2d>) -> Self>(constr: F, n1: Nat, n2: Nat) -> Self {
        constr(Box::new(Dim2d(n1, n2)))
    }
    pub fn new_1d<F: Fn(Box<Dim1d>) -> Self>(constr: F, n: Nat) -> Self {
        constr(Box::new(Dim1d(n)))
    }

    pub fn proj_size(&self, dim_compo: DimCompo) -> Nat {
        match (dim_compo, self) {
            (DimCompo::X, Dim::XYZ(dim3d)) => dim3d.0.clone(),
            (DimCompo::X, Dim::XY(dim2d) | Dim::XZ(dim2d)) => dim2d.0.clone(),
            (DimCompo::X, Dim::X(dim1d)) => dim1d.0.clone(),
            (DimCompo::Y, Dim::XYZ(dim3d)) => dim3d.1.clone(),
            (DimCompo::Y, Dim::XY(dim2d)) => dim2d.1.clone(),
            (DimCompo::Y, Dim::YZ(dim2d)) => dim2d.0.clone(),
            (DimCompo::Y, Dim::Y(dim1d)) => dim1d.0.clone(),
            (DimCompo::Z, Dim::XYZ(dim3d)) => dim3d.2.clone(),
            (DimCompo::Z, Dim::XZ(dim2d) | Dim::YZ(dim2d)) => dim2d.1.clone(),
            (DimCompo::Z, Dim::Z(dim1d)) => dim1d.0.clone(),
            _ => panic!("Attempting to project size for a dimension that does not exist."),
        }
    }

    pub fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Self {
        use Dim::*;
        match self {
            XYZ(dim3d) => XYZ(Box::new(dim3d.subst_ident_kinded(ident_kinded, with))),
            XY(dim2d) => XY(Box::new(dim2d.subst_ident_kinded(ident_kinded, with))),
            XZ(dim2d) => XZ(Box::new(dim2d.subst_ident_kinded(ident_kinded, with))),
            YZ(dim2d) => YZ(Box::new(dim2d.subst_ident_kinded(ident_kinded, with))),
            X(dim1d) => X(Box::new(dim1d.subst_ident_kinded(ident_kinded, with))),
            Y(dim1d) => Y(Box::new(dim1d.subst_ident_kinded(ident_kinded, with))),
            Z(dim1d) => Z(Box::new(dim1d.subst_ident_kinded(ident_kinded, with))),
        }
    }

    fn dim3d(&self) -> Dim3d {
        use Dim::*;
        match self {
            XYZ(d) => d.as_ref().clone(),
            XY(d) => Dim3d(d.0.clone(), d.1.clone(), Nat::Lit(1)),
            XZ(d) => Dim3d(d.0.clone(), Nat::Lit(1), d.1.clone()),
            YZ(d) => Dim3d(Nat::Lit(1), d.0.clone(), d.1.clone()),
            X(d) => Dim3d(d.0.clone(), Nat::Lit(1), Nat::Lit(1)),
            Y(d) => Dim3d(Nat::Lit(1), d.0.clone(), Nat::Lit(1)),
            Z(d) => Dim3d(Nat::Lit(1), Nat::Lit(1), d.0.clone()),
        }
    }
}

impl std::ops::Mul for Dim {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        unimplemented!()
    }
}

impl fmt::Display for Dim {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Dim::*;
        match self {
            XYZ(dim3d) => write!(
                f,
                "{}, {}, {}",
                dim3d.as_ref().0,
                dim3d.as_ref().1,
                dim3d.as_ref().2
            ),
            XY(dim2d) | XZ(dim2d) | YZ(dim2d) => {
                write!(f, "{}, {}", dim2d.as_ref().0, dim2d.as_ref().1)
            }
            X(dim1d) | Y(dim1d) | Z(dim1d) => write!(f, "{}", dim1d.as_ref().0),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Copy, Clone)]
pub enum DimCompo {
    X,
    Y,
    Z,
}

impl fmt::Display for DimCompo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DimCompo::X => write!(f, "x"),
            DimCompo::Y => write!(f, "y"),
            DimCompo::Z => write!(f, "z"),
        }
    }
}

#[span_derive(PartialEq, Eq, Hash)]
#[derive(Debug, Clone)]
pub struct DataTy {
    pub dty: DataTyKind,
    // TODO remove with introduction of traits
    pub constraints: Vec<Constraint>,
    #[span_derive_ignore]
    pub span: Option<Span>,
}
impl DataTy {
    pub fn new(dty: DataTyKind) -> Self {
        DataTy {
            dty,
            constraints: vec![],
            span: None,
        }
    }

    pub fn with_constr(dty: DataTyKind, constraints: Vec<Constraint>) -> Self {
        DataTy {
            dty,
            constraints,
            span: None,
        }
    }

    pub fn with_span(dty: DataTyKind, span: Span) -> Self {
        DataTy {
            dty,
            constraints: vec![],
            span: Some(span),
        }
    }

    pub fn non_copyable(&self) -> bool {
        use DataTyKind::*;

        match &self.dty {
            Scalar(_) => false,
            Atomic(_) => false,
            Ident(_) => true,
            Ref(reff) => reff.own == Ownership::Uniq,
            At(_, _) => true,
            ArrayShape(_, _) => true,
            Tuple(elem_tys) => elem_tys.iter().any(|ty| ty.non_copyable()),
            Array(_, _) => false,
            RawPtr(_) => true,
            Range => true,
            Dead(_) => panic!(
                "This case is not expected to mean anything.\
                The type is dead. There is nothign we can do with it."
            ),
        }
    }

    pub fn copyable(&self) -> bool {
        !self.non_copyable()
    }

    pub fn is_fully_alive(&self) -> bool {
        use DataTyKind::*;
        match &self.dty {
            Scalar(_)
            | RawPtr(_)
            | Range
            | Atomic(_)
            | Ident(_)
            | Ref(_)
            | At(_, _)
            | Array(_, _)
            | ArrayShape(_, _) => true,
            Tuple(elem_tys) => elem_tys
                .iter()
                .fold(true, |acc, ty| acc & ty.is_fully_alive()),
            Dead(_) => false,
        }
    }

    pub fn occurs_in(&self, dty: &DataTy) -> bool {
        if self == dty {
            return true;
        }
        match &dty.dty {
            DataTyKind::Scalar(_) | DataTyKind::Ident(_) | DataTyKind::Range => false,
            DataTyKind::Dead(_) => panic!("unexpected"),
            DataTyKind::Atomic(sty) => &self.dty == &DataTyKind::Scalar(sty.clone()),
            DataTyKind::Ref(reff) => self.occurs_in(&reff.dty),
            DataTyKind::RawPtr(elem_dty) => self.occurs_in(elem_dty),
            DataTyKind::Tuple(elem_dtys) => {
                let mut found = false;
                for elem_dty in elem_dtys {
                    found = self.occurs_in(elem_dty);
                }
                found
            }
            DataTyKind::Array(elem_dty, _) => self.occurs_in(elem_dty),
            DataTyKind::ArrayShape(elem_dty, _) => self.occurs_in(elem_dty),
            DataTyKind::At(elem_dty, _) => self.occurs_in(elem_dty),
        }
    }

    pub fn contains_ref_to_prv(&self, prv_val_name: &str) -> bool {
        use DataTyKind::*;
        match &self.dty {
            Scalar(_) | Atomic(_) | Ident(_) | Range | Dead(_) => false,
            Ref(reff) => {
                let found_reference = if let Provenance::Value(prv_val_n) = &reff.rgn {
                    prv_val_name == prv_val_n
                } else {
                    false
                };
                found_reference || reff.dty.contains_ref_to_prv(prv_val_name)
            }
            RawPtr(dty) => dty.contains_ref_to_prv(prv_val_name),
            At(dty, _) => dty.contains_ref_to_prv(prv_val_name),
            Array(dty, _) => dty.contains_ref_to_prv(prv_val_name),
            ArrayShape(dty, _) => dty.contains_ref_to_prv(prv_val_name),
            Tuple(elem_tys) => elem_tys
                .iter()
                .any(|ty| ty.contains_ref_to_prv(prv_val_name)),
        }
    }

    pub fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Self {
        use DataTyKind::*;
        match &self.dty {
            Scalar(_) | Atomic(_) | Range => self.clone(),
            Ident(id) => {
                if &ident_kinded.ident == id && ident_kinded.kind == Kind::DataTy {
                    match with {
                        ArgKinded::Ident(idk) => DataTy::new(Ident(idk.clone())),
                        ArgKinded::DataTy(dty) => dty.clone(),
                        _ => {
                            panic!("Trying to substitute data type identifier with non-type value.")
                        }
                    }
                } else {
                    self.clone()
                }
            }
            Ref(reff) => DataTy::new(Ref(Box::new(RefDty::new(
                reff.rgn.subst_ident_kinded(ident_kinded, with),
                reff.own,
                reff.mem.subst_ident_kinded(ident_kinded, with),
                reff.dty.subst_ident_kinded(ident_kinded, with),
            )))),
            RawPtr(dty) => {
                DataTy::new(RawPtr(Box::new(dty.subst_ident_kinded(ident_kinded, with))))
            }
            At(dty, mem) => DataTy::new(At(
                Box::new(dty.subst_ident_kinded(ident_kinded, with)),
                mem.subst_ident_kinded(ident_kinded, with),
            )),
            Tuple(elem_tys) => DataTy::new(Tuple(
                elem_tys
                    .iter()
                    .map(|ty| ty.subst_ident_kinded(ident_kinded, with))
                    .collect(),
            )),
            Array(dty, n) => DataTy::new(Array(
                Box::new(dty.subst_ident_kinded(ident_kinded, with)),
                n.subst_ident_kinded(ident_kinded, with),
            )),
            ArrayShape(dty, n) => DataTy::new(ArrayShape(
                Box::new(dty.subst_ident_kinded(ident_kinded, with)),
                n.subst_ident_kinded(ident_kinded, with),
            )),
            Dead(dty) => DataTy::new(Dead(Box::new(dty.subst_ident_kinded(ident_kinded, with)))),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct RefDty {
    pub rgn: Provenance,
    pub own: Ownership,
    pub mem: Memory,
    pub dty: Box<DataTy>,
}

impl RefDty {
    pub fn new(rgn: Provenance, own: Ownership, mem: Memory, dty: DataTy) -> Self {
        RefDty {
            rgn,
            own,
            mem,
            dty: Box::new(dty),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum DataTyKind {
    Ident(Ident),
    Scalar(ScalarTy),
    Atomic(ScalarTy),
    Array(Box<DataTy>, Nat),
    // [[ dty; n ]]
    ArrayShape(Box<DataTy>, Nat),
    Tuple(Vec<DataTy>),
    At(Box<DataTy>, Memory),
    Ref(Box<RefDty>),
    RawPtr(Box<DataTy>),
    Range,
    // Only for type checking purposes.
    Dead(Box<DataTy>),
}

#[derive(PartialEq, Eq, Hash, Debug, Copy, Clone)]
pub enum ScalarTy {
    Unit,
    U32,
    U64,
    I32,
    I64,
    F32,
    F64,
    Bool,
    Gpu,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum Provenance {
    Value(String),
    Ident(Ident),
}

impl Provenance {
    fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Self {
        if ident_kinded.kind == Kind::Provenance {
            match self {
                Provenance::Ident(id) if id == &ident_kinded.ident => match with {
                    ArgKinded::Ident(idk) => Provenance::Ident(idk.clone()),
                    ArgKinded::Provenance(prv) => prv.clone(),
                    err => panic!(
                        "Trying to create provenance value from non-provenance `{:?}`",
                        err
                    ),
                },
                _ => self.clone(),
            }
        } else {
            self.clone()
        }
    }
}

impl fmt::Display for Provenance {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Value(name) => write!(f, "{}", name),
            Self::Ident(ty_ident) => write!(f, "{}", ty_ident),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum Memory {
    CpuMem,
    GpuGlobal,
    GpuShared,
    GpuLocal,
    Ident(Ident),
}

impl Memory {
    fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Memory {
        if ident_kinded.kind == Kind::Memory {
            match self {
                Memory::Ident(id) if id == &ident_kinded.ident => match with {
                    ArgKinded::Ident(kid) => Memory::Ident(kid.clone()),
                    ArgKinded::Memory(m) => m.clone(),
                    err => panic!("Trying to create Memory value from non-memory `{:?}`", err),
                },
                _ => self.clone(),
            }
        } else {
            self.clone()
        }
    }
}

impl fmt::Display for Memory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Memory::CpuMem => write!(f, "cpu.mem"),
            Memory::GpuGlobal => write!(f, "gpu.global"),
            Memory::GpuShared => write!(f, "gpu.shared"),
            Memory::GpuLocal => write!(f, "gpu.local"),
            Memory::Ident(x) => write!(f, "{}", x),
        }
    }
}

#[span_derive(PartialEq, Eq, Hash)]
#[derive(Debug, Clone)]
pub struct ExecTy {
    pub ty: ExecTyKind,
    #[span_derive_ignore]
    pub span: Option<Span>,
}

impl ExecTy {
    pub fn new(exec: ExecTyKind) -> Self {
        ExecTy {
            ty: exec,
            span: None,
        }
    }
}

impl fmt::Display for ExecTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.ty)
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum ExecTyKind {
    CpuThread,
    GpuGrid(Dim, Dim),
    GpuBlock(Dim),
    GpuGlobalThreads(Dim),
    GpuBlockGrp(Dim, Dim),
    GpuThreadGrp(Dim),
    GpuThread,
    View,
}

impl fmt::Display for ExecTyKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExecTyKind::CpuThread => write!(f, "cpu.thread"),
            ExecTyKind::GpuGrid(gsize, bsize) => write!(f, "gpu.grid<{}, {}>", gsize, bsize),
            ExecTyKind::GpuGlobalThreads(size) => write!(f, "gpu.global_threads<{}>", size),
            ExecTyKind::GpuBlock(bsize) => write!(f, "gpu.block<{}>", bsize),
            ExecTyKind::GpuThread => write!(f, "gpu.thread"),
            ExecTyKind::GpuBlockGrp(gsize, bsize) => {
                write!(f, "gpu.block_grp<{}, {}>", gsize, bsize)
            }
            ExecTyKind::GpuThreadGrp(size) => write!(f, "gpu.thread_grp<{}>", size),
            ExecTyKind::View => write!(f, "view"),
        }
    }
}

// Provenance Relation: varrho_1:varrho_2
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct PrvRel {
    pub longer: Ident,
    pub shorter: Ident,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct IdentKinded {
    pub ident: Ident,
    pub kind: Kind,
}

impl IdentKinded {
    pub fn new(ident: &Ident, kind: Kind) -> Self {
        IdentKinded {
            ident: ident.clone(),
            kind: kind.clone(),
        }
    }
}

// FIXME Implement Hash
#[derive(Eq, Hash, Debug, Clone)]
pub enum Nat {
    Ident(Ident),
    Lit(usize),
    ThreadIdx(DimCompo),
    BlockIdx(DimCompo),
    BlockDim(DimCompo),
    // Dummy that is always 0, i.e. equivalent to Lit(0)
    GridIdx,
    BinOp(BinOpNat, Box<Nat>, Box<Nat>),
    // Use Box<[Nat]> to safe 8 bytes compared to Vec<Nat>
    App(Ident, Box<[Nat]>),
}

impl Nat {
    // Very naive implementation covering only one case.
    pub fn simplify(&self) -> Nat {
        match self {
            Nat::BinOp(BinOpNat::Mul, l, r) => match l.as_ref() {
                Nat::BinOp(BinOpNat::Div, ll, lr) if lr.as_ref() == r.as_ref() => ll.simplify(),
                _ => Nat::BinOp(
                    BinOpNat::Mul,
                    Box::new(l.simplify()),
                    Box::new(r.simplify()),
                ),
            },
            Nat::BinOp(BinOpNat::Add, l, r) => match (l.as_ref(), r.as_ref()) {
                (Nat::Lit(0), r) => r.simplify(),
                (l, Nat::Lit(0)) => l.simplify(),
                _ => Nat::BinOp(
                    BinOpNat::Add,
                    Box::new(l.simplify()),
                    Box::new(r.simplify()),
                ),
            },
            Nat::BinOp(op, l, r) => {
                Nat::BinOp(op.clone(), Box::new(l.simplify()), Box::new(r.simplify()))
            }
            _ => self.clone(),
        }
    }

    pub fn eval(&self) -> Result<usize, String> {
        match self {
            Nat::Ident(_)
            | Nat::GridIdx
            | Nat::BlockIdx(_)
            | Nat::BlockDim(_)
            | Nat::ThreadIdx(_) => Err("Cannot evaluate.".to_string()),
            Nat::Lit(n) => Ok(*n),
            Nat::BinOp(op, l, r) => match op {
                BinOpNat::Add => Ok(l.eval()? + r.eval()?),
                BinOpNat::Sub => Ok(l.eval()? - r.eval()?),
                BinOpNat::Mul => Ok(l.eval()? * r.eval()?),
                BinOpNat::Div => Ok(l.eval()? / r.eval()?),
                BinOpNat::Mod => Ok(l.eval()? % r.eval()?),
            },
            Nat::App(_, _) => unimplemented!(),
        }
    }

    pub fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Nat {
        if ident_kinded.kind == Kind::Nat {
            match self {
                Nat::Ident(id) if id == &ident_kinded.ident => match with {
                    ArgKinded::Ident(idk) => Nat::Ident(idk.clone()),
                    ArgKinded::Nat(n) => n.clone(),
                    err => panic!("Trying to create nat value from non-nat `{:?}`", err),
                },
                Nat::BinOp(op, n1, n2) => Nat::BinOp(
                    op.clone(),
                    Box::new(n1.subst_ident_kinded(ident_kinded, with)),
                    Box::new(n2.subst_ident_kinded(ident_kinded, with)),
                ),
                _ => self.clone(),
            }
        } else {
            self.clone()
        }
    }
}

#[test]
fn test_simplify() {
    let d = Nat::Ident(Ident::new("d"));
    let i = Nat::Ident(Ident::new("i"));
    let n = Nat::BinOp(
        BinOpNat::Mul,
        Box::new(Nat::BinOp(
            BinOpNat::Div,
            Box::new(i.clone()),
            Box::new(d.clone()),
        )),
        Box::new(d),
    );
    let r = n.simplify();
    if i != r {
        panic!("{}", r)
    }
}

impl PartialEq for Nat {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Nat::Lit(l), Nat::Lit(o)) => l == o,
            (Nat::Ident(i), Nat::Ident(o)) if i == o => true,
            (Nat::BinOp(op, lhs, rhs), Nat::BinOp(oop, olhs, orhs))
                if op == oop && lhs == olhs && rhs == orhs =>
            {
                true
            }
            _ => match (self.eval(), other.eval()) {
                (Ok(n), Ok(o)) => n == o,
                _ => false,
            },
        }
    }
}

impl PartialOrd for Nat {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Nat::Lit(l), Nat::Lit(o)) if l < o => Some(Ordering::Less),
            (Nat::Lit(l), Nat::Lit(o)) if l == o => Some(Ordering::Equal),
            (Nat::Lit(l), Nat::Lit(o)) if l > o => Some(Ordering::Greater),
            (Nat::BinOp(op, lhs, rhs), Nat::BinOp(oop, olhs, orhs))
                if op == oop && lhs == olhs && rhs == orhs =>
            {
                Some(Ordering::Equal)
            }
            _ => match (self.eval(), other.eval()) {
                (Ok(n), Ok(o)) if n < o => Some(Ordering::Less),
                (Ok(n), Ok(o)) if n == o => Some(Ordering::Equal),
                (Ok(n), Ok(o)) if n > o => Some(Ordering::Greater),
                _ => None,
            },
        }
    }
}

impl fmt::Display for Nat {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Ident(ident) => write!(f, "{}", ident),
            Self::GridIdx => Ok(()),
            Self::BlockIdx(d) => write!(f, "blockIdx.{}", d),
            Self::BlockDim(d) => write!(f, "blockDim.{}", d),
            Self::ThreadIdx(d) => write!(f, "threadIdx.{}", d),
            Self::Lit(n) => write!(f, "{}", n),
            Self::BinOp(op, lhs, rhs) => write!(f, "({} {} {})", lhs, op, rhs),
            Self::App(func, args) => {
                write!(f, "{}(", func)?;
                if let Some((last, leading)) = args.split_last() {
                    for arg in leading {
                        write!(f, "{}, ", arg)?;
                    }
                    write!(f, "{})", last)?;
                }
                Ok(())
            }
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum BinOpNat {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

impl fmt::Display for BinOpNat {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Add => write!(f, "+"),
            Self::Sub => write!(f, "-"),
            Self::Mul => write!(f, "*"),
            Self::Div => write!(f, "/"),
            Self::Mod => write!(f, "%"),
        }
    }
}

// When changing the AST, the types can quickly grow and lead to stack overflows in the different
//  compiler stages.
//
// Taken from the rustc implementation and adjusted for this AST:
// Some nodes are used a lot. Make sure they don't unintentionally get bigger.
#[cfg(all(target_arch = "x86_64", target_pointer_width = "64"))]
mod size_asserts {
    use super::*;
    // Type size assertion. The first argument is a type and the second argument is its expected size.
    macro_rules! static_assert_size {
        ($ty:ty, $size:expr) => {
            const _: [(); $size] = [(); ::std::mem::size_of::<$ty>()];
        };
    }
    static_assert_size!(Dim, 16);
    static_assert_size!(DataTy, 112);
    static_assert_size!(DataTyKind, 72);
    static_assert_size!(ExecExpr, 32);
    static_assert_size!(Exec, 64);
    static_assert_size!(ExecPathElem, 16);
    static_assert_size!(ExecTy, 56);
    static_assert_size!(ExecTyKind, 40);
    static_assert_size!(Expr, 128);
    static_assert_size!(ExprKind, 104);
    static_assert_size!(FunDef, 264);
    static_assert_size!(Ident, 32); // maybe too large?
    static_assert_size!(IdentExec, 40);
    static_assert_size!(Lit, 16);
    static_assert_size!(Memory, 32);
    static_assert_size!(Nat, 56);
    static_assert_size!(ParamDecl, 72);
    static_assert_size!(Pattern, 40);
    static_assert_size!(PlaceExpr, 88);
    static_assert_size!(PlaceExprKind, 40);
    static_assert_size!(ScalarTy, 1);
    static_assert_size!(Ty, 32);
    static_assert_size!(TyKind, 16);
}
