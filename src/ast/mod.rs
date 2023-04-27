use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;

use descend_derive::span_derive;
pub use span::*;

use crate::ast::visit_mut::VisitMut;
use crate::parser::SourceCode;

pub mod internal;

pub mod printer;
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

    // pub fn subst_idents(&mut self, subst_map: &HashMap<&str, &Expr>) {
    //     fn pl_expr_contains_name_in<'a, I>(pl_expr: &PlaceExpr, mut idents: I) -> bool
    //     where
    //         I: Iterator<Item = &'a &'a str>,
    //     {
    //         match &pl_expr.pl_expr {
    //             PlaceExprKind::Ident(ident) => idents.any(|name| ident.name.as_ref() == *name),
    //             PlaceExprKind::Proj(tuple, _) => pl_expr_contains_name_in(tuple, idents),
    //             PlaceExprKind::Deref(deref) => pl_expr_contains_name_in(deref, idents),
    //             PlaceExprKind::Select(pl_expr, _) => pl_expr_contains_name_in(pl_expr, idents),
    //             PlaceExprKind::SplitAt(_, pl_expr) => pl_expr_contains_name_in(pl_expr, idents),
    //             PlaceExprKind::View(pl_expr, _) => pl_expr_contains_name_in(pl_expr, idents),
    //             PlaceExprKind::Idx(pl_expr, _) => pl_expr_contains_name_in(pl_expr, idents),
    //         }
    //     }
    //
    //     struct SubstIdents<'a> {
    //         subst_map: &'a HashMap<&'a str, &'a Expr>,
    //     }
    //     impl VisitMut for SubstIdents<'_> {
    //         fn visit_pl_expr(&mut self, pl_expr: &mut PlaceExpr) {
    //             if pl_expr_contains_name_in(pl_expr, self.subst_map.keys()) {
    //                 match &pl_expr.pl_expr {
    //                     PlaceExprKind::Ident(ident) => {
    //                         let subst_expr =
    //                             self.subst_map.get::<str>(ident.name.as_ref()).unwrap();
    //                         if let ExprKind::PlaceExpr(pl_e) = &subst_expr.expr {
    //                             *pl_expr = pl_e.as_ref().clone();
    //                         } else {
    //                             // TODO can this happen?
    //                             panic!("How did this happen?")
    //                         }
    //                     }
    //                     _ => visit_mut::walk_pl_expr(self, pl_expr),
    //                 }
    //             }
    //         }
    //
    //         fn visit_expr(&mut self, expr: &mut Expr) {
    //             match &expr.expr {
    //                 ExprKind::PlaceExpr(pl_expr) => {
    //                     if pl_expr_contains_name_in(pl_expr, self.subst_map.keys()) {
    //                         match &pl_expr.pl_expr {
    //                             PlaceExprKind::Ident(ident) => {
    //                                 if let Some(&subst_expr) =
    //                                     self.subst_map.get::<str>(ident.name.as_ref())
    //                                 {
    //                                     *expr = subst_expr.clone();
    //                                 }
    //                             }
    //                             PlaceExprKind::Proj(tuple, i) => {
    //                                 let mut tuple_expr = Expr::new(ExprKind::PlaceExpr(Box::new(
    //                                     tuple.as_ref().clone(),
    //                                 )));
    //                                 self.visit_expr(&mut tuple_expr);
    //                                 *expr = Expr::new(ExprKind::Proj(Box::new(tuple_expr), *i));
    //                             }
    //                             PlaceExprKind::Deref(deref_expr) => {
    //                                 let mut ref_expr = Expr::new(ExprKind::PlaceExpr(Box::new(
    //                                     deref_expr.as_ref().clone(),
    //                                 )));
    //                                 self.visit_expr(&mut ref_expr);
    //                                 *expr = Expr::new(ExprKind::Deref(Box::new(ref_expr)));
    //                             }
    //                             PlaceExprKind::Select(_, _)
    //                             | PlaceExprKind::SplitAt(_, _)
    //                             | PlaceExprKind::Idx(_, _)
    //                             | PlaceExprKind::View(_, _) => {
    //                                 unimplemented!()
    //                             }
    //                         }
    //                     }
    //                 }
    //                 _ => visit_mut::walk_expr(self, expr),
    //             }
    //         }
    //     }
    //     let mut subst_idents = SubstIdents { subst_map };
    //     subst_idents.visit_expr(self);
    // }
}

#[derive(PartialEq, Debug, Clone)]
pub struct Sched {
    pub dim: DimCompo,
    pub inner_exec_ident: Option<Ident>,
    pub sched_exec: ExecExpr,
    pub body: Box<Block>,
}

impl Sched {
    pub fn new(
        dim: DimCompo,
        inner_exec_ident: Option<Ident>,
        sched_exec: ExecExpr,
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
pub struct Indep {
    pub dim_compo: DimCompo,
    pub pos: Nat,
    pub split_exec: ExecExpr,
    pub branch_idents: Vec<Ident>,
    pub branch_bodies: Vec<Expr>,
}

impl Indep {
    pub fn new(
        dim_compo: DimCompo,
        pos: Nat,
        split_exec: ExecExpr,
        branch_idents: Vec<Ident>,
        branch_bodies: Vec<Expr>,
    ) -> Self {
        Indep {
            dim_compo,
            pos,
            split_exec,
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
    // e.g., [1, 2 + 3, 4]
    Array(Vec<Expr>),
    Tuple(Vec<Expr>),
    // Borrow Expressions
    Ref(Option<String>, Ownership, Box<PlaceExpr>),
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
    Sync(Option<ExecExpr>),
    Range(Box<Expr>, Box<Expr>),
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
            ArgKinded::Ident(i) => {
                panic!("Unexpected: unkinded identifier should have been removed after parsing, ident: {}", i)
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
    #[span_derive_ignore]
    pub span: Option<Span>,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct View {
    pub name: Ident,
    pub gen_args: Vec<ArgKinded>,
    pub args: Vec<View>,
}

// TODO create generic View struct to enable easier extensibility by introducing only
//  new predeclared types
// #[derive(PartialEq, Eq, Hash, Debug, Clone)]
// pub enum View {
//     ToView,
//     Group(Nat),
//     SplitAt(Nat),
//     Transpose,
//     Rev,
//     Map(Box<View>),
// }

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum PlaceExprKind {
    View(Box<PlaceExpr>, Box<View>),
    // similar to a projection, but it projects an element for each provided execution resource
    // (similar to indexing)
    // p[[x]]
    Select(Box<PlaceExpr>, Box<ExecExpr>),
    // p.0 | p.1
    Proj(Box<PlaceExpr>, usize),
    // *p
    Deref(Box<PlaceExpr>),
    // Index into array, e.g., arr[i]
    Idx(Box<PlaceExpr>, Box<Nat>),
    // x
    Ident(Ident),
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum PlExprPathElem {
    View(View),
    Select(Box<ExecExpr>),
    SplitAt(Box<Nat>),
    Proj(usize),
    Deref,
    Idx(Box<Nat>),
    Ident(Ident),
}

impl PlaceExpr {
    pub fn new(pl_expr: PlaceExprKind) -> Self {
        PlaceExpr {
            pl_expr,
            ty: None,
            span: None,
        }
    }

    pub fn with_span(pl_expr: PlaceExprKind, span: Span) -> Self {
        PlaceExpr {
            pl_expr,
            ty: None,
            span: Some(span),
        }
    }

    pub fn is_place(&self) -> bool {
        match &self.pl_expr {
            PlaceExprKind::Ident(_) => true,
            PlaceExprKind::Proj(ple, _) => ple.is_place(),
            PlaceExprKind::Select(_, _)
            | PlaceExprKind::Deref(_)
            | PlaceExprKind::Idx(_, _)
            | PlaceExprKind::View(_, _) => false,
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
            PlaceExprKind::Select(inner_ple, exec_idents) => {
                let (pl_ctx, pl) = inner_ple.to_pl_ctx_and_most_specif_pl();
                (
                    internal::PlaceCtx::Select(Box::new(pl_ctx), exec_idents.clone()),
                    pl,
                )
            }
            PlaceExprKind::Deref(inner_ple) => {
                let (pl_ctx, pl) = inner_ple.to_pl_ctx_and_most_specif_pl();
                (internal::PlaceCtx::Deref(Box::new(pl_ctx)), pl)
            }
            PlaceExprKind::View(inner_ple, view) => {
                let (pl_ctx, pl) = inner_ple.to_pl_ctx_and_most_specif_pl();
                (internal::PlaceCtx::View(Box::new(pl_ctx), view.clone()), pl)
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
            PlaceExprKind::Idx(inner_ple, idx) => {
                let (pl_ctx, pl) = inner_ple.to_pl_ctx_and_most_specif_pl();
                (internal::PlaceCtx::Idx(Box::new(pl_ctx), idx.clone()), pl)
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

    pub fn as_ident_and_path(&self) -> (Ident, Vec<PlExprPathElem>) {
        fn as_ident_and_path_rec(
            pl_expr: &PlaceExpr,
            mut path: Vec<PlExprPathElem>,
        ) -> (Ident, Vec<PlExprPathElem>) {
            match &pl_expr.pl_expr {
                PlaceExprKind::Ident(i) => {
                    path.reverse();
                    (i.clone(), path)
                }
                PlaceExprKind::Select(inner_ple, exec_idents) => {
                    path.push(PlExprPathElem::Select(exec_idents.clone()));
                    as_ident_and_path_rec(inner_ple, path)
                }
                PlaceExprKind::Deref(inner_ple) => {
                    path.push(PlExprPathElem::Deref);
                    as_ident_and_path_rec(inner_ple, path)
                }
                PlaceExprKind::View(inner_ple, view) => {
                    path.push(PlExprPathElem::View(view.as_ref().clone()));
                    as_ident_and_path_rec(inner_ple, path)
                }
                PlaceExprKind::Proj(inner_ple, n) => {
                    path.push(PlExprPathElem::Proj(*n));
                    as_ident_and_path_rec(inner_ple, path)
                }
                PlaceExprKind::Idx(inner_ple, idx) => {
                    path.push(PlExprPathElem::Idx(idx.clone()));
                    as_ident_and_path_rec(inner_ple, path)
                }
            }
        }
        as_ident_and_path_rec(self, vec![])
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
        if self.exec.path.len() > exec.exec.path.len() {
            return self.exec.path[..exec.exec.path.len()] == exec.exec.path;
        }
        false
    }

    pub fn remove_last_distrib(&self) -> ExecExpr {
        let last_distrib_pos = self
            .exec
            .path
            .iter()
            .rposition(|e| matches!(e, ExecPathElem::Distrib(_)));
        let removed_distrib_path = if let Some(ldp) = last_distrib_pos {
            self.exec.path[..ldp].to_vec()
        } else {
            vec![]
        };
        ExecExpr::new(Exec::with_path(
            self.exec.base.clone(),
            removed_distrib_path,
        ))
    }
}

#[test]
fn equal_exec_exprs() {
    let exec1 = ExecExpr::new(Exec::with_path(
        BaseExec::Ident(Ident::new("grid")),
        vec![ExecPathElem::Distrib(DimCompo::X)],
    ));
    let exec2 = ExecExpr::new(Exec::with_path(
        BaseExec::Ident(Ident::new("grid")),
        vec![ExecPathElem::Distrib(DimCompo::X)],
    ));
    if exec1 != exec2 {
        panic!("Unequal execs, that should be equal")
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

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct Exec {
    pub base: BaseExec,
    pub path: Vec<ExecPathElem>,
}

impl Exec {
    pub fn new(base: BaseExec) -> Self {
        Exec { base, path: vec![] }
    }

    pub fn with_path(base: BaseExec, path: Vec<ExecPathElem>) -> Self {
        Exec { base, path }
    }

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

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum BaseExec {
    Ident(Ident),
    CpuThread,
    GpuGrid(Dim, Dim),
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum ExecPathElem {
    SplitProj(Box<SplitProj>),
    Distrib(DimCompo),
    ToThreads(DimCompo),
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
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct Dim1d(pub Nat);
#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct Dim2d(pub Nat, pub Nat);
#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct Dim3d(pub Nat, pub Nat, pub Nat);
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
}

#[derive(PartialEq, Eq, Hash, Debug, Copy, Clone)]
pub enum DimCompo {
    X,
    Y,
    Z,
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
    // TODO remove. This is an attribute of a typing context entry, not the type.
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

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum Memory {
    CpuMem,
    GpuGlobal,
    GpuShared,
    GpuLocal,
    Ident(Ident),
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

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum BinOpNat {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
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
    static_assert_size!(PlaceExpr, 56); //ACHTUNG bei mir geändert -> eigentlich 56
    static_assert_size!(PlaceExprKind, 32); //ACHTUNG bei mir geändert -> eigentlich 32
    static_assert_size!(ScalarTy, 1);
    static_assert_size!(Ty, 32);
    static_assert_size!(TyKind, 16);
}
