use std::fmt;

use crate::ast::internal::PathElem;
use bumpalo::{collections::Vec as BumpVec, Bump};
use descend_derive::span_derive;
pub use span::*;

use crate::parser::SourceCode;

pub mod internal;

pub mod printer;
mod span;
pub mod utils;
pub mod visit;
pub mod visit_mut;

#[derive(Clone, Debug)]
pub struct CompilUnit<'a> {
    pub items: Vec<Item<'a>>,
    pub source: &'a SourceCode<'a>,
}

impl<'a> CompilUnit<'a> {
    pub fn new(items: Vec<Item<'a>>, source: &'a SourceCode<'a>) -> Self {
        CompilUnit { items, source }
    }
}

#[derive(Debug, Clone)]
pub enum Item<'a> {
    FunDef(&'a FunDef<'a>),
    FunDecl(&'a FunDecl<'a>),
    StructDecl(&'a StructDecl<'a>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunDecl<'a> {
    pub ident: Ident<'a>,
    pub generic_params: BumpVec<'a, IdentKinded<'a>>,
    pub generic_exec: Option<IdentExec<'a>>,
    pub param_decls: BumpVec<'a, ParamDecl<'a>>,
    pub ret_dty: &'a DataTy<'a>,
    pub exec: ExecExpr<'a>,
    pub prv_rels: BumpVec<'a, PrvRel<'a>>,
}

impl<'a> FunDecl<'a> {
    pub fn fn_ty(&self, bump: &'a Bump) -> FnTy<'a> {
        let mut param_sigs = BumpVec::new_in(bump);
        for p_decl in &self.param_decls {
            let exec_expr = p_decl.exec_expr.as_ref().unwrap_or(&self.exec).clone();
            let ty = p_decl.ty.as_ref().unwrap().clone(); // This may need arena allocation too
            param_sigs.push(ParamSig::new(exec_expr, ty));
        }

        let mut generics = BumpVec::new_in(bump);
        generics.extend(self.generic_params.iter().cloned());

        FnTy::new(
            bump,
            generics,
            self.generic_exec.clone(),
            param_sigs,
            self.exec.clone(),
            bump.alloc(Ty {
                ty: TyKind::Data(self.ret_dty),
                span: None,
            }),
            [],
        )
    }
}

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub struct StructDecl<'a> {
    pub ident: Ident<'a>,
    pub generic_params: BumpVec<'a, IdentKinded<'a>>,
    pub fields: BumpVec<'a, (Ident<'a>, DataTy<'a>)>,
}

// TODO refactor to make use of FunDecl
#[derive(Debug, Clone, PartialEq)]
pub struct FunDef<'a> {
    pub ident: Ident<'a>,
    pub generic_params: BumpVec<'a, IdentKinded<'a>>,
    pub generic_exec: Option<IdentExec<'a>>,
    pub param_decls: BumpVec<'a, ParamDecl<'a>>,
    pub ret_dty: &'a DataTy<'a>,
    pub exec: ExecExpr<'a>,
    pub prv_rels: BumpVec<'a, PrvRel<'a>>,
    pub body: &'a Block<'a>,
}

impl<'a> FunDef<'a> {
    pub fn fn_ty(&self, bump: &'a Bump) -> FnTy<'a> {
        let mut param_sigs = BumpVec::new_in(bump);
        for p_decl in &self.param_decls {
            let exec_expr = p_decl.exec_expr.as_ref().unwrap_or(&self.exec).clone();
            let ty = p_decl.ty.expect("Missing parameter type");
            let ty_ref = bump.alloc(ty.clone());
            param_sigs.push(ParamSig::new(exec_expr, ty_ref));
        }

        let mut generics = BumpVec::new_in(bump);
        generics.extend(self.generic_params.iter().cloned());

        let ret_ty = bump.alloc(Ty {
            ty: TyKind::Data(self.ret_dty),
            span: None,
        });

        FnTy::new(
            bump,
            generics,
            self.generic_exec.clone(),
            param_sigs,
            self.exec.clone(),
            ret_ty,
            [],
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IdentExec<'a> {
    pub ident: Ident<'a>,
    pub ty: &'a ExecTy<'a>,
}

impl<'a> IdentExec<'a> {
    pub fn new_in(bump: &'a bumpalo::Bump, ident: Ident<'a>, exec_ty: ExecTy<'a>) -> Self {
        IdentExec {
            ident,
            ty: bump.alloc(exec_ty),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParamDecl<'a> {
    pub ident: Ident<'a>,
    pub ty: Option<&'a Ty<'a>>,
    pub mutbl: Mutability,
    pub exec_expr: Option<ExecExpr<'a>>,
}

#[span_derive(PartialEq)]
#[derive(Debug, Clone)]
pub struct Expr<'a> {
    pub expr: ExprKind<'a>,
    // FIXME misusing span_derive_ignore to ignore type on equality checks
    #[span_derive_ignore]
    pub ty: Option<&'a Ty<'a>>,
    #[span_derive_ignore]
    pub span: Option<Span>,
}

impl<'a> Expr<'a> {
    pub fn new(expr: ExprKind<'a>) -> Self {
        Expr {
            expr,
            ty: None,
            span: None,
        }
    }

    pub fn with_span(expr: ExprKind<'a>, span: Span) -> Self {
        Expr {
            expr,
            ty: None,
            span: Some(span),
        }
    }

    pub fn with_type(expr: ExprKind<'a>, ty: &'a Ty<'a>) -> Self {
        Expr {
            expr,
            ty: Some(ty),
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
pub struct Sched<'a> {
    pub dim: DimCompo,
    pub inner_exec_ident: Option<Ident<'a>>,
    pub sched_exec: &'a ExecExpr<'a>,
    pub body: &'a Block<'a>,
}

impl<'a> Sched<'a> {
    pub fn new_in(
        bump: &'a bumpalo::Bump,
        dim: DimCompo,
        inner_exec_ident: Option<Ident<'a>>,
        sched_exec: ExecExpr<'a>,
        body: Block<'a>,
    ) -> Self {
        Sched {
            dim,
            inner_exec_ident,
            sched_exec: bump.alloc(sched_exec),
            body: bump.alloc(body),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct Split<'a> {
    pub dim_compo: DimCompo,
    pub pos: Nat<'a>,
    pub split_exec: &'a ExecExpr<'a>,
    pub branch_idents: BumpVec<'a, Ident<'a>>,
    pub branch_bodies: BumpVec<'a, Expr<'a>>,
}

impl<'a> Split<'a> {
    pub fn new(
        bump: &'a bumpalo::Bump,
        dim_compo: DimCompo,
        pos: Nat<'a>,
        split_exec: ExecExpr<'a>,
        branch_idents: impl IntoIterator<Item = Ident<'a>>,
        branch_bodies: impl IntoIterator<Item = Expr<'a>>,
    ) -> Self {
        let split_exec = bump.alloc(split_exec);

        let mut idents = BumpVec::new_in(bump);
        idents.extend(branch_idents);

        let mut bodies = BumpVec::new_in(bump);
        bodies.extend(branch_bodies);

        Split {
            dim_compo,
            pos,
            split_exec,
            branch_idents: idents,
            branch_bodies: bodies,
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct Block<'a> {
    pub prvs: BumpVec<'a, String>,
    pub body: &'a Expr<'a>,
}

impl<'a> Block<'a> {
    pub fn new(bump: &'a bumpalo::Bump, body: Expr<'a>) -> Self {
        Block {
            prvs: BumpVec::new_in(bump),
            body: bump.alloc(body),
        }
    }

    pub fn with_prvs(
        bump: &'a bumpalo::Bump,
        prvs: impl IntoIterator<Item = String>,
        body: Expr<'a>,
    ) -> Self {
        let mut prvs_vec = BumpVec::new_in(bump);
        prvs_vec.extend(prvs);
        Block {
            prvs: prvs_vec,
            body: bump.alloc(body),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct AppKernel<'a> {
    pub grid_dim: Dim<'a>,
    pub block_dim: Dim<'a>,
    pub shared_mem_dtys: BumpVec<'a, DataTy<'a>>,
    pub shared_mem_prvs: BumpVec<'a, String>,
    pub fun_ident: &'a Ident<'a>,
    pub gen_args: BumpVec<'a, ArgKinded<'a>>,
    pub args: BumpVec<'a, Expr<'a>>,
}

#[derive(PartialEq, Debug, Clone)]
pub enum ExprKind<'a> {
    Hole,
    Lit(Lit),
    // An l-value equivalent: *p, p.n, x
    PlaceExpr(&'a PlaceExpr<'a>),
    // e.g., [1, 2 + 3, 4]
    Array(BumpVec<'a, Expr<'a>>),
    Tuple(BumpVec<'a, Expr<'a>>),
    // Borrow Expressions
    Ref(Option<String>, Ownership, &'a PlaceExpr<'a>),
    Block(&'a Block<'a>),
    // Variable declaration
    // let mut x: ty;
    LetUninit(Option<&'a ExecExpr<'a>>, Ident<'a>, &'a Ty<'a>),
    // let w x: ty = e1
    Let(Pattern<'a>, Option<&'a Ty<'a>>, &'a Expr<'a>),
    // Assignment to existing place [expression]
    Assign(&'a PlaceExpr<'a>, &'a Expr<'a>),
    // e1[i] = e2
    IdxAssign(&'a PlaceExpr<'a>, Nat<'a>, &'a Expr<'a>),
    // e1 ; e2
    Seq(BumpVec<'a, Expr<'a>>),
    // Anonymous function which can capture its surrounding context
    // | x_n: d_1, ..., x_n: d_n | [exec]-> d_r { e }
    // TODO body expression should always be block?! No but treated like one.
    //Lambda(Vec<ParamDecl>, Ident<'a>Exec, Box<DataTy>, Box<Expr>),
    // Function application
    // e_f(e_1, ..., e_n)
    App(
        &'a Ident<'a>,
        BumpVec<'a, ArgKinded<'a>>,
        BumpVec<'a, Expr<'a>>,
    ),
    DepApp(Ident<'a>, BumpVec<'a, ArgKinded<'a>>),
    AppKernel(&'a AppKernel<'a>),
    // TODO branches must be blocks
    IfElse(&'a Expr<'a>, &'a Expr<'a>, &'a Expr<'a>),
    // TODO branch must be block
    If(&'a Expr<'a>, &'a Expr<'a>),
    // For-each loop.
    // for x in e_1 { e_2 }
    // TODO body must be block
    For(Ident<'a>, &'a Expr<'a>, &'a Expr<'a>),
    // for n in range(..) { e }
    // TODO body must be block
    ForNat(Ident<'a>, &'a NatRange<'a>, &'a Expr<'a>),
    // while( e_1 ) { e_2 }
    // TODO body must be block
    While(&'a Expr<'a>, &'a Expr<'a>),
    BinOp(BinOp, &'a Expr<'a>, &'a Expr<'a>),
    UnOp(UnOp, &'a Expr<'a>),
    Cast(&'a Expr<'a>, &'a DataTy<'a>),
    // TODO branches must be blocks or treated like blocks
    Split(&'a Split<'a>),
    Sched(&'a Sched<'a>),
    Sync(Option<ExecExpr<'a>>),
    Unsafe(&'a Expr<'a>),
    Range(&'a Expr<'a>, &'a Expr<'a>),
}

#[span_derive(PartialEq, Eq, Hash)]
#[derive(Clone, Debug)]
pub struct Ident<'a> {
    // Identifier names never change. Instead a new identifier is created. Therefore it is not
    // necessary to keep the capacity that is stored in a String for efficient appending.
    pub name: &'a str,
    #[span_derive_ignore]
    pub span: Option<Span>,
    pub is_implicit: bool,
}
// TODO: Arena String Interna nachschauen
impl<'a> Ident<'a> {
    pub fn new(bump: &'a bumpalo::Bump, name: &'a str) -> Self {
        Self {
            name: bump.alloc_str(name),
            span: None,
            is_implicit: false,
        }
    }

    pub fn new_impli(bump: &'a bumpalo::Bump, name: &'a str) -> Self {
        Self {
            name: bump.alloc_str(name),
            span: None,
            is_implicit: true,
        }
    }

    pub fn with_span(bump: &'a bumpalo::Bump, name: &'a str, span: Span) -> Self {
        Self {
            name: bump.alloc_str(name),
            span: Some(span),
            is_implicit: false,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Pattern<'a> {
    Ident(Mutability, Ident<'a>),
    Tuple(BumpVec<'a, Pattern<'a>>),
    Wildcard,
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Lit {
    Unit,
    Bool(bool),
    I32(i32),
    U8(u8),
    U32(u32),
    U64(u64),
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
            Self::U8(uc) => write!(f, "{}", uc),
            Self::U32(u) => write!(f, "{}", u),
            Self::U64(ul) => write!(f, "{}", ul),
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
    Shl,
    Shr,
    BitOr,
    BitAnd,
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
            Self::Shl => "<<",
            Self::Shr => ">>",
            Self::BitOr => "|",
            Self::BitAnd => "&",
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
pub enum ArgKinded<'a> {
    Ident(Ident<'a>),
    Nat(Nat<'a>),
    Memory(Memory<'a>),
    DataTy(DataTy<'a>),
    Provenance(Provenance<'a>),
}

impl<'a> ArgKinded<'a> {
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

    pub fn equal(&self, nat_ctx: &NatCtx, other: &Self) -> NatEvalResult<bool> {
        match (self, other) {
            (ArgKinded::Ident(i), ArgKinded::Ident(o)) => Ok(i == o),
            (ArgKinded::Nat(n), ArgKinded::Nat(no)) => Ok(n.eval(nat_ctx)? == no.eval(nat_ctx)?),
            (ArgKinded::Provenance(r), ArgKinded::Provenance(ro)) => Ok(r == ro),
            (ArgKinded::DataTy(dty), ArgKinded::DataTy(dtyo)) => dty.equal(nat_ctx, dtyo),
            (ArgKinded::Memory(mem), ArgKinded::Memory(memo)) => Ok(mem == memo),
            _ => Ok(false),
        }
    }
}

#[span_derive(PartialEq, Eq, Hash)]
#[derive(Debug, Clone)]
pub struct PlaceExpr<'a> {
    pub pl_expr: PlaceExprKind<'a>,
    // FIXME misusing span_derive_ignore to ignore type on equality checks
    #[span_derive_ignore]
    pub ty: Option<&'a Ty<'a>>,
    #[span_derive_ignore]
    pub span: Option<Span>,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct View<'a> {
    pub name: Ident<'a>,
    pub gen_args: BumpVec<'a, ArgKinded<'a>>,
    pub args: BumpVec<'a, View<'a>>,
}

impl<'a> View<'a> {
    pub fn equal(&self, nat_ctx: &NatCtx, other: &View<'a>) -> NatEvalResult<bool> {
        if self.name.name != other.name.name {
            return Ok(false);
        }

        if self.gen_args.len() != other.gen_args.len() {
            return Ok(false);
        }

        for (ga, go) in self.gen_args.iter().zip(other.gen_args.iter()) {
            if !ga.equal(nat_ctx, go)? {
                return Ok(false);
            }
        }

        if self.args.len() != other.args.len() {
            return Ok(false);
        }

        for (v, vo) in self.args.iter().zip(other.args.iter()) {
            if !v.equal(nat_ctx, vo)? {
                return Ok(false);
            }
        }

        Ok(true)
    }
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
pub enum PlaceExprKind<'a> {
    View(&'a PlaceExpr<'a>, &'a View<'a>),
    // similar to a projection, but it projects an element for each provided execution resource
    // (similar to indexing)
    // p[[x]]
    Select(&'a PlaceExpr<'a>, &'a ExecExpr<'a>),
    // p.0 | p.1
    Proj(&'a PlaceExpr<'a>, usize),
    FieldProj(&'a PlaceExpr<'a>, &'a Ident<'a>),
    // *p
    Deref(&'a PlaceExpr<'a>),
    // Index into array, e.g., arr[i]
    Idx(&'a PlaceExpr<'a>, &'a Nat<'a>),
    // x
    Ident(Ident<'a>),
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum PlExprPathElem<'a> {
    View(View<'a>),
    Select(&'a ExecExpr<'a>),
    Proj(usize),
    FieldProj(Ident<'a>),
    Deref,
    Idx(&'a Nat<'a>),
    RangeSelec(&'a Nat<'a>, &'a Nat<'a>),
}

impl<'a> PlaceExpr<'a> {
    pub fn new(pl_expr: PlaceExprKind<'a>) -> Self {
        PlaceExpr {
            pl_expr,
            ty: None,
            span: None,
        }
    }

    pub fn with_span(pl_expr: PlaceExprKind<'a>, span: Span) -> Self {
        PlaceExpr {
            pl_expr,
            ty: None,
            span: Some(span),
        }
    }

    pub fn is_place(&self) -> bool {
        match &self.pl_expr {
            PlaceExprKind::Ident(_) => true,
            PlaceExprKind::Proj(ple, _) | PlaceExprKind::FieldProj(ple, _) => ple.is_place(),
            PlaceExprKind::Select(_, _)
            | PlaceExprKind::Deref(_)
            | PlaceExprKind::Idx(_, _)
            | PlaceExprKind::View(_, _) => false,
        }
    }

    // TODO refactor. Places are only needed during typechecking and codegen
    pub fn to_place(&self, arena: &'a bumpalo::Bump) -> Option<internal::Place> {
        if self.is_place() {
            Some(self.to_pl_ctx_and_most_specif_pl(arena).1)
        } else {
            None
        }
    }

    // TODO refactor see to_place
    pub fn to_pl_ctx_and_most_specif_pl(
        &'a self,
        arena: &'a bumpalo::Bump,
    ) -> (internal::PlaceCtx<'a>, internal::Place<'a>) {
        match &self.pl_expr {
            PlaceExprKind::Select(inner_ple, exec_idents) => {
                let (pl_ctx, pl) = inner_ple.to_pl_ctx_and_most_specif_pl(arena);
                (
                    internal::PlaceCtx::Select(arena.alloc(pl_ctx), exec_idents.clone()),
                    pl,
                )
            }
            PlaceExprKind::Deref(inner_ple) => {
                let (pl_ctx, pl) = inner_ple.to_pl_ctx_and_most_specif_pl(arena);
                (internal::PlaceCtx::Deref(arena.alloc(pl_ctx)), pl)
            }
            PlaceExprKind::View(inner_ple, view) => {
                let (pl_ctx, pl) = inner_ple.to_pl_ctx_and_most_specif_pl(arena);
                (
                    internal::PlaceCtx::View(arena.alloc(pl_ctx), view.clone()),
                    pl,
                )
            }
            PlaceExprKind::Proj(inner_ple, n) => {
                let (pl_ctx, mut pl) = inner_ple.to_pl_ctx_and_most_specif_pl(arena);
                match pl_ctx {
                    internal::PlaceCtx::Hole => {
                        pl.path.push(PathElem::Proj(*n));
                        (pl_ctx, internal::Place::new(pl.ident, pl.path))
                    }
                    _ => (internal::PlaceCtx::Proj(arena.alloc(pl_ctx), *n), pl),
                }
            }
            PlaceExprKind::FieldProj(inner_ple, field_name) => {
                let (pl_ctx, mut pl) = inner_ple.to_pl_ctx_and_most_specif_pl(arena);
                match pl_ctx {
                    internal::PlaceCtx::Hole => {
                        pl.path.push(PathElem::FieldProj(field_name.clone()));
                        (pl_ctx, internal::Place::new(pl.ident, pl.path))
                    }
                    _ => (
                        internal::PlaceCtx::FieldProj(arena.alloc(pl_ctx), **field_name),
                        pl,
                    ),
                }
            }
            PlaceExprKind::Idx(inner_ple, idx) => {
                let (pl_ctx, pl) = inner_ple.to_pl_ctx_and_most_specif_pl(arena);
                (
                    internal::PlaceCtx::Idx(arena.alloc(pl_ctx), idx.clone()),
                    pl,
                )
            }
            PlaceExprKind::Ident(ident) => (
                internal::PlaceCtx::Hole,
                internal::Place::new(ident.clone(), vec![]), // create a BumpVec here
            ),
        }
    }

    pub fn equiv(&'_ self, arena: &'a bumpalo::Bump, place: &'_ internal::Place) -> bool {
        if let (internal::PlaceCtx::Hole, pl) = self.to_pl_ctx_and_most_specif_pl(arena) {
            &pl == place
        } else {
            false
        }
    }

    pub fn as_ident_and_path(&self) -> (Ident<'a>, Vec<PlExprPathElem<'a>>) {
        fn as_ident_and_path_rec(
            pl_expr: &PlaceExpr,
            mut path: BumpVec<PlExprPathElem<'a>>,
        ) -> (Ident<'a>, BumpVec<PlExprPathElem<'a>>) {
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
                    path.push(PlExprPathElem::View(**view)); // formerly as_ref().clone() ? Can that just work with double dereferencing?
                    as_ident_and_path_rec(inner_ple, path)
                }
                PlaceExprKind::Proj(inner_ple, n) => {
                    path.push(PlExprPathElem::Proj(*n));
                    as_ident_and_path_rec(inner_ple, path)
                }
                PlaceExprKind::FieldProj(inner_ple, ident) => {
                    path.push(PlExprPathElem::FieldProj(**ident));  // formerly as_ref().clone() ? Can that just work with double dereferencing?
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
pub struct ExecExpr<'a> {
    pub exec: &'a ExecExprKind<'a>,
    #[span_derive_ignore]
    pub ty: Option<&'a ExecTy<'a>>,
    #[span_derive_ignore]
    pub span: Option<Span>,
}
impl<'a> ExecExpr<'a> {
    pub fn new(arena: &'a bumpalo::Bump, exec: ExecExprKind<'a>) -> Self {
        Self {
            exec: arena.alloc(exec),
            ty: None,
            span: None,
        }
    }

    // TODO how does this relate to is_prefix_of. Refactor.
    pub fn is_sub_exec_of(&self, exec: &ExecExpr) -> bool {
        if self.exec.path.len() > exec.exec.path.len() {
            return self.exec.path[..exec.exec.path.len()] == exec.exec.path[..];
        }
        false
    }

    pub fn remove_last_distrib(&self, arena: &'a bumpalo::Bump) -> ExecExpr {
        let last_distrib_pos = self
            .exec
            .path
            .iter()
            .rposition(|e| matches!(e, ExecPathElem::ForAll(_)));
        
        // What did i do here?
        let removed_distrib_path = if let Some(ldp) = last_distrib_pos {
            let mut vec = BumpVec::new_in(arena);
            // self.exec.path[..ldp].to_vec() --> changed this to BumpVec
            vec.extend_from_slice(&self.exec.path[..ldp]);
            vec
        } else {
            //vec![] --> changed this to BumpVec
            BumpVec::new_in(arena)
        };
        
        ExecExpr::new(arena, 
            ExecExprKind::with_path(
                self.exec.base.clone(),
                removed_distrib_path,
            )
        )
    }

    /** Kind of idea how to do it 
    pub fn remove_last_distrib(&self, arena: &'a Bump) -> ExecExpr<'a> {
        let last_distrib_pos = self
            .exec
            .path
            .iter()
            .rposition(|e| matches!(e, ExecPathElem::ForAll(_)));

        let removed_path = match last_distrib_pos {
            Some(pos) => &self.exec.path[..pos],
            None => &[],
        };

        let exec_kind = ExecExprKind::with_path(self.exec.base.clone(), removed_path.iter().cloned(), arena);
        ExecExpr::new(arena, exec_kind)
    }
    */

    pub fn equal(&self, nat_ctx: &NatCtx, other: &Self) -> NatEvalResult<bool> {
        match (&self.exec.base, &other.exec.base) {
            (BaseExec::Ident(i), BaseExec::Ident(o)) => {
                if i != o {
                    return Ok(false);
                }
            }
            (BaseExec::CpuThread, BaseExec::CpuThread) => (),
            (BaseExec::GpuGrid(gdim, bdim), BaseExec::GpuGrid(gdimo, bdimo)) => {
                if !(gdim.equal(nat_ctx, gdimo)? && bdim.equal(nat_ctx, bdimo)?) {
                    return Ok(false);
                }
            }
            _ => return Ok(false),
        }
        if self.exec.path.len() != other.exec.path.len() {
            return Ok(false);
        }
        for path_elems in self.exec.path.iter().zip(&other.exec.path) {
            match path_elems {
                (ExecPathElem::ToWarps, ExecPathElem::ToWarps) => (),
                (ExecPathElem::ForAll(d), ExecPathElem::ForAll(o)) => {
                    if d != o {
                        return Ok(false);
                    }
                }
                (ExecPathElem::ToThreads(d), ExecPathElem::ToThreads(o)) => {
                    if d != o {
                        return Ok(false);
                    }
                }
                (ExecPathElem::TakeRange(r), ExecPathElem::TakeRange(ro)) => {
                    if !(r.split_dim == ro.split_dim
                        && r.left_or_right == ro.left_or_right
                        && r.pos.eval(nat_ctx)? == ro.pos.eval(nat_ctx)?)
                    {
                        return Ok(false);
                    }
                }
                _ => return Ok(false),
            }
        }
        Ok(true)
    }
}

#[test]
fn equal_exec_exprs() {
    let arena = Bump::new();

    let exec1 = ExecExpr::new(
        &arena,
        ExecExprKind::with_path(
            BaseExec::Ident(Ident::new(&arena, "grid")),
            bumpalo::collections::Vec::from_iter_in(
                [ExecPathElem::ForAll(DimCompo::X)],
                &arena
            )
        )
    );

    let exec2 = ExecExpr::new(
        &arena,
        ExecExprKind::with_path(
            BaseExec::Ident(Ident::new(&arena, "grid")),
            bumpalo::collections::Vec::from_iter_in(
                [ExecPathElem::ForAll(DimCompo::X)],
                &arena
            )
        )
    );

    assert_eq!(exec1, exec2, "Unequal execs that should be equal");
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub enum LeftOrRight {
    Left,
    Right,
}

impl fmt::Display for LeftOrRight {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LeftOrRight::Left => write!(f, "left"),
            LeftOrRight::Right => write!(f, "right"),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct TakeRange<'a> {
    pub split_dim: DimCompo,
    pub pos: Nat<'a>,
    pub left_or_right: LeftOrRight,
}

impl<'a> TakeRange<'a> {
    pub fn new(split_dim: DimCompo, pos: Nat<'a>, proj: LeftOrRight) -> Self {
        TakeRange {
            split_dim,
            pos,
            left_or_right: proj,
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct ExecExprKind<'a> {
    pub base: BaseExec<'a>,
    pub path: BumpVec<'a, ExecPathElem<'a>>,
}

impl<'a> ExecExprKind<'a> {
    pub fn new(arena: &'a bumpalo::Bump, base: BaseExec<'a>) -> Self {
        ExecExprKind {
            base,
            path: BumpVec::new_in(arena),
        }
    }

    pub fn with_path(base: BaseExec<'a>, path: BumpVec<'a, ExecPathElem<'a>>) -> Self {
        ExecExprKind { base, path }
    }

    /** 
    pub fn with_path(base: BaseExec, path: impl IntoIterator<Item = ExecPathElem<'a>>, arena: &'a Bump) -> Self {
        let mut bump_vec = BumpVec::new_in(arena);
        bump_vec.extend(path);
        Self { base, path: bump_vec }
    }*/


    pub fn split_proj(
        mut self,
        arena: &'a bumpalo::Bump,
        dim_compo: DimCompo,
        pos: Nat,
        proj: LeftOrRight,
    ) -> Self {
        self.path.push(ExecPathElem::TakeRange(
            arena.alloc(TakeRange::new(dim_compo, pos<'a>, proj)),
        ));
        self
    }

    pub fn forall(mut self, dim_compo: DimCompo) -> Self {
        self.path.push(ExecPathElem::ForAll(dim_compo));
        self
    }

    pub fn active_distrib_dim(&self) -> Option<DimCompo> {
        for e in self.path.iter().rev() {
            if let ExecPathElem::ForAll(dim) = e {
                return Some(*dim);
            }
        }
        None
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum BaseExec<'a> {
    Ident(Ident<'a>),
    CpuThread,
    GpuGrid(Dim<'a>, Dim<'a>),
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum ExecPathElem<'a> {
    TakeRange(&'a TakeRange<'a>),
    ForAll(DimCompo),
    ToWarps,
    ToThreads(DimCompo),
}

// ExecTy
// fn size(DimCompo) -> usize
// fn take_range(DimCompo, Nat) -> ExecTy
// fn elem_type(DimCompo) -> ExecTy
#[span_derive(PartialEq, Eq, Hash)]
#[derive(Debug, Clone)]
pub struct ExecTy<'a> {
    pub ty: ExecTyKind<'a>,
    #[span_derive_ignore]
    pub span: Option<Span>,
}

impl<'a> ExecTy<'a> {
    pub fn new(exec: ExecTyKind<'a>) -> Self {
        ExecTy {
            ty: exec,
            span: None,
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum ExecTyKind<'a> {
    CpuThread,
    GpuThread,
    GpuWarp,
    GpuBlock(Dim<'a>),
    GpuGrid(Dim<'a>, Dim<'a>),
    GpuToThreads(Dim<'a>, &'a ExecTy<'a>),
    GpuThreadGrp(Dim<'a>),
    GpuWarpGrp(Nat<'a>),
    GpuBlockGrp(Dim<'a>, Dim<'a>),
    Any,
}

#[span_derive(PartialEq, Eq, Hash)]
#[derive(Debug, Clone)]
pub struct Ty<'a> {
    pub ty: TyKind<'a>,
    #[span_derive_ignore]
    pub span: Option<Span>,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct ParamSig<'a> {
    pub exec_expr: ExecExpr<'a>,
    pub ty: &'a Ty<'a>,
}

impl<'a> ParamSig<'a> {
    pub fn new(exec_expr: ExecExpr<'a>, ty: &'a Ty<'a>) -> Self {
        ParamSig { exec_expr, ty }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct FnTy<'a> {
    pub generics: BumpVec<'a, IdentKinded<'a>>,
    pub generic_exec: Option<IdentExec<'a>>,
    pub param_sigs: BumpVec<'a, ParamSig<'a>>,
    pub exec: ExecExpr<'a>,
    pub ret_ty: &'a Ty<'a>,
    pub nat_constrs: BumpVec<'a, NatConstr<'a>>,
}

impl<'a> FnTy<'a> {
    pub fn new(
        arena: &'a Bump,
        generics: impl IntoIterator<Item = IdentKinded<'a>>,
        generic_exec: Option<IdentExec<'a>>,
        param_sigs: impl IntoIterator<Item = ParamSig<'a>>,
        exec: ExecExpr<'a>,
        ret_ty: &'a Ty<'a>,
        nat_constrs: impl IntoIterator<Item = NatConstr<'a>>,
    ) -> Self {
        let mut generics_vec = BumpVec::new_in(arena);
        generics_vec.extend(generics);

        let mut param_vec = BumpVec::new_in(arena);
        param_vec.extend(param_sigs);

        let mut nat_vec = BumpVec::new_in(arena);
        nat_vec.extend(nat_constrs);

        FnTy {
            generics: generics_vec,
            generic_exec,
            param_sigs: param_vec,
            exec,
            ret_ty: arena.alloc(ret_ty),
            nat_constrs: nat_vec,
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum NatConstr<'a> {
    True,
    Eq(Box<Nat<'a>>, Box<Nat<'a>>),
    Lt(Box<Nat<'a>>, Box<Nat<'a>>),
    And(Box<NatConstr<'a>>, Box<NatConstr<'a>>),
    Or(Box<NatConstr<'a>>, Box<NatConstr<'a>>),
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum TyKind<'a> {
    Data(&'a DataTy<'a>),
    // <x:k,..>(ty..) -[x:exec]-> ty
    FnTy(&'a FnTy<'a>),
}

// TODO remove
#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub enum Constraint {
    Copyable,
}

impl<'a> Ty<'a> {
    pub fn new(ty: TyKind<'a>) -> Self {
        Ty { ty, span: None }
    }

    pub fn with_span(ty: TyKind<'a>, span: Span) -> Ty<'a> {
        Ty {
            ty,
            span: Some(span),
        }
    }

    pub fn dty(&self) -> &'a DataTy<'a> {
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
                    .param_sigs
                    .iter()
                    .any(|param_sig| param_sig.ty.contains_ref_to_prv(prv_val_name))
                    || fn_ty.ret_ty.contains_ref_to_prv(prv_val_name)
            }
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct Dim1d<'a>(pub Nat<'a>);
#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct Dim2d<'a>(pub Nat<'a>, pub Nat<'a>);
#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct Dim3d<'a>(pub Nat<'a>, pub Nat<'a>, pub Nat<'a>);
#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum Dim<'a> {
    XYZ(&'a Dim3d<'a>),
    XY(&'a Dim2d<'a>),
    XZ(&'a Dim2d<'a>),
    YZ(&'a Dim2d<'a>),
    X(&'a Dim1d<'a>),
    Y(&'a Dim1d<'a>),
    Z(&'a Dim1d<'a>),
}

impl<'a> Dim<'a> {
    pub fn new_3d(arena: &'a Bump, n1: Nat<'a>, n2:  Nat<'a>, n3:  Nat<'a>) -> Self {
        Dim::XYZ(arena.alloc(Dim3d(n1, n2, n3)))
    }

    pub fn new_2d<F: Fn(&'a Dim2d) -> Self>(arena: &'a Bump, constr: F, n1:  Nat<'a>, n2: Nat<'a>) -> Self {
        constr(arena.alloc(Dim2d(n1, n2)))
    }
    
    pub fn new_1d<F: Fn(&'a Dim1d) -> Self>(arena: &'a Bump, constr: F, n:  Nat<'a>) -> Self {
        constr(arena.alloc(Dim1d(n)))
    }

    pub fn equal(&self, nat_ctx: &NatCtx, other: &Self) -> NatEvalResult<bool> {
        match (self, other) {
            (Dim::XYZ(d), Dim::XYZ(o)) => Ok(d.0.eval(nat_ctx)? == o.0.eval(nat_ctx)?
                && d.1.eval(nat_ctx)? == o.1.eval(nat_ctx)?
                && d.2.eval(nat_ctx)? == o.2.eval(nat_ctx)?),
            (Dim::XY(d), Dim::XY(o)) | (Dim::XZ(d), Dim::XZ(o)) | (Dim::YZ(d), Dim::YZ(o)) => {
                Ok(d.0.eval(nat_ctx)? == o.0.eval(nat_ctx)?
                    && d.1.eval(nat_ctx)? == o.1.eval(nat_ctx)?)
            }
            (Dim::X(d), Dim::X(o)) | (Dim::Y(d), Dim::Y(o)) | (Dim::Z(d), Dim::Z(o)) => {
                Ok(d.0.eval(nat_ctx)? == o.0.eval(nat_ctx)?)
            }
            _ => Ok(false),
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Hash, Debug, Copy, Clone)]
pub enum DimCompo {
    X,
    Y,
    Z,
}

#[span_derive(PartialEq, Eq, Hash)]
#[derive(Debug, Clone)]
pub struct DataTy<'a> {
    pub dty: DataTyKind<'a>,
    // TODO remove with introduction of traits
    pub constraints: BumpVec<'a, Constraint>,
    #[span_derive_ignore]
    pub span: Option<Span>,
}

impl<'a> DataTy<'a> {
    pub fn new_in(bump: &'a bumpalo::Bump, dty: DataTyKind<'a>) -> Self {
        DataTy {
            dty,
            constraints: BumpVec::new_in(bump),
            span: None,
        }
    }

    pub fn with_constr(
        bump: &'a bumpalo::Bump,
        dty: DataTyKind<'a>,
        constraints: impl IntoIterator<Item = Constraint>,
    ) -> Self {
        let mut v = BumpVec::new_in(bump);
        v.extend(constraints);
        DataTy {
            dty,
            constraints: v,
            span: None,
        }
    }

    pub fn with_span(bump: &'a bumpalo::Bump, dty: DataTyKind<'a>, span: Span) -> Self {
        DataTy {
            dty,
            constraints: BumpVec::new_in(bump),
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
            | Atomic(_)
            | Ident(_)
            | Ref(_)
            | At(_, _)
            | Array(_, _)
            | ArrayShape(_, _) => true,
            Tuple(elem_tys) => elem_tys
                .iter()
                .fold(true, |acc, dty| acc & dty.is_fully_alive()),
            Struct(struct_decl) => struct_decl
                .fields
                .iter()
                .fold(true, |acc, (_, dty)| acc & dty.is_fully_alive()),
            Dead(_) => false,
        }
    }

    pub fn occurs_in(&self, dty: &DataTy) -> bool {
        if self == dty {
            return true;
        }
        match &dty.dty {
            DataTyKind::Scalar(_) | DataTyKind::Ident(_) => false,
            DataTyKind::Dead(_) => panic!("unexpected"),
            DataTyKind::Atomic(aty) => &self.dty == &DataTyKind::Atomic(aty.clone()),
            DataTyKind::Ref(reff) => self.occurs_in(&reff.dty),
            DataTyKind::RawPtr(elem_dty) => self.occurs_in(elem_dty),
            DataTyKind::Tuple(elem_dtys) => {
                let mut found = false;
                for elem_dty in elem_dtys {
                    found = self.occurs_in(elem_dty);
                }
                found
            }
            DataTyKind::Struct(struct_decl) => {
                let mut found = false;
                for (_, dty) in &struct_decl.fields {
                    found = self.occurs_in(dty)
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
            Scalar(_) | Atomic(_) | Ident(_) | Dead(_) => false,
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
            Struct(struct_decl) => struct_decl
                .fields
                .iter()
                .any(|(_, dty)| dty.contains_ref_to_prv(prv_val_name)),
        }
    }

    pub fn equal(&self, nat_ctx: &NatCtx, other: &Self) -> NatEvalResult<bool> {
        match (&self.dty, &other.dty) {
            (DataTyKind::Ident(i), DataTyKind::Ident(o)) => Ok(i == o),
            (DataTyKind::Tuple(dtys), DataTyKind::Tuple(dtyos)) => {
                for (d, o) in dtys.iter().zip(dtyos) {
                    if !d.equal(nat_ctx, o)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (DataTyKind::Ref(ref_dty), DataTyKind::Ref(ref_dtyo)) => Ok(ref_dty.own
                == ref_dtyo.own
                && ref_dty.rgn == ref_dtyo.rgn
                && ref_dty.mem == ref_dtyo.mem
                && ref_dty.dty.equal(nat_ctx, &ref_dtyo.dty)?),
            (DataTyKind::Array(dty, n), DataTyKind::Array(dtyo, no))
            | (DataTyKind::ArrayShape(dty, n), DataTyKind::ArrayShape(dtyo, no)) => {
                Ok(dty.equal(nat_ctx, dtyo)? && n.eval(nat_ctx)? == no.eval(nat_ctx)?)
            }
            (DataTyKind::At(dty, mem), DataTyKind::At(dtyo, memo)) => {
                Ok(dty.equal(nat_ctx, dtyo)? && mem == memo)
            }
            (DataTyKind::Struct(struct_decl), DataTyKind::Struct(struct_declo)) => {
                Ok(struct_decl.ident == struct_declo.ident)
            }
            (DataTyKind::Atomic(aty), DataTyKind::Atomic(atyo)) => Ok(aty == atyo),
            (DataTyKind::Scalar(sty), DataTyKind::Scalar(styo)) => Ok(sty == styo),
            _ => Ok(false),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct RefDty<'a> {
    pub rgn: Provenance<'a>,
    pub own: Ownership,
    pub mem: Memory<'a>,
    pub dty: &'a DataTy<'a>,
}

impl<'a> RefDty<'a> {
    pub fn new(
        bump: &'a Bump,
        rgn: Provenance<'a>,
        own: Ownership,
        mem: Memory<'a>,
        dty: DataTy<'a>,
    ) -> Self {
        RefDty {
            rgn,
            own,
            mem,
            dty: bump.alloc(dty),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum DataTyKind<'a> {
    Ident(Ident<'a>),
    Scalar(ScalarTy),
    Atomic(AtomicTy),
    Array(&'a DataTy<'a>, Nat<'a>),
    ArrayShape(&'a DataTy<'a>, Nat<'a>),
    Tuple(BumpVec<'a, DataTy<'a>>),
    Struct(&'a StructDecl<'a>),
    At(&'a DataTy<'a>, Memory<'a>),
    Ref(&'a RefDty<'a>),
    RawPtr(&'a DataTy<'a>),
    //Range,
    // TODO remove. This is an attribute of a typing context entry, not the type.
    // Only for type checking purposes.
    Dead(&'a DataTy<'a>),
}

#[derive(PartialEq, Eq, Hash, Debug, Copy, Clone)]
pub enum ScalarTy {
    Unit,
    U8,
    U32,
    U64,
    I32,
    I64,
    F32,
    F64,
    Bool,
    Gpu,
}

#[derive(PartialEq, Eq, Hash, Debug, Copy, Clone)]
pub enum AtomicTy {
    AtomicU32,
    AtomicI32,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum Provenance<'a> {
    Value(String),
    Ident(Ident<'a>),
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum Memory<'a> {
    CpuMem,
    GpuGlobal,
    GpuShared,
    GpuLocal,
    Ident(Ident<'a>),
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct PrvRel<'a> {
    pub longer: Ident<'a>,
    pub shorter: Ident<'a>,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct IdentKinded<'a> {
    pub ident: Ident<'a>,
    pub kind: Kind,
}

impl<'a> IdentKinded<'a> {
    pub fn new(ident: &Ident<'a>, kind: Kind) -> Self {
        IdentKinded {
            ident: ident.clone(),
            kind,
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum NatRange<'a> {
    Simple { lower: Nat<'a>, upper: Nat<'a> },
    Halved { upper: Nat<'a> },
    Doubled { upper: Nat<'a> },
}

impl<'a> NatRange<'a> {
    pub fn lift(&self, arena: &'a Bump, nat_ctx: &NatCtx) -> NatEvalResult<NatRangeIter> {
        let range_iter = match self {
            NatRange::Simple { lower, upper } => {
                let lower = lower.eval(nat_ctx)?;
                let upper = upper.eval(nat_ctx)?;
                NatRangeIter::new(
                    lower,
                    arena.alloc(|x| x + 1),
                    arena.alloc(move |c| c >= upper),
                )
            }
            NatRange::Halved { upper } => {
                let upper = upper.eval(nat_ctx)?;
                NatRangeIter::new(upper, arena.alloc(|x| x / 2), arena.alloc(|c| c == 0))
            }
            NatRange::Doubled { upper } => {
                let upper = upper.eval(nat_ctx)?;
                NatRangeIter::new(1, arena.alloc(|x| x * 2), arena.alloc(move |c| c >= upper))
            }
        };
        Ok(range_iter)
    }
}

pub struct NatRangeIter<'a> {
    current: usize,
    // go from current to next value
    step_fun: &'a dyn Fn(usize) -> usize,
    // determine whether the current value is still within range
    end_cond: &'a dyn Fn(usize) -> bool,
}

impl<'a> NatRangeIter<'a> {
    fn new(
        start: usize,
        step_fun: &'a dyn Fn(usize) -> usize,
        end_cond: &'a dyn Fn(usize) -> bool,
    ) -> Self {
        NatRangeIter {
            current: start,
            step_fun,
            end_cond,
        }
    }
}

impl<'a> Iterator for NatRangeIter<'a> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        self.current = (self.step_fun)(self.current);

        if !(self.end_cond)(self.current) {
            Some(self.current)
        } else {
            None
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum Nat<'a> {
    Ident(Ident<'a>),
    Lit(usize),
    ThreadIdx(DimCompo),
    BlockIdx(DimCompo),
    BlockDim(DimCompo),
    WarpGrpIdx,
    WarpIdx,
    LaneIdx,
    // Dummy that is always 0, i.e. equivalent to Lit(0)
    GridIdx,
    BinOp(BinOpNat, Box<Nat<'a>>, Box<Nat<'a>>),
    // Use Box<[Nat]> to safe 8 bytes compared to Vec<Nat>
    App(Ident<'a>, Box<[Nat<'a>]>),
}

pub struct NatCtx {
    frames: Vec<Vec<(Box<str>, usize)>>,
}

impl NatCtx {
    pub fn new() -> Self {
        NatCtx {
            frames: vec![vec![]],
        }
    }

    pub fn with_frame(frame: Vec<(Box<str>, usize)>) -> Self {
        let mut ctx = NatCtx { frames: vec![] };
        ctx.push_frame(frame);
        ctx
    }

    pub fn append(&mut self, nat_name: &str, val: usize) {
        self.frames
            .last_mut()
            .unwrap()
            .push((Box::from(nat_name), val))
    }

    pub fn find(&self, name: &str) -> Option<usize> {
        self.frames.iter().flatten().rev().find_map(|(i, n)| {
            if i.as_ref() == name {
                Some(*n)
            } else {
                None
            }
        })
    }

    pub fn push_empty_frame(&mut self) -> &mut Self {
        self.frames.push(vec![]);
        self
    }

    fn push_frame(&mut self, frame: Vec<(Box<str>, usize)>) -> &mut Self {
        self.frames.push(frame);
        self
    }

    pub fn pop_frame(&mut self) -> &mut Self {
        self.frames.pop().expect("There must always be a scope.");
        self
    }
}

#[derive(Debug)]
pub struct NatEvalError<'a> {
    unevaluable: Nat<'a>,
}

pub type NatEvalResult<'a, T> = Result<T, NatEvalError<'a>>;

impl<'a> Nat<'a> {
    pub fn eval(&self, nat_ctx: &NatCtx) -> NatEvalResult<usize> {
        match self {
            Nat::GridIdx
            | Nat::BlockIdx(_)
            | Nat::BlockDim(_)
            | Nat::ThreadIdx(_)
            | Nat::WarpGrpIdx
            | Nat::WarpIdx
            | Nat::LaneIdx => Err(NatEvalError {
                unevaluable: self.clone(),
            }),
            Nat::Ident(i) => {
                if let Some(n) = nat_ctx.find(&i.name) {
                    Ok(n)
                } else {
                    Err(NatEvalError {
                        unevaluable: self.clone(),
                    })
                }
            }
            Nat::Lit(n) => Ok(*n),
            Nat::BinOp(op, l, r) => match op {
                BinOpNat::Add => Ok(l.eval(nat_ctx)? + r.eval(nat_ctx)?),
                BinOpNat::Sub => Ok(l.eval(nat_ctx)? - r.eval(nat_ctx)?),
                BinOpNat::Mul => Ok(l.eval(nat_ctx)? * r.eval(nat_ctx)?),
                BinOpNat::Div => Ok(l.eval(nat_ctx)? / r.eval(nat_ctx)?),
                BinOpNat::Mod => Ok(l.eval(nat_ctx)? % r.eval(nat_ctx)?),
            },
            Nat::App(_, _) => unimplemented!(),
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
    static_assert_size!(DataTy, 104);
    static_assert_size!(DataTyKind, 64);
    static_assert_size!(ExecExpr, 32);
    static_assert_size!(ExecExprKind, 64);
    static_assert_size!(ExecPathElem, 16);
    static_assert_size!(ExecTy, 64);
    static_assert_size!(ExecTyKind, 48);
    static_assert_size!(Expr, 96);
    static_assert_size!(ExprKind, 72);
    static_assert_size!(FunDef, 192);
    static_assert_size!(Ident, 32); // maybe too large?
    static_assert_size!(IdentExec, 40);
    static_assert_size!(Lit, 16);
    static_assert_size!(Memory, 32);
    static_assert_size!(Nat, 48);
    static_assert_size!(ParamDecl, 104);
    static_assert_size!(Pattern, 40);
    static_assert_size!(PlaceExpr, 56);
    static_assert_size!(PlaceExprKind, 32);
    static_assert_size!(ScalarTy, 1);
    static_assert_size!(Ty, 32);
    static_assert_size!(TyKind, 16);
}
