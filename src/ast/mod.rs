use std::fmt;

use crate::ast::internal::PathElem;
use descend_derive::span_derive;
pub use span::*;

use crate::arena_ast;
use crate::parser::SourceCode;
use bumpalo::{collections::CollectIn, collections::Vec as BumpVec, Bump};

pub mod internal;

pub mod printer;
mod span;
pub mod utils;
pub mod visit;
pub mod visit_mut;

#[derive(Clone, Debug)]
pub struct CompilUnit<'a> {
    pub items: Vec<Item>,
    pub source: &'a SourceCode<'a>,
}

impl<'a> CompilUnit<'a> {
    pub fn new(items: Vec<Item>, source: &'a SourceCode<'a>) -> Self {
        CompilUnit { items, source }
    }
}

#[derive(Debug, Clone)]
pub enum Item {
    FunDef(Box<FunDef>),
    FunDecl(Box<FunDecl>),
    StructDecl(Box<StructDecl>),
}

impl Item {
    pub fn into_arena<'a>(self, arena: &'a Bump) -> arena_ast::Item<'a> {
        match self {
            Item::FunDef(f) => {
                let arena_f = f.into_arena(arena);
                arena_ast::Item::FunDef(arena.alloc(arena_f))
            }
            Item::FunDecl(f) => {
                let arena_fd = f.into_arena(arena);
                arena_ast::Item::FunDecl(arena.alloc(arena_fd))
            }
            Item::StructDecl(s) => {
                let arena_s = s.into_arena(arena);
                arena_ast::Item::StructDecl(arena.alloc(arena_s))
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunDecl {
    pub ident: Ident,
    pub generic_params: Vec<IdentKinded>,
    pub generic_exec: Option<IdentExec>,
    pub param_decls: Vec<ParamDecl>,
    pub ret_dty: Box<DataTy>,
    pub exec: ExecExpr,
    pub prv_rels: Vec<PrvRel>,
}

impl FunDecl {
    pub fn fn_ty(&self) -> FnTy {
        let param_sigs: Vec<_> = self
            .param_decls
            .iter()
            .map(|p_decl| {
                ParamSig::new(
                    p_decl.exec_expr.as_ref().unwrap_or(&self.exec).clone(),
                    p_decl.ty.as_ref().unwrap().clone(),
                )
            })
            .collect();
        FnTy {
            generics: self.generic_params.clone(),
            generic_exec: self.generic_exec.clone(),
            param_sigs,
            exec: self.exec.clone(),
            ret_ty: Box::new(Ty::new(TyKind::Data(self.ret_dty.clone()))),
            nat_constrs: vec![],
        }
    }

    pub fn into_arena<'a>(self: Box<Self>, arena: &'a Bump) -> arena_ast::FunDecl<'a> {
        let generic_params = self
            .generic_params
            .into_iter()
            .map(|g| g.into_arena(arena))
            .collect_in(arena);

        let param_decls = self
            .param_decls
            .into_iter()
            .map(|p| p.into_arena(arena))
            .collect_in(arena);

        let prv_rels = self
            .prv_rels
            .into_iter()
            .map(|r| r.into_arena(arena))
            .collect_in(arena);

        arena_ast::FunDecl {
            ident: self.ident.into_arena(arena),
            generic_params,
            generic_exec: self.generic_exec.map(|g| g.into_arena(arena)),
            param_decls,
            ret_dty: arena.alloc(self.ret_dty.into_arena(arena)),
            exec: self.exec.into_arena(arena),
            prv_rels,
        }
    }
}

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub struct StructDecl {
    pub ident: Ident,
    pub generic_params: Vec<IdentKinded>,
    pub fields: Vec<(Ident, DataTy)>,
}

impl StructDecl {
    pub fn into_arena<'a>(self: Box<Self>, arena: &'a Bump) -> arena_ast::StructDecl<'a> {
        let generic_params = self
            .generic_params
            .into_iter()
            .map(|gp| gp.into_arena(arena))
            .collect_in(arena);

        let fields = self
            .fields
            .into_iter()
            .map(|(i, dty)| (i.into_arena(arena), dty.into_arena(arena)))
            .collect_in(arena);

        arena_ast::StructDecl {
            ident: self.ident.into_arena(arena),
            generic_params,
            fields,
        }
    }
}

// TODO refactor to make use of FunDecl
#[derive(Debug, Clone, PartialEq)]
pub struct FunDef {
    pub ident: Ident,
    pub generic_params: Vec<IdentKinded>,
    pub generic_exec: Option<IdentExec>,
    pub param_decls: Vec<ParamDecl>,
    pub ret_dty: Box<DataTy>,
    pub exec: ExecExpr,
    pub prv_rels: Vec<PrvRel>,
    pub body: Box<Block>,
}

impl FunDef {
    pub fn fn_ty(&self) -> FnTy {
        let param_sigs: Vec<_> = self
            .param_decls
            .iter()
            .map(|p_decl| {
                ParamSig::new(
                    p_decl.exec_expr.as_ref().unwrap_or(&self.exec).clone(),
                    p_decl.ty.as_ref().unwrap().clone(),
                )
            })
            .collect();
        FnTy {
            generics: self.generic_params.clone(),
            generic_exec: self.generic_exec.clone(),
            param_sigs,
            exec: self.exec.clone(),
            ret_ty: Box::new(Ty::new(TyKind::Data(self.ret_dty.clone()))),
            nat_constrs: vec![],
        }
    }

    pub fn into_arena<'a>(self: Box<Self>, arena: &'a Bump) -> arena_ast::FunDef<'a> {
        let generic_params = self
            .generic_params
            .into_iter()
            .map(|g| g.into_arena(arena))
            .collect_in(arena);

        let generic_exec = self.generic_exec.map(|g| g.into_arena(arena));

        let param_decls = self
            .param_decls
            .into_iter()
            .map(|p| p.into_arena(arena))
            .collect_in(arena);

        let ret_dty = arena.alloc(self.ret_dty.into_arena(arena));

        let prv_rels = self
            .prv_rels
            .into_iter()
            .map(|r| r.into_arena(arena))
            .collect_in(arena);

        let body = arena.alloc(self.body.into_arena(arena));

        arena_ast::FunDef {
            ident: self.ident.into_arena(arena),
            generic_params,
            generic_exec,
            param_decls,
            ret_dty,
            exec: self.exec.into_arena(arena),
            prv_rels,
            body,
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

    pub fn into_arena<'a>(self, arena: &'a Bump) -> arena_ast::IdentExec<'a> {
        arena_ast::IdentExec {
            ident: self.ident.into_arena(arena),
            ty: arena.alloc(self.ty.into_arena(arena)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParamDecl {
    pub ident: Ident,
    pub ty: Option<Ty>,
    pub mutbl: Mutability,
    pub exec_expr: Option<ExecExpr>,
}

impl ParamDecl {
    pub fn into_arena<'a>(self, arena: &'a Bump) -> arena_ast::ParamDecl<'a> {
        let ty = self.ty.map(|t| &*arena.alloc(t.into_arena(arena)));
        let exec_expr = self
            .exec_expr
            .map(|e| arena.alloc(e.into_arena(arena)).clone());

        arena_ast::ParamDecl {
            ident: self.ident.into_arena(arena),
            ty,
            mutbl: self.mutbl.into_arena(),
            exec_expr,
        }
    }
}

#[span_derive(PartialEq)]
#[derive(Debug, Clone)]
pub struct Expr {
    pub expr: ExprKind,
    // FIXME misusing span_derive_ignore to ignore type on equality checks
    #[span_derive_ignore]
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

    pub fn into_arena<'a>(self, arena: &'a Bump) -> arena_ast::Expr<'a> {
        arena_ast::Expr {
            expr: self.expr.into_arena(arena),
            ty: self.ty.map(|t| &*arena.alloc(t.into_arena(arena))),
            span: self.span,
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
    pub sched_exec: Box<ExecExpr>,
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
            sched_exec: Box::new(sched_exec),
            body: Box::new(body),
        }
    }

    pub fn into_arena<'a>(self, arena: &'a Bump) -> arena_ast::Sched<'a> {
        arena_ast::Sched {
            dim: self.dim.into_arena(),
            inner_exec_ident: self.inner_exec_ident.map(|id| id.into_arena(arena)),
            sched_exec: arena.alloc(self.sched_exec.into_arena(arena)),
            body: arena.alloc(self.body.into_arena(arena)),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct Split {
    pub dim_compo: DimCompo,
    pub pos: Nat,
    pub split_exec: Box<ExecExpr>,
    pub branch_idents: Vec<Ident>,
    pub branch_bodies: Vec<Expr>,
}

impl Split {
    pub fn new(
        dim_compo: DimCompo,
        pos: Nat,
        split_exec: ExecExpr,
        branch_idents: Vec<Ident>,
        branch_bodies: Vec<Expr>,
    ) -> Self {
        Split {
            dim_compo,
            pos,
            split_exec: Box::new(split_exec),
            branch_idents,
            branch_bodies,
        }
    }

    pub fn into_arena<'a>(self, arena: &'a Bump) -> arena_ast::Split<'a> {
        let mut branch_idents = bumpalo::collections::Vec::new_in(arena);
        branch_idents.extend(
            self.branch_idents
                .into_iter()
                .map(|ident| ident.into_arena(arena)),
        );

        let mut branch_bodies = bumpalo::collections::Vec::new_in(arena);
        branch_bodies.extend(
            self.branch_bodies
                .into_iter()
                .map(|expr| expr.into_arena(arena)),
        );

        arena_ast::Split {
            dim_compo: self.dim_compo.into_arena(),
            pos: self.pos.into_arena(arena),
            split_exec: arena.alloc(self.split_exec.into_arena(arena)),
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

    pub fn into_arena<'a>(self, arena: &'a Bump) -> arena_ast::Block<'a> {
        let prvs: bumpalo::collections::Vec<'a, String> = self.prvs.into_iter().collect_in(arena);

        arena_ast::Block {
            prvs,
            body: arena.alloc(self.body.into_arena(arena)),
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
    pub fun_ident: Box<Ident>,
    pub gen_args: Vec<ArgKinded>,
    pub args: Vec<Expr>,
}

impl AppKernel {
    pub fn into_arena<'a>(&self, arena: &'a Bump) -> arena_ast::AppKernel<'a> {
        arena_ast::AppKernel {
            grid_dim: self.grid_dim.into_arena(arena),
            block_dim: self.block_dim.into_arena(arena),
            shared_mem_dtys: self
                .shared_mem_dtys
                .iter()
                .map(|dty| dty.clone().into_arena(arena))
                .collect_in(arena),
            shared_mem_prvs: self
                .shared_mem_prvs
                .iter()
                .map(|s| arena.alloc_str(s).to_string())
                .collect_in(arena),
            fun_ident: arena.alloc(self.fun_ident.clone().into_arena(arena)),
            gen_args: self
                .gen_args
                .iter()
                .map(|arg| arg.into_arena(arena))
                .collect_in(arena),
            args: self
                .args
                .iter()
                .map(|arg| arg.clone().into_arena(arena))
                .collect_in(arena),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum ExprKind {
    Hole,
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
    LetUninit(Option<Box<ExecExpr>>, Ident, Box<Ty>),
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
    //Lambda(Vec<ParamDecl>, IdentExec, Box<DataTy>, Box<Expr>),
    // Function application
    // e_f(e_1, ..., e_n)
    App(Box<Ident>, Vec<ArgKinded>, Vec<Expr>),
    DepApp(Ident, Vec<ArgKinded>),
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
    ForNat(Ident, Box<NatRange>, Box<Expr>),
    // while( e_1 ) { e_2 }
    // TODO body must be block
    While(Box<Expr>, Box<Expr>),
    BinOp(BinOp, Box<Expr>, Box<Expr>),
    UnOp(UnOp, Box<Expr>),
    Cast(Box<Expr>, Box<DataTy>),
    // TODO branches must be blocks or treated like blocks
    Split(Box<Split>),
    Sched(Box<Sched>),
    Sync(Option<ExecExpr>),
    Unsafe(Box<Expr>),
    Range(Box<Expr>, Box<Expr>),
}

impl ExprKind {
    pub fn into_arena<'a>(self, arena: &'a Bump) -> arena_ast::ExprKind<'a> {
        use ExprKind::*;
        match self {
            Hole => arena_ast::ExprKind::Hole,
            Lit(l) => arena_ast::ExprKind::Lit(l.into_arena(arena)), // assuming `Lit` is Copy or doesn't need arena
            PlaceExpr(p) => arena_ast::ExprKind::PlaceExpr(arena.alloc(p.into_arena(arena))),
            Array(exprs) => {
                let mut bump_vec = bumpalo::collections::Vec::new_in(arena);
                for e in exprs {
                    bump_vec.push(e.into_arena(arena));
                }
                arena_ast::ExprKind::Array(bump_vec)
            }
            Tuple(exprs) => {
                let mut bump_vec = bumpalo::collections::Vec::new_in(arena);
                for e in exprs {
                    bump_vec.push(e.into_arena(arena));
                }
                arena_ast::ExprKind::Tuple(bump_vec)
            }
            Ref(ann, own, pl) => {
                arena_ast::ExprKind::Ref(ann, own.into_arena(), arena.alloc(pl.into_arena(arena)))
            }
            Block(b) => {
                let b_ref = arena.alloc(b.into_arena(arena));
                arena_ast::ExprKind::Block(b_ref)
            }
            LetUninit(exec, ident, ty) => arena_ast::ExprKind::LetUninit(
                exec.map(|e| &*arena.alloc(e.into_arena(arena))),
                ident.into_arena(arena),
                arena.alloc(ty.into_arena(arena)),
            ),
            Let(pat, ty, expr) => arena_ast::ExprKind::Let(
                pat.into_arena(arena),
                ty.map(|t| &*arena.alloc(t.into_arena(arena))),
                arena.alloc(expr.into_arena(arena)),
            ),
            Assign(pl, val) => arena_ast::ExprKind::Assign(
                arena.alloc(pl.into_arena(arena)),
                arena.alloc(val.into_arena(arena)),
            ),
            IdxAssign(pl, nat, val) => arena_ast::ExprKind::IdxAssign(
                arena.alloc(pl.into_arena(arena)),
                nat.into_arena(arena),
                arena.alloc(val.into_arena(arena)),
            ),
            Seq(exprs) => arena_ast::ExprKind::Seq(
                exprs
                    .into_iter()
                    .map(|e| e.into_arena(arena))
                    .collect_in(arena),
            ),
            App(ident, args, exprs) => arena_ast::ExprKind::App(
                arena.alloc(ident.into_arena(arena)),
                args.into_iter()
                    .map(|a| a.into_arena(arena))
                    .collect_in(arena),
                exprs
                    .into_iter()
                    .map(|e| e.into_arena(arena))
                    .collect_in(arena),
            ),
            DepApp(ident, args) => arena_ast::ExprKind::DepApp(
                ident.into_arena(arena),
                args.into_iter()
                    .map(|a| a.into_arena(arena))
                    .collect_in(arena),
            ),
            ExprKind::AppKernel(kern) => {
                arena_ast::ExprKind::AppKernel(arena.alloc(kern.into_arena(arena)))
            }
            IfElse(cond, then_, else_) => arena_ast::ExprKind::IfElse(
                arena.alloc(cond.into_arena(arena)),
                arena.alloc(then_.into_arena(arena)),
                arena.alloc(else_.into_arena(arena)),
            ),
            If(cond, body) => arena_ast::ExprKind::If(
                arena.alloc(cond.into_arena(arena)),
                arena.alloc(body.into_arena(arena)),
            ),
            For(ident, iter, body) => arena_ast::ExprKind::For(
                ident.into_arena(arena),
                arena.alloc(iter.into_arena(arena)),
                arena.alloc(body.into_arena(arena)),
            ),
            ForNat(ident, range, body) => arena_ast::ExprKind::ForNat(
                ident.into_arena(arena),
                arena.alloc(range.into_arena(arena)),
                arena.alloc(body.into_arena(arena)),
            ),
            While(cond, body) => arena_ast::ExprKind::While(
                arena.alloc(cond.into_arena(arena)),
                arena.alloc(body.into_arena(arena)),
            ),
            BinOp(op, lhs, rhs) => arena_ast::ExprKind::BinOp(
                op.into_arena(),
                arena.alloc(lhs.into_arena(arena)),
                arena.alloc(rhs.into_arena(arena)),
            ),
            UnOp(op, expr) => {
                arena_ast::ExprKind::UnOp(op.into_arena(), arena.alloc(expr.into_arena(arena)))
            }
            Cast(expr, dty) => arena_ast::ExprKind::Cast(
                arena.alloc(expr.into_arena(arena)),
                arena.alloc(dty.into_arena(arena)),
            ),
            Split(split) => arena_ast::ExprKind::Split(arena.alloc(split.into_arena(arena))),
            Sched(sched) => arena_ast::ExprKind::Sched(arena.alloc(sched.into_arena(arena))),
            Sync(exec_opt) => arena_ast::ExprKind::Sync(exec_opt.map(|e| e.into_arena(arena))),
            Unsafe(expr) => arena_ast::ExprKind::Unsafe(arena.alloc(expr.into_arena(arena))),
            Range(start, end) => arena_ast::ExprKind::Range(
                arena.alloc(start.into_arena(arena)),
                arena.alloc(end.into_arena(arena)),
            ),
        }
    }
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

    pub fn into_arena<'a>(self, arena: &'a Bump) -> arena_ast::Ident<'a> {
        arena_ast::Ident {
            name: arena.alloc_str(&self.name),
            span: self.span,
            is_implicit: self.is_implicit,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    Ident(Mutability, Ident),
    Tuple(Vec<Pattern>),
    Wildcard,
}

impl Pattern {
    pub fn into_arena<'a>(&self, arena: &'a Bump) -> arena_ast::Pattern<'a> {
        use Pattern::*;
        match self {
            Ident(mutability, ident) => {
                arena_ast::Pattern::Ident(mutability.into_arena(), ident.clone().into_arena(arena))
            }
            Tuple(pats) => {
                let arena_vec: bumpalo::collections::Vec<'a, _> =
                    pats.iter().map(|p| p.into_arena(arena)).collect_in(arena);
                arena_ast::Pattern::Tuple(arena_vec)
            }
            Wildcard => arena_ast::Pattern::Wildcard,
        }
    }
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

impl Lit {
    pub fn into_arena<'a>(&self, _arena: &'a Bump) -> arena_ast::Lit {
        use arena_ast::Lit as ALit;
        use Lit::*;

        match self {
            Unit => ALit::Unit,
            Bool(b) => ALit::Bool(*b),
            I32(i) => ALit::I32(*i),
            U8(u) => ALit::U8(*u),
            U32(u) => ALit::U32(*u),
            U64(u) => ALit::U64(*u),
            F32(f) => ALit::F32(*f),
            F64(f) => ALit::F64(*f),
        }
    }
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

impl Mutability {
    pub fn into_arena(&self) -> arena_ast::Mutability {
        match self {
            Mutability::Mut => arena_ast::Mutability::Mut,
            Mutability::Const => arena_ast::Mutability::Const,
        }
    }
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

impl Ownership {
    pub fn into_arena(&self) -> arena_ast::Ownership {
        match self {
            Ownership::Shrd => arena_ast::Ownership::Shrd,
            Ownership::Uniq => arena_ast::Ownership::Uniq,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum UnOp {
    Not,
    Neg,
}

impl UnOp {
    pub fn into_arena(&self) -> arena_ast::UnOp {
        match self {
            UnOp::Not => arena_ast::UnOp::Not,
            UnOp::Neg => arena_ast::UnOp::Neg,
        }
    }
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

impl BinOp {
    pub fn into_arena(&self) -> arena_ast::BinOp {
        match self {
            BinOp::Add => arena_ast::BinOp::Add,
            BinOp::Sub => arena_ast::BinOp::Sub,
            BinOp::Mul => arena_ast::BinOp::Mul,
            BinOp::Div => arena_ast::BinOp::Div,
            BinOp::Mod => arena_ast::BinOp::Mod,
            BinOp::And => arena_ast::BinOp::And,
            BinOp::Or => arena_ast::BinOp::Or,
            BinOp::Eq => arena_ast::BinOp::Eq,
            BinOp::Lt => arena_ast::BinOp::Lt,
            BinOp::Le => arena_ast::BinOp::Le,
            BinOp::Gt => arena_ast::BinOp::Gt,
            BinOp::Ge => arena_ast::BinOp::Ge,
            BinOp::Neq => arena_ast::BinOp::Neq,
            BinOp::Shl => arena_ast::BinOp::Shl,
            BinOp::Shr => arena_ast::BinOp::Shr,
            BinOp::BitOr => arena_ast::BinOp::BitOr,
            BinOp::BitAnd => arena_ast::BinOp::BitAnd,
        }
    }
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

impl Kind {
    pub fn into_arena(&self, _arena: &Bump) -> arena_ast::Kind {
        match self {
            Kind::Nat => arena_ast::Kind::Nat,
            Kind::Memory => arena_ast::Kind::Memory,
            Kind::DataTy => arena_ast::Kind::DataTy,
            Kind::Provenance => arena_ast::Kind::Provenance,
        }
    }
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

    pub fn into_arena<'a>(&self, arena: &'a Bump) -> arena_ast::ArgKinded<'a> {
        use ArgKinded::*;

        match self {
            Ident(ident) => arena_ast::ArgKinded::Ident(ident.clone().into_arena(arena)),
            Nat(nat) => arena_ast::ArgKinded::Nat(nat.into_arena(arena)),
            Memory(mem) => arena_ast::ArgKinded::Memory(mem.into_arena(arena)),
            DataTy(dty) => arena_ast::ArgKinded::DataTy(dty.clone().into_arena(arena)),
            Provenance(prv) => arena_ast::ArgKinded::Provenance(prv.into_arena(arena)),
        }
    }
}

#[span_derive(PartialEq, Eq, Hash)]
#[derive(Debug, Clone)]
pub struct PlaceExpr {
    pub pl_expr: PlaceExprKind,
    // FIXME misusing span_derive_ignore to ignore type on equality checks
    #[span_derive_ignore]
    pub ty: Option<Box<Ty>>,
    #[span_derive_ignore]
    pub span: Option<Span>,
}

impl PlaceExpr {
    pub fn into_arena<'a>(self, arena: &'a Bump) -> arena_ast::PlaceExpr<'a> {
        arena_ast::PlaceExpr {
            pl_expr: self.pl_expr.into_arena(arena),
            ty: self.ty.map(|t| &*arena.alloc(t.into_arena(arena))),
            span: self.span,
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct View {
    pub name: Ident,
    pub gen_args: Vec<ArgKinded>,
    pub args: Vec<View>,
}

impl View {
    pub fn equal(&self, nat_ctx: &NatCtx, other: &View) -> NatEvalResult<bool> {
        if self.name.name != other.name.name {
            return Ok(false);
        }
        if self.gen_args.len() != other.gen_args.len() {
            return Ok(false);
        }
        for (ga, go) in self.gen_args.iter().zip(&other.gen_args) {
            if !ga.equal(nat_ctx, go)? {
                return Ok(false);
            }
        }
        if self.args.len() != other.args.len() {
            return Ok(false);
        }
        for (v, vo) in self.args.iter().zip(&other.args) {
            if !v.equal(nat_ctx, vo)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub fn into_arena<'a>(self, arena: &'a Bump) -> arena_ast::View<'a> {
        let gen_args = self
            .gen_args
            .into_iter()
            .map(|g| g.into_arena(arena))
            .collect_in(arena);

        let args = self
            .args
            .into_iter()
            .map(|v| v.into_arena(arena))
            .collect_in(arena);

        arena_ast::View {
            name: self.name.into_arena(arena),
            gen_args,
            args,
        }
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
pub enum PlaceExprKind {
    View(Box<PlaceExpr>, Box<View>),
    // similar to a projection, but it projects an element for each provided execution resource
    // (similar to indexing)
    // p[[x]]
    Select(Box<PlaceExpr>, Box<ExecExpr>),
    // p.0 | p.1
    Proj(Box<PlaceExpr>, usize),
    FieldProj(Box<PlaceExpr>, Box<Ident>),
    // *p
    Deref(Box<PlaceExpr>),
    // Index into array, e.g., arr[i]
    Idx(Box<PlaceExpr>, Box<Nat>),
    // x
    Ident(Ident),
}

impl PlaceExprKind {
    pub fn into_arena<'a>(self, arena: &'a Bump) -> arena_ast::PlaceExprKind<'a> {
        use PlaceExprKind::*;

        match self {
            View(pl, view) => arena_ast::PlaceExprKind::View(
                arena.alloc(pl.into_arena(arena)),
                arena.alloc(view.into_arena(arena)),
            ),
            Select(pl, exec) => arena_ast::PlaceExprKind::Select(
                arena.alloc(pl.into_arena(arena)),
                arena.alloc(exec.into_arena(arena)),
            ),
            Proj(pl, idx) => arena_ast::PlaceExprKind::Proj(arena.alloc(pl.into_arena(arena)), idx),
            FieldProj(pl, ident) => arena_ast::PlaceExprKind::FieldProj(
                arena.alloc(pl.into_arena(arena)),
                arena.alloc(ident.into_arena(arena)),
            ),
            Deref(pl) => arena_ast::PlaceExprKind::Deref(arena.alloc(pl.into_arena(arena))),
            Idx(pl, nat) => arena_ast::PlaceExprKind::Idx(
                arena.alloc(pl.into_arena(arena)),
                arena.alloc(nat.into_arena(arena)),
            ),
            Ident(ident) => arena_ast::PlaceExprKind::Ident(ident.into_arena(arena)),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum PlExprPathElem {
    View(View),
    Select(Box<ExecExpr>),
    Proj(usize),
    FieldProj(Ident),
    Deref,
    Idx(Box<Nat>),
    RangeSelec(Box<Nat>, Box<Nat>),
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
            PlaceExprKind::Proj(ple, _) | PlaceExprKind::FieldProj(ple, _) => ple.is_place(),
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
                        pl.path.push(PathElem::Proj(*n));
                        (pl_ctx, internal::Place::new(pl.ident, pl.path))
                    }
                    _ => (internal::PlaceCtx::Proj(Box::new(pl_ctx), *n), pl),
                }
            }
            PlaceExprKind::FieldProj(inner_ple, field_name) => {
                let (pl_ctx, mut pl) = inner_ple.to_pl_ctx_and_most_specif_pl();
                match pl_ctx {
                    internal::PlaceCtx::Hole => {
                        pl.path.push(PathElem::FieldProj(field_name.clone()));
                        (pl_ctx, internal::Place::new(pl.ident, pl.path))
                    }
                    _ => (
                        internal::PlaceCtx::FieldProj(Box::new(pl_ctx), field_name.clone()),
                        pl,
                    ),
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
                PlaceExprKind::FieldProj(inner_ple, ident) => {
                    path.push(PlExprPathElem::FieldProj(ident.as_ref().clone()));
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
    pub exec: Box<ExecExprKind>,
    // FIXME misusing span_derive_ignore to ignore type on equality checks
    #[span_derive_ignore]
    pub ty: Option<Box<ExecTy>>,
    #[span_derive_ignore]
    pub span: Option<Span>,
}

impl ExecExpr {
    pub fn new(exec: ExecExprKind) -> Self {
        ExecExpr {
            exec: Box::new(exec),
            ty: None,
            span: None,
        }
    }

    pub fn into_arena<'a>(self, arena: &'a Bump) -> arena_ast::ExecExpr<'a> {
        arena_ast::ExecExpr {
            exec: arena.alloc(self.exec.into_arena(arena)),
            ty: self.ty.map(|t| {
                let tmp: &mut arena_ast::ExecTy<'a> = arena.alloc(t.into_arena(arena));
                &*tmp
            }),
            span: self.span,
        }
    }

    // TODO how does this relate to is_prefix_of. Refactor.
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
            .rposition(|e| matches!(e, ExecPathElem::ForAll(_)));
        let removed_distrib_path = if let Some(ldp) = last_distrib_pos {
            self.exec.path[..ldp].to_vec()
        } else {
            vec![]
        };
        ExecExpr::new(ExecExprKind::with_path(
            self.exec.base.clone(),
            removed_distrib_path,
        ))
    }

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
    let exec1 = ExecExpr::new(ExecExprKind::with_path(
        BaseExec::Ident(Ident::new("grid")),
        vec![ExecPathElem::ForAll(DimCompo::X)],
    ));
    let exec2 = ExecExpr::new(ExecExprKind::with_path(
        BaseExec::Ident(Ident::new("grid")),
        vec![ExecPathElem::ForAll(DimCompo::X)],
    ));
    if exec1 != exec2 {
        panic!("Unequal execs, that should be equal")
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub enum LeftOrRight {
    Left,
    Right,
}

impl LeftOrRight {
    pub fn into_arena(self) -> crate::arena_ast::LeftOrRight {
        match self {
            LeftOrRight::Left => crate::arena_ast::LeftOrRight::Left,
            LeftOrRight::Right => crate::arena_ast::LeftOrRight::Right,
        }
    }
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
pub struct TakeRange {
    pub split_dim: DimCompo,
    pub pos: Nat,
    pub left_or_right: LeftOrRight,
}

impl TakeRange {
    pub fn new(split_dim: DimCompo, pos: Nat, proj: LeftOrRight) -> Self {
        TakeRange {
            split_dim,
            pos,
            left_or_right: proj,
        }
    }

    pub fn into_arena<'a>(self, arena: &'a Bump) -> arena_ast::TakeRange<'a> {
        arena_ast::TakeRange {
            split_dim: self.split_dim.into_arena(),
            pos: self.pos.into_arena(arena),
            left_or_right: self.left_or_right.into_arena(),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct ExecExprKind {
    pub base: BaseExec,
    pub path: Vec<ExecPathElem>,
}

impl ExecExprKind {
    pub fn new(base: BaseExec) -> Self {
        ExecExprKind { base, path: vec![] }
    }

    pub fn with_path(base: BaseExec, path: Vec<ExecPathElem>) -> Self {
        ExecExprKind { base, path }
    }

    pub fn split_proj(mut self, dim_compo: DimCompo, pos: Nat, proj: LeftOrRight) -> Self {
        self.path
            .push(ExecPathElem::TakeRange(Box::new(TakeRange::new(
                dim_compo, pos, proj,
            ))));
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

    pub fn into_arena<'a>(self, arena: &'a Bump) -> arena_ast::ExecExprKind<'a> {
        let path = bumpalo::collections::Vec::from_iter_in(
            self.path.into_iter().map(|elem| elem.into_arena(arena)),
            arena,
        );

        arena_ast::ExecExprKind {
            base: self.base.into_arena(arena),
            path,
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum BaseExec {
    Ident(Ident),
    CpuThread,
    GpuGrid(Dim, Dim),
}

impl BaseExec {
    pub fn into_arena<'a>(self, arena: &'a Bump) -> arena_ast::BaseExec<'a> {
        use BaseExec::*;
        match self {
            Ident(ident) => arena_ast::BaseExec::Ident(ident.into_arena(arena)),
            CpuThread => arena_ast::BaseExec::CpuThread,
            GpuGrid(d1, d2) => {
                arena_ast::BaseExec::GpuGrid(d1.into_arena(arena), d2.into_arena(arena))
            }
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum ExecPathElem {
    TakeRange(Box<TakeRange>),
    ForAll(DimCompo),
    ToWarps,
    ToThreads(DimCompo),
}

impl ExecPathElem {
    pub fn into_arena<'a>(self, arena: &'a Bump) -> arena_ast::ExecPathElem<'a> {
        use ExecPathElem::*;

        match self {
            TakeRange(take_range) => {
                let arena_take_range = arena.alloc(take_range.clone().into_arena(arena));
                arena_ast::ExecPathElem::TakeRange(arena_take_range)
            }
            ForAll(dim_compo) => arena_ast::ExecPathElem::ForAll(dim_compo.into_arena()),
            ToWarps => arena_ast::ExecPathElem::ToWarps,
            ToThreads(dim_compo) => arena_ast::ExecPathElem::ToThreads(dim_compo.into_arena()),
        }
    }
}

// ExecTy
// fn size(DimCompo) -> usize
// fn take_range(DimCompo, Nat) -> ExecTy
// fn elem_type(DimCompo) -> ExecTy
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

    pub fn into_arena<'a>(self, arena: &'a Bump) -> arena_ast::ExecTy<'a> {
        arena_ast::ExecTy {
            ty: self.ty.into_arena(arena),
            span: self.span,
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum ExecTyKind {
    CpuThread,
    GpuThread,
    GpuWarp,
    GpuBlock(Dim),
    GpuGrid(Dim, Dim),
    GpuToThreads(Dim, Box<ExecTy>),
    GpuThreadGrp(Dim),
    GpuWarpGrp(Nat),
    GpuBlockGrp(Dim, Dim),
    Any,
}

impl ExecTyKind {
    pub fn into_arena<'a>(&self, arena: &'a Bump) -> arena_ast::ExecTyKind<'a> {
        use ExecTyKind::*;

        match self {
            CpuThread => arena_ast::ExecTyKind::CpuThread,
            GpuThread => arena_ast::ExecTyKind::GpuThread,
            GpuWarp => arena_ast::ExecTyKind::GpuWarp,
            GpuBlock(dim) => arena_ast::ExecTyKind::GpuBlock(dim.into_arena(arena)),
            GpuGrid(d1, d2) => {
                arena_ast::ExecTyKind::GpuGrid(d1.into_arena(arena), d2.into_arena(arena))
            }
            GpuToThreads(dim, inner) => arena_ast::ExecTyKind::GpuToThreads(
                dim.into_arena(arena),
                arena.alloc(inner.clone().into_arena(arena)),
            ),
            GpuThreadGrp(dim) => arena_ast::ExecTyKind::GpuThreadGrp(dim.into_arena(arena)),
            GpuWarpGrp(nat) => arena_ast::ExecTyKind::GpuWarpGrp(nat.into_arena(arena)),
            GpuBlockGrp(d1, d2) => {
                arena_ast::ExecTyKind::GpuBlockGrp(d1.into_arena(arena), d2.into_arena(arena))
            }
            Any => arena_ast::ExecTyKind::Any,
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

impl Ty {
    pub fn into_arena<'a>(self, arena: &'a Bump) -> arena_ast::Ty<'a> {
        arena_ast::Ty {
            ty: self.ty.into_arena(arena),
            span: self.span,
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct ParamSig {
    pub exec_expr: ExecExpr,
    pub ty: Ty,
}

impl ParamSig {
    pub fn new(exec_expr: ExecExpr, ty: Ty) -> Self {
        ParamSig { exec_expr, ty }
    }

    pub fn into_arena<'a>(self, arena: &'a Bump) -> arena_ast::ParamSig<'a> {
        let ty = self.ty.into_arena(arena);
        arena_ast::ParamSig {
            exec_expr: self.exec_expr.into_arena(arena),
            ty: arena.alloc(ty),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct FnTy {
    pub generics: Vec<IdentKinded>,
    pub generic_exec: Option<IdentExec>,
    pub param_sigs: Vec<ParamSig>,
    pub exec: ExecExpr,
    pub ret_ty: Box<Ty>,
    pub nat_constrs: Vec<NatConstr>,
}

impl FnTy {
    pub fn new(
        generics: Vec<IdentKinded>,
        generic_exec: Option<IdentExec>,
        param_sigs: Vec<ParamSig>,
        exec: ExecExpr,
        ret_ty: Ty,
        nat_constrs: Vec<NatConstr>,
    ) -> Self {
        FnTy {
            generics,
            generic_exec,
            param_sigs,
            exec,
            ret_ty: Box::new(ret_ty),
            nat_constrs,
        }
    }

    pub fn into_arena<'a>(self, arena: &'a Bump) -> arena_ast::FnTy<'a> {
        let generics = self
            .generics
            .into_iter()
            .map(|g| g.into_arena(arena))
            .collect_in(arena);

        let generic_exec = self.generic_exec.map(|g| g.into_arena(arena));

        let param_sigs = self
            .param_sigs
            .into_iter()
            .map(|p| p.into_arena(arena))
            .collect_in(arena);

        let nat_constrs = self
            .nat_constrs
            .into_iter()
            .map(|c| c.into_arena(arena))
            .collect_in(arena);

        arena_ast::FnTy {
            generics,
            generic_exec,
            param_sigs,
            exec: self.exec.into_arena(arena),
            ret_ty: arena.alloc(self.ret_ty.into_arena(arena)),
            nat_constrs,
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum NatConstr {
    True,
    Eq(Box<Nat>, Box<Nat>),
    Lt(Box<Nat>, Box<Nat>),
    And(Box<NatConstr>, Box<NatConstr>),
    Or(Box<NatConstr>, Box<NatConstr>),
}

impl NatConstr {
    pub fn into_arena<'a>(self, arena: &'a Bump) -> arena_ast::NatConstr<'a> {
        use NatConstr::*;

        match self {
            True => arena_ast::NatConstr::True,
            Eq(lhs, rhs) => arena_ast::NatConstr::Eq(
                arena.alloc(lhs.into_arena(arena)),
                arena.alloc(rhs.into_arena(arena)),
            ),
            Lt(lhs, rhs) => arena_ast::NatConstr::Lt(
                arena.alloc(lhs.into_arena(arena)),
                arena.alloc(rhs.into_arena(arena)),
            ),
            And(lhs, rhs) => arena_ast::NatConstr::And(
                arena.alloc(lhs.into_arena(arena)),
                arena.alloc(rhs.into_arena(arena)),
            ),
            Or(lhs, rhs) => arena_ast::NatConstr::Or(
                arena.alloc(lhs.into_arena(arena)),
                arena.alloc(rhs.into_arena(arena)),
            ),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum TyKind {
    Data(Box<DataTy>),
    // <x:k,..>(ty..) -[x:exec]-> ty
    FnTy(Box<FnTy>),
}

impl TyKind {
    pub fn into_arena<'a>(self, arena: &'a Bump) -> arena_ast::TyKind<'a> {
        match self {
            TyKind::Data(dty) => {
                let boxed = bumpalo::boxed::Box::new_in(dty.into_arena(arena), arena);
                arena_ast::TyKind::Data(arena.alloc(boxed))
            }
            TyKind::FnTy(fn_ty) => {
                let boxed = bumpalo::boxed::Box::new_in(fn_ty.into_arena(arena), arena);
                arena_ast::TyKind::FnTy(arena.alloc(boxed))
            }
        }
    }
}

// TODO remove
#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub enum Constraint {
    Copyable,
}

impl Constraint {
    pub fn into_arena(&self) -> arena_ast::Constraint {
        match self {
            Constraint::Copyable => arena_ast::Constraint::Copyable,
        }
    }
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
                    .param_sigs
                    .iter()
                    .any(|param_sig| param_sig.ty.contains_ref_to_prv(prv_val_name))
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

    pub fn into_arena<'a>(&self, arena: &'a Bump) -> arena_ast::Dim<'a> {
        use Dim::*;

        match self {
            XYZ(boxed) => arena_ast::Dim::XYZ(arena.alloc(arena_ast::Dim3d(
                boxed.0.into_arena(arena),
                boxed.1.into_arena(arena),
                boxed.2.into_arena(arena),
            ))),
            XY(boxed) => arena_ast::Dim::XY(arena.alloc(arena_ast::Dim2d(
                boxed.0.into_arena(arena),
                boxed.1.into_arena(arena),
            ))),
            XZ(boxed) => arena_ast::Dim::XZ(arena.alloc(arena_ast::Dim2d(
                boxed.0.into_arena(arena),
                boxed.1.into_arena(arena),
            ))),
            YZ(boxed) => arena_ast::Dim::YZ(arena.alloc(arena_ast::Dim2d(
                boxed.0.into_arena(arena),
                boxed.1.into_arena(arena),
            ))),
            X(boxed) => arena_ast::Dim::X(arena.alloc(arena_ast::Dim1d(boxed.0.into_arena(arena)))),
            Y(boxed) => arena_ast::Dim::Y(arena.alloc(arena_ast::Dim1d(boxed.0.into_arena(arena)))),
            Z(boxed) => arena_ast::Dim::Z(arena.alloc(arena_ast::Dim1d(boxed.0.into_arena(arena)))),
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Hash, Debug, Copy, Clone)]
pub enum DimCompo {
    X,
    Y,
    Z,
}

impl DimCompo {
    pub fn into_arena(self) -> crate::arena_ast::DimCompo {
        match self {
            DimCompo::X => crate::arena_ast::DimCompo::X,
            DimCompo::Y => crate::arena_ast::DimCompo::Y,
            DimCompo::Z => crate::arena_ast::DimCompo::Z,
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

    pub fn into_arena<'a>(self, arena: &'a Bump) -> arena_ast::DataTy<'a> {
        arena_ast::DataTy {
            dty: self.dty.into_arena(arena),
            constraints: self
                .constraints
                .into_iter()
                .map(|c| c.into_arena())
                .collect_in(arena),
            span: self.span,
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

    pub fn into_arena<'a>(&self, arena: &'a Bump) -> arena_ast::RefDty<'a> {
        arena_ast::RefDty {
            rgn: self.rgn.into_arena(arena),
            own: self.own.into_arena(),
            mem: self.mem.into_arena(arena),
            dty: arena.alloc(self.dty.clone().into_arena(arena)),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum DataTyKind {
    Ident(Ident),
    Scalar(ScalarTy),
    Atomic(AtomicTy),
    Array(Box<DataTy>, Nat),
    // [[ dty; n ]]
    ArrayShape(Box<DataTy>, Nat),
    Tuple(Vec<DataTy>),
    Struct(Box<StructDecl>),
    At(Box<DataTy>, Memory),
    Ref(Box<RefDty>),
    RawPtr(Box<DataTy>),
    //Range,
    // TODO remove. This is an attribute of a typing context entry, not the type.
    // Only for type checking purposes.
    Dead(Box<DataTy>),
}

impl DataTyKind {
    pub fn into_arena<'a>(&self, arena: &'a Bump) -> arena_ast::DataTyKind<'a> {
        use DataTyKind::*;

        match self {
            Ident(ident) => arena_ast::DataTyKind::Ident(ident.clone().into_arena(arena)),
            Scalar(sty) => arena_ast::DataTyKind::Scalar(sty.into_arena()),
            Atomic(aty) => arena_ast::DataTyKind::Atomic(aty.into_arena()),

            Array(dty, nat) => arena_ast::DataTyKind::Array(
                arena.alloc(dty.clone().into_arena(arena)),
                nat.into_arena(arena),
            ),

            ArrayShape(dty, nat) => arena_ast::DataTyKind::ArrayShape(
                arena.alloc(dty.clone().into_arena(arena)),
                nat.into_arena(arena),
            ),

            Tuple(elem_dtys) => {
                let arena_vec = bumpalo::collections::Vec::from_iter_in(
                    elem_dtys.iter().map(|dty| dty.clone().into_arena(arena)),
                    arena,
                );
                arena_ast::DataTyKind::Tuple(arena_vec)
            }

            Struct(decl) => {
                arena_ast::DataTyKind::Struct(arena.alloc(decl.clone().into_arena(arena)))
            }

            At(dty, mem) => arena_ast::DataTyKind::At(
                arena.alloc(dty.clone().into_arena(arena)),
                mem.into_arena(arena),
            ),

            Ref(refdty) => {
                let refdty_in = arena.alloc(refdty.into_arena(arena));
                arena_ast::DataTyKind::Ref(refdty_in)
            }

            RawPtr(dty) => {
                arena_ast::DataTyKind::RawPtr(arena.alloc(dty.clone().into_arena(arena)))
            }

            Dead(dty) => arena_ast::DataTyKind::Dead(arena.alloc(dty.clone().into_arena(arena))),
        }
    }
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

impl ScalarTy {
    pub fn into_arena(self) -> arena_ast::ScalarTy {
        match self {
            ScalarTy::Unit => arena_ast::ScalarTy::Unit,
            ScalarTy::U8 => arena_ast::ScalarTy::U8,
            ScalarTy::U32 => arena_ast::ScalarTy::U32,
            ScalarTy::U64 => arena_ast::ScalarTy::U64,
            ScalarTy::I32 => arena_ast::ScalarTy::I32,
            ScalarTy::I64 => arena_ast::ScalarTy::I64,
            ScalarTy::F32 => arena_ast::ScalarTy::F32,
            ScalarTy::F64 => arena_ast::ScalarTy::F64,
            ScalarTy::Bool => arena_ast::ScalarTy::Bool,
            ScalarTy::Gpu => arena_ast::ScalarTy::Gpu,
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Copy, Clone)]
pub enum AtomicTy {
    AtomicU32,
    AtomicI32,
}

impl AtomicTy {
    pub fn into_arena(self) -> arena_ast::AtomicTy {
        match self {
            AtomicTy::AtomicU32 => arena_ast::AtomicTy::AtomicU32,
            AtomicTy::AtomicI32 => arena_ast::AtomicTy::AtomicI32,
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum Provenance {
    Value(String),
    Ident(Ident),
}

impl Provenance {
    pub fn into_arena<'a>(&self, arena: &'a Bump) -> arena_ast::Provenance<'a> {
        match self {
            Provenance::Value(s) => arena_ast::Provenance::Value(arena.alloc_str(s)),
            Provenance::Ident(ident) => {
                arena_ast::Provenance::Ident(ident.clone().into_arena(arena))
            }
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
    pub fn into_arena<'a>(&self, arena: &'a Bump) -> arena_ast::Memory<'a> {
        match self {
            Memory::CpuMem => arena_ast::Memory::CpuMem,
            Memory::GpuGlobal => arena_ast::Memory::GpuGlobal,
            Memory::GpuShared => arena_ast::Memory::GpuShared,
            Memory::GpuLocal => arena_ast::Memory::GpuLocal,
            Memory::Ident(ident) => arena_ast::Memory::Ident(ident.clone().into_arena(arena)),
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct PrvRel {
    pub longer: Ident,
    pub shorter: Ident,
}

impl PrvRel {
    pub fn into_arena<'a>(&self, arena: &'a Bump) -> arena_ast::PrvRel<'a> {
        arena_ast::PrvRel {
            longer: self.longer.clone().into_arena(arena),
            shorter: self.shorter.clone().into_arena(arena),
        }
    }
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
            kind,
        }
    }

    pub fn into_arena<'a>(&self, arena: &'a Bump) -> arena_ast::IdentKinded<'a> {
        arena_ast::IdentKinded {
            ident: self.ident.clone().into_arena(arena),
            kind: self.kind.into_arena(arena),
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum NatRange {
    Simple { lower: Nat, upper: Nat },
    Halved { upper: Nat },
    Doubled { upper: Nat },
}

impl NatRange {
    pub fn lift(&self, nat_ctx: &NatCtx) -> NatEvalResult<NatRangeIter> {
        let range_iter = match self {
            NatRange::Simple { lower, upper } => {
                let lower = lower.eval(nat_ctx)?;
                let upper = upper.eval(nat_ctx)?;
                NatRangeIter::new(lower, Box::new(|x| x + 1), Box::new(move |c| c >= upper))
            }
            NatRange::Halved { upper } => {
                let upper = upper.eval(nat_ctx)?;
                NatRangeIter::new(upper, Box::new(|x| x / 2), Box::new(|c| c == 0))
            }
            NatRange::Doubled { upper } => {
                let upper = upper.eval(nat_ctx)?;
                NatRangeIter::new(1, Box::new(|x| x * 2), Box::new(move |c| c >= upper))
            }
        };
        Ok(range_iter)
    }

    pub fn into_arena<'a>(&self, arena: &'a Bump) -> arena_ast::NatRange<'a> {
        use NatRange::*;

        match self {
            Simple { lower, upper } => arena_ast::NatRange::Simple {
                lower: lower.into_arena(arena),
                upper: upper.into_arena(arena),
            },
            Halved { upper } => arena_ast::NatRange::Halved {
                upper: upper.into_arena(arena),
            },
            Doubled { upper } => arena_ast::NatRange::Doubled {
                upper: upper.into_arena(arena),
            },
        }
    }
}

pub struct NatRangeIter {
    current: usize,
    // go from current to next value
    step_fun: Box<dyn Fn(usize) -> usize>,
    // determine whether the current value is still within range
    end_cond: Box<dyn Fn(usize) -> bool>,
}

impl NatRangeIter {
    fn new(
        start: usize,
        step_fun: Box<dyn Fn(usize) -> usize>,
        end_cond: Box<dyn Fn(usize) -> bool>,
    ) -> Self {
        NatRangeIter {
            current: start,
            step_fun,
            end_cond,
        }
    }
}

impl Iterator for NatRangeIter {
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
pub enum Nat {
    Ident(Ident),
    Lit(usize),
    ThreadIdx(DimCompo),
    BlockIdx(DimCompo),
    BlockDim(DimCompo),
    WarpGrpIdx,
    WarpIdx,
    LaneIdx,
    // Dummy that is always 0, i.e. equivalent to Lit(0)
    GridIdx,
    BinOp(BinOpNat, Box<Nat>, Box<Nat>),
    // Use Box<[Nat]> to safe 8 bytes compared to Vec<Nat>
    App(Ident, Box<[Nat]>),
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
pub struct NatEvalError {
    pub unevaluable: Nat,
}

impl NatEvalError {
    pub fn into_arena<'a>(&self, arena: &'a Bump) -> arena_ast::NatEvalError<'a> {
        arena_ast::NatEvalError {
            unevaluable: self.unevaluable.clone().into_arena(arena),
        }
    }
}

pub type NatEvalResult<T> = Result<T, NatEvalError>;

fn convert_result<'a>(
    result: NatEvalResult<usize>,
    arena: &'a Bump,
) -> arena_ast::NatEvalResult<'a, usize> {
    result.map_err(|e| e.into_arena(arena))
}

impl Nat {
    pub fn into_arena<'a>(&self, arena: &'a Bump) -> arena_ast::Nat<'a> {
        use Nat::*;

        match self {
            Ident(ident) => arena_ast::Nat::Ident(ident.clone().into_arena(arena)),

            Lit(n) => arena_ast::Nat::Lit(*n),

            ThreadIdx(dc) => arena_ast::Nat::ThreadIdx((*dc).into_arena()),
            BlockIdx(dc) => arena_ast::Nat::BlockIdx((*dc).into_arena()),
            BlockDim(dc) => arena_ast::Nat::BlockDim((*dc).into_arena()),

            WarpGrpIdx => arena_ast::Nat::WarpGrpIdx,
            WarpIdx => arena_ast::Nat::WarpIdx,
            LaneIdx => arena_ast::Nat::LaneIdx,
            GridIdx => arena_ast::Nat::GridIdx,

            BinOp(op, lhs, rhs) => arena_ast::Nat::BinOp(
                op.clone().into_arena(),
                arena.alloc(lhs.into_arena(arena)),
                arena.alloc(rhs.into_arena(arena)),
            ),

            App(ident, args) => {
                let arena_args: BumpVec<'a, arena_ast::Nat<'a>> =
                    BumpVec::from_iter_in(args.iter().map(|n| n.into_arena(arena)), arena);

                arena_ast::Nat::App(ident.clone().into_arena(arena), arena_args)
            }
        }
    }

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

impl BinOpNat {
    pub fn into_arena(self) -> crate::arena_ast::BinOpNat {
        match self {
            BinOpNat::Add => crate::arena_ast::BinOpNat::Add,
            BinOpNat::Sub => crate::arena_ast::BinOpNat::Sub,
            BinOpNat::Mul => crate::arena_ast::BinOpNat::Mul,
            BinOpNat::Div => crate::arena_ast::BinOpNat::Div,
            BinOpNat::Mod => crate::arena_ast::BinOpNat::Mod,
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
