use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;
use std::fmt::Formatter;

use descend_derive::span_derive;
pub use span::*;

use crate::ast::visit_mut::VisitMut;
use crate::parser::SourceCode;

pub mod internal;

mod span;
#[macro_use]
pub mod visit;
pub mod utils;
#[macro_use]
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
    pub name: String,
    pub generic_params: Vec<IdentKinded>,
    pub param_decls: Vec<ParamDecl>,
    pub ret_dty: DataTy,
    pub exec: Exec,
    pub prv_rels: Vec<PrvRel>,
    pub body_expr: Expr,
}

impl FunDef {
    pub fn ty(&self) -> Ty {
        let param_tys: Vec<_> = self
            .param_decls
            .iter()
            .map(|p_decl| p_decl.ty.as_ref().unwrap().clone())
            .collect();
        Ty::new(TyKind::Fn(
            self.generic_params.clone(),
            param_tys,
            self.exec,
            Box::new(Ty::new(TyKind::Data(self.ret_dty.clone()))),
        ))
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
    pub ty: Option<Ty>,
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
            ty: Some(ty),
            span: None,
        }
    }

    pub fn subst_idents(&mut self, subst_map: &HashMap<&str, &Expr>) {
        fn pl_expr_contains_name_in<'a, I>(pl_expr: &PlaceExpr, mut idents: I) -> bool
        where
            I: Iterator<Item = &'a &'a str>,
        {
            match &pl_expr.pl_expr {
                PlaceExprKind::Ident(ident) => idents.any(|name| ident.name == *name),
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
                                self.subst_map.get::<&str>(&ident.name.as_str()).unwrap();
                            if let ExprKind::PlaceExpr(pl_e) = &subst_expr.expr {
                                *pl_expr = pl_e.clone();
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
                                        self.subst_map.get::<&str>(&ident.name.as_str())
                                    {
                                        *expr = subst_expr.clone();
                                    }
                                }
                                PlaceExprKind::Proj(tuple, i) => {
                                    let mut tuple_expr =
                                        Expr::new(ExprKind::PlaceExpr(tuple.as_ref().clone()));
                                    self.visit_expr(&mut tuple_expr);
                                    *expr = Expr::new(ExprKind::Proj(Box::new(tuple_expr), *i));
                                }
                                PlaceExprKind::Deref(deref_expr) => {
                                    let mut ref_expr =
                                        Expr::new(ExprKind::PlaceExpr(deref_expr.as_ref().clone()));
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

    pub fn subst_kinded_idents(&mut self, subst_map: HashMap<&str, &ArgKinded>) {
        struct SubstKindedIdents<'a> {
            subst_map: HashMap<&'a str, &'a ArgKinded>,
        }
        // FIXME currently not able to deal with identifiers for which the kind is not known,
        //  i.e., pre codegneration, there still exist ArgKinded::Ident(_)
        impl VisitMut for SubstKindedIdents<'_> {
            fn visit_nat(&mut self, nat: &mut Nat) {
                match nat {
                    Nat::Ident(ident) => {
                        if let Some(ArgKinded::Nat(nat_arg)) =
                            self.subst_map.get::<&str>(&ident.name.as_str())
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
                            self.subst_map.get::<&str>(&ident.name.as_str())
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
                            self.subst_map.get::<&str>(&ident.name.as_str())
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
                        if let Some(ArgKinded::Ty(Ty {
                            ty: TyKind::Data(dty_arg),
                            ..
                        })) = self.subst_map.get::<&str>(&ident.name.as_str())
                        {
                            *dty = dty_arg.clone()
                        }
                    }
                    _ => visit_mut::walk_dty(self, dty),
                }
            }

            fn visit_ty(&mut self, ty: &mut Ty) {
                match &ty.ty {
                    TyKind::Ident(ident) => {
                        if let Some(ArgKinded::Ty(ty_arg)) =
                            self.subst_map.get::<&str>(&ident.name.as_str())
                        {
                            *ty = ty_arg.clone();
                        }
                    }
                    _ => visit_mut::walk_ty(self, ty),
                }
            }
        }

        let mut subst_kinded_idents = SubstKindedIdents { subst_map };
        subst_kinded_idents.visit_expr(self)
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum ExprKind {
    Lit(Lit),
    // An l-value equivalent: *p, p.n, x
    PlaceExpr(PlaceExpr),
    // Index into array, e.g., arr[i]
    Index(PlaceExpr, Nat),
    // Projection, e.g. e.1, for non place expressions, e.g. f(x).1
    Proj(Box<Expr>, usize),
    // e.g., [1, 2 + 3, 4]
    Array(Vec<Expr>),
    Tuple(Vec<Expr>),
    // Borrow Expressions
    Ref(Option<String>, Ownership, PlaceExpr),
    BorrowIndex(Option<String>, Ownership, PlaceExpr, Nat),
    Block(Vec<String>, Box<Expr>),
    // Variable declaration
    // let mut x: ty;
    LetUninit(Ident, Box<Ty>),
    // Variable declaration, assignment and sequencing
    // let w x: ty = e1
    Let(Pattern, Box<Option<Ty>>, Box<Expr>),
    // Assignment to existing place [expression]
    Assign(PlaceExpr, Box<Expr>),
    // e1[i] = e2
    IdxAssign(PlaceExpr, Nat, Box<Expr>),
    // e1 ; e2
    Seq(Vec<Expr>),
    // Anonymous function which can capture its surrounding context
    // | x_n: d_1, ..., x_n: d_n | [exec]-> d_r { e }
    Lambda(Vec<ParamDecl>, Exec, Box<DataTy>, Box<Expr>),
    // Function application
    // e_f(e_1, ..., e_n)
    App(Box<Expr>, Vec<ArgKinded>, Vec<Expr>),
    // TODO remove
    DepApp(Box<Expr>, Vec<ArgKinded>),
    IfElse(Box<Expr>, Box<Expr>, Box<Expr>),
    If(Box<Expr>, Box<Expr>),
    // For-each loop.
    // for x in e_1 { e_2 }
    For(Ident, Box<Expr>, Box<Expr>),
    // for n in range(..) { e }
    ForNat(Ident, Nat, Box<Expr>),
    // while( e_1 ) { e_2 }
    While(Box<Expr>, Box<Expr>),
    BinOp(BinOp, Box<Expr>, Box<Expr>),
    UnOp(UnOp, Box<Expr>),
    ParBranch(Box<Expr>, Vec<Ident>, Vec<Expr>),
    ParForWith(
        Option<Vec<Expr>>,
        DimCompo,
        Option<Ident>,
        Box<Expr>,
        Vec<Ident>,
        Vec<Expr>,
        Box<Expr>,
    ),
    Split(
        Option<String>,
        Option<String>,
        Ownership,
        Nat,
        Box<PlaceExpr>,
    ),
    Range(Box<Expr>, Box<Expr>),
    // Deref a non place expression; ONLY for codegen
    Deref(Box<Expr>),
    // Index into an array; ONLY for codegen
    Idx(Box<Expr>, Nat),
}

#[span_derive(PartialEq, Eq, Hash)]
#[derive(Clone, Debug)]
pub struct Ident {
    pub name: String,
    #[span_derive_ignore]
    pub span: Option<Span>,
    pub is_implicit: bool,
}

impl Ident {
    pub fn new(name: &str) -> Self {
        Self {
            name: String::from(name),
            span: None,
            is_implicit: false,
        }
    }

    pub fn new_impli(name: &str) -> Self {
        Self {
            name: String::from(name),
            span: None,
            is_implicit: true,
        }
    }

    pub fn with_span(name: String, span: Span) -> Self {
        Self {
            name,
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

#[derive(PartialEq, Eq, Hash, Debug, Copy, Clone)]
pub enum Kind {
    Nat,
    Memory,
    Ty,
    DataTy,
    Provenance,
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let str = match self {
            Kind::Nat => "nat",
            Kind::Memory => "mem",
            Kind::Ty => "type",
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
    Ty(Ty),
    DataTy(DataTy),
    Provenance(Provenance),
}

impl ArgKinded {
    pub fn kind(&self) -> Kind {
        match self {
            ArgKinded::Ident(_) => {
                panic!("Unexpected: unkinded identifier should have been removed after parsing")
            }
            ArgKinded::Ty(_) => Kind::Ty,
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
    pub ty: Option<Ty>,
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
pub struct Ty {
    pub ty: TyKind,
    pub constraints: Vec<Constraint>,
    #[span_derive_ignore]
    pub span: Option<Span>,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum TyKind {
    Data(DataTy),
    Fn(Vec<IdentKinded>, Vec<Ty>, Exec, Box<Ty>),
    Ident(Ident),
    Dead(Box<Ty>),
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub enum Constraint {
    Copyable,
    NonCopyable,
    Dead,
}

impl Ty {
    pub fn new(ty: TyKind) -> Self {
        Ty {
            ty,
            constraints: vec![],
            span: None,
        }
    }

    pub fn with_constr(ty: TyKind, constraints: Vec<Constraint>) -> Ty {
        Ty {
            ty,
            constraints,
            span: None,
        }
    }

    pub fn with_span(ty: TyKind, span: Span) -> Ty {
        Ty {
            ty,
            constraints: vec![],
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

    pub fn non_copyable(&self) -> bool {
        !self.copyable()
    }

    pub fn copyable(&self) -> bool {
        match &self.ty {
            TyKind::Data(dty) => dty.copyable(),
            TyKind::Fn(_, _, _, _) => true,
            TyKind::Ident(_) => false,
            TyKind::Dead(_) => panic!(
                "This case is not expected to mean anything.\
                The type is dead. There is nothing we can do with it."
            ),
        }
    }

    pub fn is_fully_alive(&self) -> bool {
        match &self.ty {
            TyKind::Data(dty) => dty.is_fully_alive(),
            TyKind::Ident(_) | TyKind::Fn(_, _, _, _) => true,
            TyKind::Dead(_) => false,
        }
    }

    pub fn eq_structure(&self, other: &Self) -> bool {
        match (&self.ty, &other.ty) {
            (TyKind::Fn(gps1, ptys1, exec1, ret_ty1), TyKind::Fn(gps2, ptys2, exec2, ret_ty2)) => {
                let mut res = true;
                for (gp1, gp2) in gps1.iter().zip(gps2) {
                    res &= gp1 == gp2;
                }
                for (pty1, pty2) in ptys1.iter().zip(ptys2) {
                    res &= pty1.eq_structure(pty2);
                }
                res &= exec1 == exec2;
                res & ret_ty1.eq_structure(ret_ty2)
            }
            (TyKind::Data(dty1), TyKind::Data(dty2)) => unimplemented!(), //dty1.eq_structure(dty2),
            (TyKind::Ident(id1), TyKind::Ident(id2)) => id1 == id2,
            (TyKind::Dead(ty1), TyKind::Dead(ty2)) => ty1.eq_structure(ty2),
            _ => false,
        }
    }

    pub fn contains_ref_to_prv(&self, prv_val_name: &str) -> bool {
        match &self.ty {
            TyKind::Data(dty) => dty.contains_ref_to_prv(prv_val_name),
            TyKind::Fn(_, param_tys, _, ret_ty) => {
                param_tys
                    .iter()
                    .any(|param_ty| param_ty.contains_ref_to_prv(prv_val_name))
                    || ret_ty.contains_ref_to_prv(prv_val_name)
            }
            TyKind::Ident(_) | TyKind::Dead(_) => false,
        }
    }

    pub fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Self {
        match &self.ty {
            // TODO mutate and do not create a new type (also this drops the span).
            TyKind::Data(dty) => Ty::new(TyKind::Data(dty.subst_ident_kinded(ident_kinded, with))),
            TyKind::Fn(gen_params, params, exec, ret) => Ty::new(TyKind::Fn(
                gen_params.clone(),
                params
                    .iter()
                    .map(|param| param.subst_ident_kinded(ident_kinded, with))
                    .collect(),
                exec.clone(),
                Box::new(ret.subst_ident_kinded(ident_kinded, with)),
            )),
            TyKind::Ident(ident) => {
                if &ident_kinded.ident == ident && ident_kinded.kind == Kind::Ty {
                    match with {
                        ArgKinded::Ident(idk) => Ty::new(TyKind::Ident(idk.clone())),
                        ArgKinded::Ty(ty) => ty.clone(),
                        _ => panic!("Trying to substitute type identifier with non-type value."),
                    }
                } else {
                    self.clone()
                }
            }
            TyKind::Dead(ty) => ty.subst_ident_kinded(ident_kinded, with),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum Dim {
    XYZ(Nat, Nat, Nat),
    XY(Nat, Nat),
    XZ(Nat, Nat),
    YZ(Nat, Nat),
    X(Nat),
    Y(Nat),
    Z(Nat),
}

impl fmt::Display for Dim {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Dim::*;
        match self {
            XYZ(n1, n2, n3) => write!(f, "{}, {}, {}", n1, n2, n3),
            XY(n1, n2) | XZ(n1, n2) | YZ(n1, n2) => write!(f, "{}, {}", n1, n2),
            X(n) | Y(n) | Z(n) => write!(f, "{}", n),
        }
    }
}

impl Dim {
    pub fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Self {
        use Dim::*;
        match self {
            XYZ(n1, n2, n3) => XYZ(
                n1.subst_ident_kinded(ident_kinded, with),
                n2.subst_ident_kinded(ident_kinded, with),
                n3.subst_ident_kinded(ident_kinded, with),
            ),
            XY(n1, n2) => XY(
                n1.subst_ident_kinded(ident_kinded, with),
                n2.subst_ident_kinded(ident_kinded, with),
            ),
            XZ(n1, n2) => XZ(
                n1.subst_ident_kinded(ident_kinded, with),
                n2.subst_ident_kinded(ident_kinded, with),
            ),
            YZ(n1, n2) => YZ(
                n1.subst_ident_kinded(ident_kinded, with),
                n2.subst_ident_kinded(ident_kinded, with),
            ),
            X(n) => X(n.subst_ident_kinded(ident_kinded, with)),
            Y(n) => Y(n.subst_ident_kinded(ident_kinded, with)),
            Z(n) => Z(n.subst_ident_kinded(ident_kinded, with)),
        }
    }

    pub fn remove_dim(&self, dim_compo: DimCompo) -> Option<Self> {
        match (self, dim_compo) {
            (Dim::XYZ(n1, n2, n3), DimCompo::X) => Some(Dim::YZ(n2.clone(), n3.clone())),
            (Dim::XYZ(n1, n2, n3), DimCompo::Y) => Some(Dim::XZ(n1.clone(), n3.clone())),
            (Dim::XYZ(n1, n2, n3), DimCompo::Z) => Some(Dim::XY(n1.clone(), n2.clone())),
            (Dim::XY(n1, n2), DimCompo::X) => Some(Dim::Y(n2.clone())),
            (Dim::XY(n1, n2), DimCompo::Y) => Some(Dim::X(n1.clone())),
            (Dim::XZ(n1, n2), DimCompo::X) => Some(Dim::Z(n2.clone())),
            (Dim::XZ(n1, n2), DimCompo::Z) => Some(Dim::X(n1.clone())),
            (Dim::YZ(n1, n2), DimCompo::Y) => Some(Dim::Z(n2.clone())),
            (Dim::YZ(n1, n2), DimCompo::Z) => Some(Dim::Y(n1.clone())),
            (Dim::X(_), DimCompo::X) | (Dim::Y(_), DimCompo::Y) | (Dim::Z(_), DimCompo::Z) => None,
            _ => panic!("provided dimension component does not exist"),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum ThreadHierchyTy {
    // BlockGrp(gridDim.x, gridDim.y, gridDim.z, blockDim.x, blockDim.y, blockDim.z)
    BlockGrp(Dim, Dim),
    // ThreadGrp(blockDim.x, blockDim.y, blockDim.z)
    ThreadGrp(Dim),
    WarpGrp(Nat),
    Warp,
    Thread,
}

impl fmt::Display for ThreadHierchyTy {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use ThreadHierchyTy::*;
        match self {
            BlockGrp(d1, d2) => write!(f, "BlockGrp<{}, ThreadGrp<{}>>", d1, d2),
            ThreadGrp(d) => write!(f, "ThreadGrp<{}>", d),
            WarpGrp(n) => write!(f, "WarpGrp<{}>", n),
            Warp => write!(f, "Warp"),
            Thread => write!(f, "Thread"),
        }
    }
}

impl ThreadHierchyTy {
    pub fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Self {
        use ThreadHierchyTy::*;
        match self {
            BlockGrp(d1, d2) => BlockGrp(
                d1.subst_ident_kinded(ident_kinded, with),
                d2.subst_ident_kinded(ident_kinded, with),
            ),
            ThreadGrp(d) => ThreadGrp(d.subst_ident_kinded(ident_kinded, with)),
            WarpGrp(n) => WarpGrp(n.subst_ident_kinded(ident_kinded, with)),
            Warp => Warp,
            Thread => Thread,
        }
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
    pub constraints: Vec<Constraint>,
    #[span_derive_ignore]
    pub span: Option<Span>,
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
    Ref(Provenance, Ownership, Memory, Box<DataTy>),
    ThreadHierchy(Box<ThreadHierchyTy>),
    SplitThreadHierchy(DimCompo, Box<ThreadHierchyTy>, Nat),
    RawPtr(Box<DataTy>),
    Range,
    // Only for type checking purposes.
    Dead(Box<DataTy>),
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
            Ref(_, Ownership::Uniq, _, _) => true,
            Ref(_, Ownership::Shrd, _, _) => false,
            // FIXME thread hierarchies and their splits should be non-copyable!
            ThreadHierchy(_) => false,
            SplitThreadHierchy(_, _, _) => false,
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
            | Ref(_, _, _, _)
            // FIXME Thread hierarchies and their splits should be non-copyable and can therefore be dead
            | ThreadHierchy(_)
            | SplitThreadHierchy(_, _, _)
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
            DataTyKind::Scalar(_)
            | DataTyKind::Ident(_)
            | DataTyKind::ThreadHierchy(_)
            | DataTyKind::SplitThreadHierchy(_, _, _)
            | DataTyKind::Range => false,
            DataTyKind::Dead(_) => panic!("unexpected"),
            DataTyKind::Atomic(sty) => &self.dty == &DataTyKind::Scalar(sty.clone()),
            DataTyKind::Ref(_, _, _, elem_dty) => self.occurs_in(elem_dty),
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
            Scalar(_)
            | Atomic(_)
            | Ident(_)
            | Range
            | ThreadHierchy(_)
            | SplitThreadHierchy(_, _, _)
            | Dead(_) => false,
            Ref(prv, _, _, ty) => {
                let found_reference = if let Provenance::Value(prv_val_n) = prv {
                    prv_val_name == prv_val_n
                } else {
                    false
                };
                found_reference || ty.contains_ref_to_prv(prv_val_name)
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
            ThreadHierchy(th_hy) => DataTy::new(ThreadHierchy(Box::new(
                th_hy.subst_ident_kinded(ident_kinded, with),
            ))),
            SplitThreadHierchy(dim_compo, th_hy, n) => DataTy::new(SplitThreadHierchy(
                dim_compo.clone(),
                Box::new(th_hy.subst_ident_kinded(ident_kinded, with)),
                n.subst_ident_kinded(ident_kinded, with),
            )),
            Ref(prv, own, mem, dty) => DataTy::new(Ref(
                prv.subst_ident_kinded(ident_kinded, with),
                *own,
                mem.subst_ident_kinded(ident_kinded, with),
                Box::new(dty.subst_ident_kinded(ident_kinded, with)),
            )),
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

#[derive(PartialEq, Eq, Hash, Debug, Copy, Clone)]
pub enum ScalarTy {
    Unit,
    I32,
    U32,
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
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Memory::CpuMem => write!(f, "cpu.mem"),
            Memory::GpuGlobal => write!(f, "gpu.global"),
            Memory::GpuShared => write!(f, "gpu.shared"),
            Memory::GpuLocal => write!(f, "gpu.local"),
            Memory::Ident(x) => write!(f, "{}", x),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Copy, Clone)]
pub enum Exec {
    CpuThread,
    GpuGrid(u8),
    GpuBlock(u8),
    GpuWarp,
    GpuThread,
    View,
}

impl Exec {
    pub fn callable_in(self, exec: Self) -> bool {
        if self == Exec::View {
            true
        } else {
            self == exec
        }
    }
}

impl fmt::Display for Exec {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Exec::CpuThread => write!(f, "cpu.thread"),
            Exec::GpuGrid(dim_size) => write!(f, "gpu.grid{}d", dim_size),
            Exec::GpuBlock(dim_size) => write!(f, "gpu.block{}d", dim_size),
            Exec::GpuWarp => write!(f, "gpu.warp"),
            Exec::GpuThread => write!(f, "gpu.thread"),
            Exec::View => write!(f, "view"),
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
    BinOp(BinOpNat, Box<Nat>, Box<Nat>),
    App(Ident, Vec<Nat>),
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
            Nat::Ident(i) => Err(format!("Cannot evaluate identifier `{}`.", i)),
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
