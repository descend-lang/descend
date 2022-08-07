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
    pub item_defs: Vec<Item>,
    pub source: &'a SourceCode<'a>,
}

impl<'a> CompilUnit<'a> {
    pub fn new(item_defs: Vec<Item>, source: &'a SourceCode<'a>) -> Self {
        CompilUnit { item_defs, source }
    }
}


#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    FunDef(FunDef),
    StructDef(StructDef),
    TraitDef(TraitDef),
    ImplDef(ImplDef)
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunDef {
    pub name: String,
    pub generic_params: Vec<IdentKinded>,
    pub constraints: Vec<Constraint>,
    pub param_decls: Vec<ParamDecl>,
    pub ret_dty: DataTy,
    pub exec: Exec,
    pub prv_rels: Vec<PrvRel>,
    pub body_expr: Expr,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunDecl {
    pub name: String,
    pub generic_params: Vec<IdentKinded>,
    pub constraints: Vec<Constraint>,
    pub param_decls: Vec<ParamTypeDecl>,
    pub ret_dty: DataTy,
    pub exec: Exec,
    pub prv_rels: Vec<PrvRel>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructDef {
    pub name: String,
    pub generic_params: Vec<IdentKinded>,
    pub constraints: Vec<Constraint>,
    pub decls: Vec<StructField>,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct StructField {
    pub name: String,
    pub ty: DataTy,
}

impl StructDef {
    pub fn ty(&self) -> TypeScheme {
        let struct_ty = StructDataType {
            name: self.name.clone(),
            attributes:
                self.decls.iter()
                .map(|field|
                    StructField {
                    name: field.name.clone(),
                    ty: self.generic_params.iter()
                        .fold(field.ty.clone(), |res, gen|
                            res.subst_ident_kinded(gen, &gen.arg_kinded())
                        )
                    })
                .collect(),
            generic_args: self.generic_params.iter()
            .map(|gen| gen.arg_kinded()).collect(),
        };

        TypeScheme {
            generic_params: self.generic_params.clone(),
            constraints: self.constraints.clone(),
            mono_ty:
                Ty::new(TyKind::Data(DataTy::new(DataTyKind::Struct(struct_ty))))
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TraitDef {
    pub name: String,
    pub generic_params: Vec<IdentKinded>,
    pub constraints: Vec<Constraint>,
    pub decls: Vec<AssociatedItem>,
    pub supertraits: Vec<TraitMonoType>
}

#[derive(Debug, Clone, PartialEq)]
pub struct ImplDef {
    pub dty: DataTy,
    pub generic_params: Vec<IdentKinded>,
    pub constraints: Vec<Constraint>,
    pub decls: Vec<AssociatedItem>,
    pub trait_impl: Option<TraitMonoType>
}

impl ImplDef {
    pub fn ty(&self) -> TypeScheme {
        TypeScheme {
            generic_params: self.generic_params.clone(),
            constraints: self.constraints.clone(),
            mono_ty: Ty::new(TyKind::Data(self.dty.clone()))
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum AssociatedItem {
    FunDef(FunDef),
    FunDecl(FunDecl),
    ConstItem(String, DataTy, Option<Expr>)
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct Constraint {
    pub param: DataTy,
    pub trait_bound: TraitMonoType,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct TraitMonoType {
    pub name: String,
    pub generics: Vec<ArgKinded>
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct StructDataType {
    pub name: String,
    pub attributes: Vec<StructField>,
    pub generic_args: Vec<ArgKinded>,
}

impl StructDataType {
    pub fn get_ty(&self, name: &String) -> Option<&DataTy> {
        match self.attributes.iter()
            .find(|field|
                field.name == *name) {
            Some(field) => Some(&field.ty),
            None => None
        }
    }

    pub fn get_ty_mut(&mut self, name: &String) -> Option<&mut DataTy> {
        match self.attributes.iter_mut()
            .find(|field|
                field.name == *name) {
            Some(field) => Some(&mut field.ty),
            None => None
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct FunctionName {
    pub name: String,
    pub fun_kind: FunctionKind
}

impl FunctionName {
    pub fn global_fun(name: &str) -> Self {
        FunctionName {
            name: String::from(name),
            fun_kind: FunctionKind::GlobalFun
        }
    }

    pub fn from_impl(name: &str, impl_def: &ImplDef) -> Self {
        let trait_name = 
            if impl_def.trait_impl.is_some() {
                Some(impl_def.trait_impl.unwrap().name)
            } else {
                None
            };
        FunctionName {
            name: String::from(name),
            fun_kind: FunctionKind::ImplFun(impl_def.ty(), trait_name)
        }
    }

    pub fn from_trait(name: &str, trait_def: &TraitDef) -> Self {
        FunctionName {
            name: String::from(name),
            fun_kind: FunctionKind::TraitFun(trait_def.name)
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum Path {
    Empty,
    DataTy(DataTy),
    InferFromFirstArg, //Replaced in type_checking through DataTy
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum FunctionKind {
    GlobalFun,
    //Typescheme of impl, and (if existing) trait which is implemented
    ImplFun(TypeScheme, Option<String>),
    TraitFun(String),
}

pub trait SubstKindedIdents where Self: Sized + Clone {
    fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Self;
    
    fn subst_idents_kinded<'a, 'b, I, J>(&self, ident_kinded: I, with: J) -> Self
    where
        I: ExactSizeIterator<Item = &'a IdentKinded>,
        J: ExactSizeIterator<Item = &'b ArgKinded>
    {
        assert!(ident_kinded.len() == with.len());
        ident_kinded
        .zip(with)
        .fold(self.clone(), |res, (ident, with)|
            res.subst_ident_kinded(ident, with)
        )
    }
}

impl SubstKindedIdents for TraitMonoType {
    fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Self {
        TraitMonoType {
            name: self.name.clone(),
            generics: self.generics.iter().map(|arg|
                arg.subst_ident_kinded(ident_kinded, with)).collect()
        }
    }
}

impl SubstKindedIdents for Constraint {
    fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Self {
        Constraint {
            param: self.param.subst_ident_kinded(ident_kinded, with),
            trait_bound: self.trait_bound.subst_ident_kinded(ident_kinded, with)
        }
    }
}

impl TraitDef {
    pub fn supertraits_constraints(&self) -> Vec<Constraint> {
        let self_ident = Ident::new("Self");
        let self_ty = DataTy::new(DataTyKind::Ident(self_ident.clone()));

        self.supertraits.iter().map(|supertrait| 
            Constraint { param: self_ty.clone(), trait_bound: supertrait.clone() }
        ).collect()
    }
}

impl FunDef {
    pub fn ty(&self) -> TypeScheme {
        let param_tys: Vec<_> = self
            .param_decls
            .iter()
            .map(|p_decl| p_decl.ty.as_ref().unwrap().clone())
            .collect();
        TypeScheme {
            generic_params: self.generic_params.clone(),
            constraints: self.constraints.clone(),
            mono_ty: Ty::new(TyKind::Fn(
                param_tys,
                self.exec,
                Box::new(Ty::new(TyKind::Data(self.ret_dty.clone()))),
            ))
        }
    }
}

impl FunDecl {
    pub fn ty(&self) -> TypeScheme {
        let param_tys: Vec<_> = self
            .param_decls
            .iter()
            .map(|p_decl| p_decl.ty.clone())
            .collect();
        TypeScheme {
            generic_params: self.generic_params.clone(),
            constraints: self.constraints.clone(),
            mono_ty: Ty::new(TyKind::Fn(
                param_tys,
                self.exec,
                Box::new(Ty::new(TyKind::Data(self.ret_dty.clone()))),
            ))
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParamDecl {
    pub ident: Ident,
    pub ty: Option<Ty>,
    pub mutbl: Mutability,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParamTypeDecl {
    pub ty: Ty,
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
                                    *expr = Expr::new(ExprKind::Proj(Box::new(tuple_expr), i.clone()));
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

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum ProjEntry {
    TupleAccess(usize),
    StructAccess(String),
}

#[derive(PartialEq, Debug, Clone)]
pub enum ExprKind {
    Lit(Lit),
    // An l-value equivalent: *p, p.n, x
    PlaceExpr(PlaceExpr),
    // Index into array, e.g., arr[i]
    Index(PlaceExpr, Nat),
    // e.g., [1, 2 + 3, 4]
    Array(Vec<Expr>),
    Tuple(Vec<Expr>),
    // e.g., structName <generic1> { name: String::from("Test") }
    StructInst(String, Vec<ArgKinded>, Vec<(Ident, Expr)>),
    // Projection, e.g. e.1, for non place expressions, e.g. f(x).1
    Proj(Box<Expr>, ProjEntry),
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
    // Struct::<T>::e_f(e_1, ..., e_n)
    // FunctionKind is inferred while typechecking
    App(Path, Option<FunctionKind>, Box<Expr>, Vec<ArgKinded>, Vec<Expr>),
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

impl SubstKindedIdents for ArgKinded {
    fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Self {
        match self {
            ArgKinded::Ident(ident) =>
                if ident.name == ident_kinded.ident.name {
                    with.clone()
                } else {
                    ArgKinded::Ident(ident.clone())
                },
            ArgKinded::Nat(nat) =>
                ArgKinded::Nat(nat.subst_ident_kinded(ident_kinded, with)),
            ArgKinded::Memory(mem) =>
                ArgKinded::Memory(mem.subst_ident_kinded(ident_kinded, with)),
            ArgKinded::Ty(ty) =>
                ArgKinded::Ty(ty.subst_ident_kinded(ident_kinded, with)),
            ArgKinded::DataTy(dty) =>
                ArgKinded::DataTy(dty.subst_ident_kinded(ident_kinded, with)),
            ArgKinded::Provenance(prov) =>
                ArgKinded::Provenance(prov.subst_ident_kinded(ident_kinded, with)),
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
    Proj(Box<PlaceExpr>, ProjEntry),
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
                        pl = pl.push(n);
                        (pl_ctx, internal::Place::new(pl.ident, pl.path))
                    }
                    _ => (internal::PlaceCtx::Proj(Box::new(pl_ctx), n.clone()), pl),
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
            PlaceExprKind::Proj(pl_expr, n) =>
               match n {
                ProjEntry::TupleAccess(n) => write!(f, "{}.{}", pl_expr, n),
                ProjEntry::StructAccess(n) => write!(f, "{}.{}", pl_expr, n),
               },
            PlaceExprKind::Deref(pl_expr) => write!(f, "*{}", pl_expr),
            PlaceExprKind::Ident(ident) => write!(f, "{}", ident),
        }
    }
}

#[span_derive(PartialEq, Eq, Hash)]
#[derive(Debug, Clone)]
pub struct TypeScheme {
    pub generic_params: Vec<IdentKinded>,
    pub constraints: Vec<Constraint>,
    pub mono_ty: Ty
}

impl TypeScheme {
    pub fn new(ty: Ty) -> Self {
        TypeScheme {
            generic_params: vec![],
            constraints: vec![],
            mono_ty: ty
        }
    }

    pub fn is_mono(&self) -> bool {
        self.generic_params.len() == 0 && self.constraints.len() == 0
    }

    pub fn as_mono(&self) -> Option<Ty> {
        if self.is_mono() {
            Some(self.mono_ty.clone())
        } else {
            None
        }
    }

    fn substitute<T: SubstKindedIdents + Clone>(&self, x: &T, with: &[ArgKinded]) -> T {
        self.generic_params[0..with.len()]
            .iter()
            .zip(with.iter())
            .fold(x.clone(), |x, (ident_kinded, with)|
                x.subst_ident_kinded(ident_kinded, with))
    }

    pub fn instantiate(&self, with: &[ArgKinded]) -> Self {
        assert!(self.generic_params.len() >= with.len());
        TypeScheme {
            generic_params: self.generic_params[with.len()..].to_vec(),
            constraints:
                self.constraints
                .iter()
                .map(|con|
                    self.substitute(con, with))
                .collect(),
            mono_ty:
                self.substitute(&self.mono_ty, with),
        }
    }

    pub fn eq_structure(&self, other: &Self) -> bool {
        if self.generic_params.len() == other.generic_params.len() &&
            self.generic_params
            .iter()
            .zip(other.generic_params.iter())
            .fold(true, |res, (gen1, gen2)|
                res && gen1.kind == gen2.kind
            ) {
            let args = self.generic_params.iter()
                .map(|gen|
                    gen.arg_kinded()
                ).collect::<Vec<ArgKinded>>();
            self.instantiate(args.as_slice())
                .eq_structure(&other.instantiate(args.as_slice()))
        } else {
            false
        }
    }
}

#[span_derive(PartialEq, Eq, Hash)]
#[derive(Debug, Clone)]
pub struct Ty {
    pub ty: TyKind,
    pub constraints: Vec<ConstraintOld>,
    #[span_derive_ignore]
    pub span: Option<Span>,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum TyKind {
    Data(DataTy),
    Fn(Vec<Ty>, Exec, Box<Ty>),
    Ident(Ident),
    Dead(Box<Ty>),
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub enum ConstraintOld {
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

    pub fn with_constr(ty: TyKind, constraints: Vec<ConstraintOld>) -> Ty {
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
            TyKind::Fn(_, _, _) => true,
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
            TyKind::Ident(_) | TyKind::Fn( _, _, _) => true,
            TyKind::Dead(_) => false,
        }
    }

    pub fn eq_structure(&self, other: &Self) -> bool {
        match (&self.ty, &other.ty) {
            (TyKind::Fn(ptys1, exec1, ret_ty1),
             TyKind::Fn(ptys2, exec2, ret_ty2)) => {
                let mut res = true;
                for (pty1, pty2) in ptys1.iter().zip(ptys2) {
                    res &= pty1.eq_structure(pty2);
                }
                res &= exec1 == exec2;
                res & ret_ty1.eq_structure(ret_ty2)
            }
            (TyKind::Data(dty1), TyKind::Data(dty2)) => dty1.eq_structure(dty2),
            (TyKind::Ident(id1), TyKind::Ident(id2)) =>
                if id1.is_implicit && id2.is_implicit {
                    true
                } else {
                    id1.name == id2.name
                }
            (TyKind::Dead(ty1), TyKind::Dead(ty2)) => ty1.eq_structure(ty2),
            _ => false,
        }
    }

    pub fn contains_ref_to_prv(&self, prv_val_name: &str) -> bool {
        match &self.ty {
            TyKind::Data(dty) => dty.contains_ref_to_prv(prv_val_name),
            TyKind::Fn(param_tys, _, ret_ty) => {
                param_tys
                    .iter()
                    .any(|param_ty| param_ty.contains_ref_to_prv(prv_val_name))
                    || ret_ty.contains_ref_to_prv(prv_val_name)
            }
            TyKind::Ident(_) | TyKind::Dead(_) => false,
        }
    }
}

impl SubstKindedIdents for Ty {
    fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Self {
        match &self.ty {
            // TODO mutate and do not create a new type (also this drops the span).
            TyKind::Data(dty) =>
                Ty::new(TyKind::Data(dty.subst_ident_kinded(ident_kinded, with))),
            TyKind::Fn(params, exec, ret) => Ty::new(TyKind::Fn(
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
                        ArgKinded::DataTy(dty) => Ty::new(TyKind::Data(dty.clone())),
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
pub enum ThreadHierchyTy {
    // BlockGrp(gridDim.x, gridDim.y, gridDim.z, blockDim.x, blockDim.y, blockDim.z)
    BlockGrp(Nat, Nat, Nat, Nat, Nat, Nat),
    // ThreadGrp(blockDim.x, blockDim.y, blockDim.z)
    ThreadGrp(Nat, Nat, Nat),
    WarpGrp(Nat),
    Warp,
    Thread,
}

impl fmt::Display for ThreadHierchyTy {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use ThreadHierchyTy::*;
        match self {
            BlockGrp(n1, n2, n3, m1, m2, m3) => write!(
                f,
                "BlockGrp<{}, {}, {}, ThreadGrp<{}, {}, {}>>",
                n1, n2, n3, m1, m2, m3
            ),
            ThreadGrp(n1, n2, n3) => write!(f, "ThreadGrp<{}, {}, {}>", n1, n2, n3),
            WarpGrp(n) => write!(f, "WarpGrp<{}>", n),
            Warp => write!(f, "Warp"),
            Thread => write!(f, "Thread"),
        }
    }
}

impl SubstKindedIdents for ThreadHierchyTy {
    fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Self {
        use ThreadHierchyTy::*;
        match self {
            BlockGrp(n1, n2, n3, m1, m2, m3) => BlockGrp(
                n1.subst_ident_kinded(ident_kinded, with),
                n2.subst_ident_kinded(ident_kinded, with),
                n3.subst_ident_kinded(ident_kinded, with),
                m1.subst_ident_kinded(ident_kinded, with),
                m2.subst_ident_kinded(ident_kinded, with),
                m3.subst_ident_kinded(ident_kinded, with),
            ),
            ThreadGrp(n1, n2, n3) => ThreadGrp(
                n1.subst_ident_kinded(ident_kinded, with),
                n2.subst_ident_kinded(ident_kinded, with),
                n3.subst_ident_kinded(ident_kinded, with),
            ),
            WarpGrp(n) => WarpGrp(n.subst_ident_kinded(ident_kinded, with)),
            Warp => Warp,
            Thread => Thread,
        }
    }
}

#[span_derive(PartialEq, Eq, Hash)]
#[derive(Debug, Clone)]
pub struct DataTy {
    pub dty: DataTyKind,
    pub constraints: Vec<ConstraintOld>,
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
    Struct(StructDataType),
    At(Box<DataTy>, Memory),
    Ref(Provenance, Ownership, Memory, Box<DataTy>),
    ThreadHierchy(Box<ThreadHierchyTy>),
    SplitThreadHierchy(Box<ThreadHierchyTy>, Nat),
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

    pub fn with_constr(dty: DataTyKind, constraints: Vec<ConstraintOld>) -> Self {
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
            SplitThreadHierchy(_, _) => false,
            At(_, _) => true,
            ArrayShape(_, _) => true,
            Tuple(elem_tys) => elem_tys.iter().any(|ty| ty.non_copyable()),
            Struct(struct_ty) =>
                struct_ty.attributes.iter().any(|field| field.ty.non_copyable()),
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
            | SplitThreadHierchy(_, _)
            | At(_, _)
            | Array(_, _)
            | ArrayShape(_, _) => true,
            Tuple(elem_tys) => elem_tys
                .iter()
                .fold(true, |acc, ty| acc & ty.is_fully_alive()),
            Struct(struct_ty) =>
                struct_ty.attributes.iter()
                .fold(true, |acc, field| acc & field.ty.is_fully_alive()),
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
            | DataTyKind::SplitThreadHierchy(_, _)
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
            DataTyKind::Struct(_) => unimplemented!("TODO"),
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
            | SplitThreadHierchy(_, _)
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
            Struct(struct_ty) => struct_ty.attributes
                .iter()
                .any(|field| field.ty.contains_ref_to_prv(prv_val_name)),
        }
    }

    pub fn eq_structure(&self, other: &Self) -> bool {
        match (&self.dty, &other.dty) {
            (DataTyKind::Ident(i1), DataTyKind::Ident(i2)) =>
                i1.name == i2.name,
            (DataTyKind::Scalar(sct1), DataTyKind::Scalar(sct2)) => 
                sct1 == sct2,
            (DataTyKind::Atomic(sct1), DataTyKind::Atomic(sct2)) =>
                sct1 == sct2,
            (DataTyKind::Array(ty1, n1), DataTyKind::Array(ty2, n2)) =>
                n1 == n2 && ty1.eq_structure(ty2),
            (DataTyKind::ArrayShape(ty1, n1), DataTyKind::ArrayShape(ty2, n2)) =>
                n1 == n2 && ty1.eq_structure(ty2),
            (DataTyKind::Tuple(dtys1), DataTyKind::Tuple(dtys2)) =>
                dtys1.len() == dtys1.len() &&
                    dtys1.iter()
                    .zip(dtys2.iter()).
                    fold(true, |res, (dty1, dty2)|
                        res && dty1.eq_structure(dty2)
                ),
            (DataTyKind::Struct(st1), DataTyKind::Struct(st2)) =>
                st1.name == st2.name && st1.generic_args.len() == st2.generic_args.len() &&
                    st1.generic_args.iter()
                    .zip(st2.generic_args.iter())
                    .fold(true, |res, (gen1, gen2)|
                        res &&
                            match (gen1, gen2) {
                                (ArgKinded::Nat(n1), ArgKinded::Nat(n2)) =>
                                    n1 == n2,
                                (ArgKinded::Memory(mem1), ArgKinded::Memory(mem2)) =>
                                    mem1 == mem2,
                                (ArgKinded::Ty(ty1), ArgKinded::Ty(ty2)) =>
                                    ty1.eq_structure(ty2),
                                (ArgKinded::DataTy(dty1), ArgKinded::DataTy(dty2)) =>
                                    dty1.eq_structure(dty2),
                                (ArgKinded::Provenance(prov1), ArgKinded::Provenance(prov2)) =>
                                    prov1 == prov2,
                                _ => false
                            }
                ),
            (DataTyKind::At(ty1, mem1), DataTyKind::At(ty2, mem2)) =>
                mem1 == mem2 && ty1.eq_structure(ty2),
            (DataTyKind::Ref(prov1, own1, mem1, ty1),
             DataTyKind::Ref(prov2, own2, mem2, ty2)) =>
                own1 == own2 && mem1 == mem2 && ty1.eq_structure(ty2) &&
                    match (prov1, prov2) {
                        (Provenance::Ident(i1), Provenance::Ident(i2)) => 
                            if i1.is_implicit && i2.is_implicit {
                                true
                            } else {
                                i1 == i2
                            },
                        _ => prov1 == prov2,    
                    },
            (DataTyKind::ThreadHierchy(tht1),
             DataTyKind::ThreadHierchy(tht2)) =>
                tht1 == tht2,
            (DataTyKind::SplitThreadHierchy(tht1, n1),
             DataTyKind::SplitThreadHierchy(tht2, n2)) =>
                n1 == n2 && tht1 == tht2,
            (DataTyKind::RawPtr(ty1), DataTyKind::RawPtr(ty2)) =>
                ty1.eq_structure(ty2),
            (DataTyKind::Range, DataTyKind::Range) =>
                true,
            (DataTyKind::Dead(ty1), DataTyKind::Dead(ty2)) =>
                ty1.eq_structure(ty2),
            _ => false
        }
    }
}

impl SubstKindedIdents for DataTy {
    fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Self {
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
            SplitThreadHierchy(th_hy, n) => DataTy::new(SplitThreadHierchy(
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
            Struct(struct_ty) =>
                DataTy::new(DataTyKind::Struct(super::ast::StructDataType{
                    name: struct_ty.name.clone(),
                    attributes:
                        struct_ty.attributes.iter().map(|field|
                            StructField {
                                name: field.name.clone(),
                                ty: field.ty.subst_ident_kinded(ident_kinded, with)
                            }
                        ).collect(),
                    generic_args: struct_ty.generic_args.iter().map(|gen_arg|
                        gen_arg.subst_ident_kinded(ident_kinded, with)).collect(),
                })),
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

impl SubstKindedIdents for Provenance {
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

impl SubstKindedIdents for Memory {
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
    GpuGrid,
    GpuBlock,
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
            Exec::GpuGrid => write!(f, "gpu.grid"),
            Exec::GpuBlock => write!(f, "gpu.block"),
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

    pub fn arg_kinded(&self) -> ArgKinded {
        self.arg_kinded_with_name(self.ident.name.clone())
    }

    pub fn arg_kinded_with_name(&self, name: String) -> ArgKinded {
        let mut ident = self.ident.clone();
        ident.name = name;
        match self.kind {
            Kind::DataTy =>
                ArgKinded::DataTy(DataTy::new(DataTyKind::Ident(ident))),
            Kind::Memory =>
                ArgKinded::Memory(Memory::Ident(ident)),
            Kind::Nat =>
                ArgKinded::Nat(Nat::Ident(ident)),
            Kind::Provenance =>
                ArgKinded::Provenance(Provenance::Ident(ident)),
            Kind::Ty =>
                ArgKinded::Ty(Ty::new(TyKind::Ident(ident))),
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
}

impl SubstKindedIdents for Nat {
    fn subst_ident_kinded(&self, ident_kinded: &IdentKinded, with: &ArgKinded) -> Nat {
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
