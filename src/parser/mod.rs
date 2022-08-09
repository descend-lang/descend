//! Module for components related to parsing
pub mod source;
mod utils;

use crate::ast::{*, visit_mut::{walk_expr, walk_arg_kinded}};
use error::ParseError;
use std::collections::{BTreeMap};

use crate::error::ErrorReported;
pub use source::*;

use crate::ast::visit_mut::{VisitMut, walk_struct_def, walk_impl_def,
    walk_trait_def, walk_fun_def, walk_dty};


pub fn parse<'a>(source: &'a SourceCode<'a>) -> Result<CompilUnit, ErrorReported> {
    let parser = Parser::new(source);
    let mut item_defs =
        parser
        .parse()
        .map_err(|err| err.emit())?;
    visit_ast(&mut item_defs);
    Ok(CompilUnit::new(
        item_defs,
        source,
    ))
}

#[derive(Debug)]
struct Parser<'a> {
    source: &'a SourceCode<'a>,
}

impl<'a> Parser<'a> {
    fn new(source: &'a SourceCode<'a>) -> Self {
        Parser { source }
    }

    fn parse(&self) -> Result<Vec<Item>, ParseError<'_>> {
        descend::compil_unit(self.source.str()).map_err(|peg_err| ParseError::new(self, peg_err))
    }
}

fn visit_ast(items: &mut Vec<Item>) { //TODO find a proper name
    struct Visitor {
        structs: BTreeMap<String, StructDef>,
        ident_kinded_in_scope: Vec<(String, Kind)>,
        impl_dty_in_scope: Option<DataTy>
    }

    impl Visitor {
        fn new(items: &Vec<Item>) -> Self {
            Visitor {
                structs: BTreeMap::from_iter(
                    items.iter().filter_map(|item| 
                        if let Item::StructDef(struct_def) = item {
                            Some((struct_def.name.clone(), struct_def.clone()))
                        } else {
                            None
                }
                    )),
                ident_kinded_in_scope: Vec::with_capacity(32),
                impl_dty_in_scope: None
                                }
                                }

        fn add_generics(&mut self, generics: &Vec<IdentKinded>) {
            self.add_ident_kinded(generics.iter().map(|ident_kinded|
                (ident_kinded.ident.name.clone(), ident_kinded.kind)));
                                }

        fn add_ident_kinded<I>(&mut self, ident_kinded: I) where I: Iterator<Item = (String, Kind)> {
            self.ident_kinded_in_scope.extend(ident_kinded);
                            }

        fn pop_ident_kinded(&mut self, n: usize) {
            self.ident_kinded_in_scope.truncate(self.ident_kinded_in_scope.len() - n);
                        }

        fn get_kind(&self, ident: &Ident) -> &Kind {
            if let Some((_, kind)) = self.ident_kinded_in_scope.iter().rev().find(|(name, _)|
                *name == ident.name
            ) {
                kind
            } else {
                panic!("Could not find kind of identifier \"{}\"", ident); //TODO throw error instead of panic
                    }
                }

        fn contains_ident_kinded(&self, name: &str) -> bool {
            self.ident_kinded_in_scope
            .iter()
            .rev()
            .find(|(generic_name, _)|
                generic_name == name
            ).is_some()
            }
        }

    //Replace ArgKinded::Ident-identifier with ArgKinded-Identifier of correct kind
    fn replace_arg_kinded_kind(visitor: &Visitor, arg: &mut ArgKinded){
        if let ArgKinded::Ident(ident) = arg {
            *arg = 
                match visitor.get_kind(&ident) {
                    Kind::Provenance => 
                        ArgKinded::Provenance(Provenance::Ident(ident.clone())),
                    Kind::Memory =>
                        ArgKinded::Memory(Memory::Ident(ident.clone())),
                    Kind::Nat =>
                        ArgKinded::Nat(Nat::Ident(ident.clone())),
                    Kind::Ty =>
                        // TODO how to deal with View??!! This is a problem!
                        //  Ident only for Ty but not for DataTy or ViewTy?
                        ArgKinded::Ty(Ty::new(TyKind::Data(DataTy::new(
                            DataTyKind::Ident(ident.clone()),
                        )))),
                    Kind::DataTy => 
                        ArgKinded::DataTy(DataTy::new(
                            DataTyKind::Ident(ident.clone()),
                        )),
                    _ => panic!("This kind can not be referred to with an identifier."),
        }
    }
}

//Replace the special ident "Self" in impls with the type of the impl
    fn replace_self_in_impls(visitor: &Visitor, dty: &mut DataTy) {
        if let Some(impl_dty_in_scope) = &visitor.impl_dty_in_scope {
            if let DataTyKind::Ident(ident) = &dty.dty {
                    if ident.name == "Self" {
                    *dty = impl_dty_in_scope.clone();
                    }
            }
        }
    }

//Distinguish between type variables and struct names without generic params
    fn replace_tyidents_struct_names(visitor: &Visitor, dty: &mut DataTy) {
        if let DataTyKind::Ident(name) = &mut dty.dty {
            let struct_def = visitor.structs.get(&name.name);
            let is_type_ident = visitor.contains_ident_kinded(&name.name);

            match (struct_def.is_some(), is_type_ident) {
                (true, false) => 
                    dty.dty =
                        match struct_def.unwrap().ty().mono_ty.ty {
                            TyKind::Data(dty) => dty.dty,
                            _ => panic!("Struct should have a Datatype!"),
                        },
                (false, true) | (false, false) =>
                    (),
                (true, true) => 
                    panic!("AmbiguousIdentifier"), //TODO throw error instead of panic
                    // self.errs.push(
                    //     TyError::from(CtxError::AmbiguousIdentifier(name.clone()))),
                        }
            }
        }

    //Initialize attributes list of struct_types
    fn initialize_struct_attribute_lists(visitor: &Visitor, dty: &mut DataTy) {
        if let DataTyKind::Struct(struct_ty) = &mut dty.dty {
            if struct_ty.attributes.len() == 0 {
            if let Some(struct_def) = visitor.structs.get(&struct_ty.name) {
                let inst_struct_mono = struct_def.ty().instantiate(&struct_ty.generic_args).mono_ty;
                if let TyKind::Data(dataty) = inst_struct_mono.ty {
                    if let DataTyKind::Struct(inst_struct_ty) = dataty.dty {
                        struct_ty.attributes = inst_struct_ty.attributes;
                    } else {
                        panic!("Instantiated struct def should have struct type")
        }
                } else {
                    panic!("Instantiated struct def should have struct type")
                }
            } else {
                panic!("TODO print some err instead of panic")
            }
        }
    }
    }

    impl VisitMut for Visitor {
        fn visit_item_def(&mut self, item_def: &mut Item) { 
            match item_def {
                Item::FunDef(fun_def) => {
                    self.visit_fun_def(fun_def);
                },
                Item::StructDef(struct_def) => {
                    self.add_generics(&struct_def.generic_params);
                    walk_struct_def(self, struct_def);
                    self.ident_kinded_in_scope.clear();
                },
                Item::TraitDef(trait_def) => {
                    self.add_generics(&trait_def.generic_params);
                    walk_trait_def(self, trait_def);
                    self.ident_kinded_in_scope.clear();
                },
                Item::ImplDef(impl_def) => {
                    self.add_generics(&impl_def.generic_params);
                    self.impl_dty_in_scope = Some(impl_def.dty.clone());
                    walk_impl_def(self, impl_def);
                    self.impl_dty_in_scope = None;
                    self.ident_kinded_in_scope.clear();
                },
            }
         }

        fn visit_fun_def(&mut self, fun_def: &mut FunDef) {
            self.add_generics(&fun_def.generic_params);
            walk_fun_def(self, fun_def);
            self.pop_ident_kinded(fun_def.generic_params.len());
        }

        fn visit_expr(&mut self, expr: &mut Expr) {
            match &mut expr.expr {
                ExprKind::Block(prvs, body) => {
                    self.add_ident_kinded(
                        prvs.iter().map(|prv| (prv.clone(), Kind::Provenance)));
                    self.visit_expr(body);
                    self.pop_ident_kinded(prvs.len());
                                },
                ExprKind::ForNat(ident, _, body) => {
                    self.ident_kinded_in_scope.push((ident.name.clone(), Kind::Nat));
                    self.visit_expr(body);
                    self.ident_kinded_in_scope.pop();
                },
                _ => {
                    walk_expr(self, expr);
                            }
                        }
                    }

        fn visit_dty(&mut self, dty: &mut DataTy) {
            replace_self_in_impls(self, dty);
            replace_tyidents_struct_names(self, dty);
            initialize_struct_attribute_lists(self, dty);
            walk_dty(self, dty);
            }

        fn visit_arg_kinded(&mut self, arg_kinded: &mut ArgKinded) {
            replace_arg_kinded_kind(self, arg_kinded);
            walk_arg_kinded(self, arg_kinded);
        }
    }

    let mut visitor = Visitor::new(items);
    items.iter_mut().for_each(|item_def|
        visitor.visit_item_def(item_def)
    )
}

pub mod error {
    use crate::error::ErrorReported;
    use crate::parser::{Parser, SourceCode};
    use annotate_snippets::display_list::DisplayList;
    use annotate_snippets::snippet::Snippet;
    use peg::error::ParseError as PegError;
    use peg::str::LineCol;

    #[must_use]
    #[derive(Debug)]
    pub struct ParseError<'a> {
        parser: &'a Parser<'a>,
        err: PegError<LineCol>,
    }

    impl<'a> ParseError<'a> {
        pub(super) fn new(parser: &'a Parser, err: PegError<LineCol>) -> Self {
            ParseError { parser, err }
        }

        pub fn emit(&self) -> ErrorReported {
            let label = format!("expected {}", self.err.expected);
            let line_num = self.err.location.line;
            let column_num = self.err.location.column;
            let snippet = single_line_parse_snippet(
                self.parser.source,
                &label,
                line_num,
                column_num,
                column_num + 1,
            );
            println!("{}", DisplayList::from(snippet).to_string());
            ErrorReported
        }
    }

    fn single_line_parse_snippet<'a>(
        source: &'a SourceCode<'a>,
        label: &'a str,
        line_num: usize,
        begin_column: usize,
        end_column: usize,
    ) -> Snippet<'a> {
        // 1-based offsets to 0-based offsets
        crate::error::single_line_snippet(
            source,
            label,
            line_num - 1,
            begin_column - 1,
            end_column - 1,
        )
    }
}

peg::parser! {
    pub(crate) grammar descend() for str {

        pub(crate) rule compil_unit() -> Vec<Item>
            = _ items:(item:item() { item }) ** _ _ {
                items
            }

        pub(crate) rule item() -> Item
            = result:(f: fun_def() { Item::FunDef(f) }
            / s: struct_def() { Item::StructDef(s) }
            / t: trait_def() { Item::TraitDef(t) }
            / i: trait_impl_def() { Item::ImplDef(i) }
            / i: inherent_impl_def() { Item::ImplDef(i) }) {
                result
            }    

        pub(crate) rule fun_def() -> FunDef
            = "fn" __ name:identifier() _ generic_params:generic_params()? _
            "(" _ param_decls:(fun_parameter() ** (_ "," _)) _ ")" _
            "-" _ "[" _ exec:execution_resource() _ "]" _ "-" _ ">"
            _ ret_dty:dty() _ w:where_clause()? _ body_expr:block() {
                let generic_params = match generic_params {
                    Some(generic_params) => generic_params,
                    None => vec![]
                };
                let constraints = w.unwrap_or(vec![]);
                FunDef {
                    name,
                    generic_params,
                    constraints,
                    param_decls,
                    ret_dty,
                    exec,
                    prv_rels: vec![],
                    body_expr
                }
        }

        pub(crate) rule fun_decl() -> FunDecl
            = "fn" __ name:identifier() _ g:generic_params()? _
            "(" _ param_decls:(p:fun_decl_param() ** (_ "," _) {p}) _ ")" _ 
            exec:("-" _ "[" _ e:execution_resource() _ "]" {e}) _ w:where_clause()? _
            "-" _ ">" _ ret_dty:dty() _ ";" {
                let generic_params =
                    match g {
                        Some(x) => x,
                        None => Vec::new()
                    };
                let constraints = w.unwrap_or(vec![]);
                FunDecl {
                    name,
                    generic_params,
                    constraints,
                    param_decls,
                    ret_dty,
                    exec,
                    prv_rels: vec![],
                }
        }

        pub(crate) rule struct_def() -> StructDef
            = "struct" __ name:identifier() _ g:generic_params()?  _  w:where_clause()? _ 
            struct_fields:(u:("{" t:(_ s:(struct_field() ** (_ "," _)) _ {s})? "}" {t}) {Some(u)}
                            / ";" {None}) _ {
                let generic_params = g.unwrap_or(vec![]);
                let constraints = w.unwrap_or(vec![]);
                let decls: Vec<StructField> = match struct_fields {
                    Some(struct_fields) => match struct_fields {Some(s) => s, None => vec![]},
                    None => vec![]
                };
                StructDef {
                    name,
                    generic_params,
                    constraints,
                    decls,
                }
            }
        
        pub(crate) rule trait_def() -> TraitDef 
            = "trait" __ name:identifier() _ g:generic_params()?
            supertraits:(":" _ t:trait_mono_ty() ** (_ "+" _) {t})?
            _ w:where_clause()? _ "{" _ decls:(_ i:associated_item() ** _ {i}) _ "}"   {
                let generic_params = g.unwrap_or(vec![]);
                let mut constraints = w.unwrap_or(vec![]);
                TraitDef {
                    name,
                    generic_params,
                    constraints,
                    decls,
                    supertraits: supertraits.unwrap_or(vec![])
                }
            }

        rule trait_mono_ty() -> TraitMonoType
            = name:identifier() generic_args:(_ "<" _ generic_args:(k:kind_argument() ** (_ "," _) {k}) _ ">" { generic_args })? { 
                TraitMonoType { name, generics: generic_args.unwrap_or(vec![]) }
            }

        pub(crate) rule inherent_impl_def() -> ImplDef    
            = "impl" _ g:generic_params()? _ dty:dty() _ w:where_clause()? _
            "{" _ decls:(_ i:associated_item() ** _ {i}) _ "}" {
                let generic_params = g.unwrap_or(vec![]);
                let constraints = w.unwrap_or(vec![]);
                ImplDef { dty, generic_params, constraints, decls, trait_impl: None}
            }

        pub(crate) rule trait_impl_def() -> ImplDef 
            = "impl" _ g:generic_params()? _ trait_impl:trait_mono_ty() __ "for" __
            dty:dty() _ w:where_clause()? _ "{" _
            decls:(_ i:associated_item() ** _ {i}) _ "}" {
                let generic_params = g.unwrap_or(vec![]);
                let constraints = w.unwrap_or(vec![]);
                ImplDef { dty, generic_params, constraints, decls, trait_impl: Some(trait_impl)}
        }

        rule struct_field() -> StructField
            = name:identifier() _ ":" _ ty:dty() {
                StructField {name, ty}
        }

        rule associated_item() -> AssociatedItem
            = ass_item:(f:fun_def() {AssociatedItem::FunDef(f)}
            / f:fun_decl() {AssociatedItem::FunDecl(f)}
            / const_item:("const" __ name:identifier() _ ":"
                _ dty:dty() expr:(_ "=" _ e:expression() {e})? _
                ";" {AssociatedItem::ConstItem(name, dty, expr)})) {
                    ass_item
            }

        rule generic_params() -> Vec<IdentKinded>
        = params:("<" _ t:(kind_parameter() ** (_ "," _)) _ ">" {t}) {
            params
        }

        // only syntatic sugar to specify trait bounds inside generic param list    
        // rule generic_params() -> (Vec<IdentKinded>, Vec<WhereClauseItem>)
        //     = generic_params:("<" _ t:(genericParam() ** (_ "," _)) _ ">" {t}) {
        //         let (idents, preds_options): (Vec<_>, Vec<_>) = generic_params.into_iter().unzip();
        //         let  preds = preds_options.into_iter().filter_map(|option| option).collect();
        //         (idents, preds)
        //     }
        
        //  rule genericParam() -> (IdentKinded, Option<WhereClauseItem>)
        //     = name:ident() bound:(_ ":" _ r:(k:kind(){Ok(k)} / t:identifier(){Err(t)}) {r})? {
        //         match bound {
        //             Some(kind_or_trait) =>
        //                 match kind_or_trait {
        //                     Ok(kind) => (IdentKinded::new(&name, kind), None),
        //                     Err(trait_bound) => {
        //                         let name_string = name.name.clone();
        //                         (IdentKinded::new(&name, Kind::Ty),
        //                             Some(WhereClauseItem{param: name_string, trait_bound}))
        //                     }
        //                 },
        //             None => (IdentKinded::new(&name, Kind::Ty), None)
        //         }
        //     }
           
        rule where_clause() -> Vec<Constraint>
            = "where" __ clauses:(where_clause_item() ** (_ "," _)) {
                clauses.into_iter().fold(Vec::new(), |mut clauses, clause| {
                    clauses.extend(clause);
                    clauses
                })
            }
        
        rule where_clause_item() -> Vec<Constraint>
            = param:dty() _ ":" _ trait_bounds:(trait_mono_ty() ** (_ "+" _)) {
                trait_bounds.into_iter().map(|trait_bound|
                    Constraint{
                        param: param.clone(),
                        trait_bound
                    }
                ).collect()
            }

        rule kind_parameter() -> IdentKinded
            = name:ident() kind:(_ ":" _ kind:kind() {kind})? {
                IdentKinded::new(&name, kind.unwrap_or(Kind::DataTy))
            }
  
        rule fun_parameter() -> ParamDecl
            = result:(
            mutbl:(m:mutability() __ {m})? ident:ident() _ ":" _ ty:ty() {
                let mutbl = mutbl.unwrap_or(Mutability::Const);
                ParamDecl { ident, ty:Some(ty), mutbl }
            } / s:self_param() { s }) {
                result
            }

        rule fun_decl_param() -> ParamTypeDecl
            = result:(
            mutbl:(m:mutability() __ {m})? (ident() _ ":" _)? ty:ty() {
                let mutbl = mutbl.unwrap_or(Mutability::Const);
                ParamTypeDecl { ty, mutbl }
            } / s:self_param() { ParamTypeDecl{ty: s.ty.unwrap(), mutbl: s.mutbl} }) {
                result
            }

        rule self_param() -> ParamDecl
            = result:(s:shorthand_self() { s } / s:typed_self() {s}) {
                result
            }  

        rule shorthand_self() -> ParamDecl
            = ref_params:("&" _ prov:(prv:provenance() __ { prv })? own:ownership() __
            mem:memory_kind() __ { (prov, own, mem) })? mutbl:(m:mutability() __ {m})? "self" {
                let self_dtykind = DataTyKind::Ident(Ident::new("Self"));
                let s_type = match ref_params {
                    Some(ref_params) => {
                        let (prov, own, mem) = ref_params;
                        DataTyKind::Ref(match prov {
                            Some(prv) => prv,
                            None => Provenance::Ident(Ident::new_impli(&crate::ast::utils::fresh_name("$r")))
                        }, own, mem, Box::new(DataTy::new(self_dtykind)))
                    }
                    None => self_dtykind    
                };
                let mutbl = mutbl.unwrap_or(Mutability::Const);
                ParamDecl{ ident: Ident::new("self"), ty: Some(Ty::new(TyKind::Data(DataTy::new(s_type)))), mutbl}
            }

        rule typed_self() -> ParamDecl
            = mutbl:(m:mutability() __ {m})? "self" _ ":" _ ty:ty() {
                let mutbl = mutbl.unwrap_or(Mutability::Const);
                ParamDecl { ident: Ident::new("self"), ty:Some(ty), mutbl }
            }

        rule lambda_parameter() -> ParamDecl
            = mutbl:(m:mutability() __ {m})? ident:ident() ty:(_ ":" _ tty:ty() { tty })? {
                let mutbl = mutbl.unwrap_or(Mutability::Const);
                ParamDecl { ident, ty, mutbl }
        }

        /// Parse a sequence of expressions (might also just be one)
        pub(crate) rule expression_seq() -> Expr
            = begin:position!() expressions:expression() **<2,> (_ ";" _) end:position!() {
                Expr::with_span(ExprKind::Seq(expressions), Span::new(begin, end))
            }
            / expr:expression() { expr }

        pub(crate) rule pattern() -> Pattern =
            mutbl:(m:mutability() __ {m})? ident:ident() {
                let mutbl = mutbl.unwrap_or(Mutability::Const);
                Pattern::Ident(mutbl, ident) }
            / tuple_pattern: "(" _ elems_pattern:pattern() ** (_ "," _) _ ")" {
                Pattern::Tuple(elems_pattern)
            }
            / "_" { Pattern::Wildcard }

        // These rules lead to stackoverflows when integrated in rule expression
        // FIXME: How to integrate this properly into the precedence parser?
        pub(crate) rule expr_helper() -> Expr =
            begin:position!() "let" __ pattern:pattern()
                typ:(_ ":" _ ty:ty() { ty })? _ "=" _ expr:expression() end:position!()
            {
                Expr::with_span(
                    ExprKind::Let(pattern, Box::new(typ), Box::new(expr)),
                    Span::new(begin, end)
                )
            }
            / let_uninit()
            / "for" __ ident:ident() __ "in" __ collection:expression()
                _ body:block()
            {
                Expr::new(ExprKind::For(ident, Box::new(collection), Box::new(body)))
            }
            / "while" __ cond:expression() __ body:block() {
                Expr::new(ExprKind::While(Box::new(cond), Box::new(body)))
            }
            // Parentheses to override precedence
            / "(" _ expression:expression() _ ")" { expression }


        /// Parse an expression
        pub(crate) rule expression() -> Expr = precedence!{
            x:(@) _ "&&" _ y:@ { utils::make_binary(BinOp::And, x, y) }
            x:(@) _ "||" _ y:@ { utils::make_binary(BinOp::Or, x, y) }
            --
            x:(@) _ "==" _ y:@ { utils::make_binary(BinOp::Eq, x, y) }
            x:(@) _ "!=" _ y:@ { utils::make_binary(BinOp::Neq, x, y) }
            x:(@) _ "<" _ y:@ { utils::make_binary(BinOp::Lt, x, y) }
            x:(@) _ "<=" _ y:@ { utils::make_binary(BinOp::Le, x, y) }
            x:(@) _ ">" _ y:@ { utils::make_binary(BinOp::Gt, x, y) }
            x:(@) _ ">=" _ y:@ { utils::make_binary(BinOp::Ge, x, y) }
            --
            x:(@) _ "+" _ y:@ { utils::make_binary(BinOp::Add, x, y) }
            x:(@) _ "-" _ y:@ { utils::make_binary(BinOp::Sub, x, y) }
            --
            x:(@) _ "*" _ y:@ { utils::make_binary(BinOp::Mul, x, y) }
            x:(@) _ "/" _ y:@ { utils::make_binary(BinOp::Div, x, y) }
            x:(@) _ "%" _ y:@ { utils::make_binary(BinOp::Mod, x, y) }
            --
            x: (@) _ ".." _ y: @ {
                Expr::new(ExprKind::Range(Box::new(x), Box::new(y)))
            }
            "-" _ x:(@) { utils::make_unary(UnOp::Neg, x) }
            "!" _ x:(@) { utils::make_unary(UnOp::Not, x) }
            --
            begin:position!() expr:@ end:position!() {
                let expr: Expr = Expr {
                    span: Some(Span::new(begin, end)),
                    ..expr
                };
                expr
            }
            // Not allowing white spaces between . and number can increase parser performance
            //  significantly.
            // To achieve this, move the first _ in front of ns.
            e:(@) ns:("." _ n:nat_literal() {n})+ {
                ns.into_iter().fold(e,
                    |prev, n| Expr::new(ExprKind::Proj(Box::new(prev), ProjEntry::TupleAccess(n)))
                )
            }
            e:(@) ns:("." _ n:identifier() {n})+ {
                ns.into_iter().fold(e,
                    |prev, n| Expr::new(ExprKind::Proj(Box::new(prev), ProjEntry::StructAccess(n)))
                )
            }
            begin:position!() "split" __ r1:(prv:prov_value() __ { prv })?
                    r2:(prv:prov_value()  __ { prv })? o:ownership() __
                    s:nat() __ view:place_expression() end:position!() {
                Expr::new(ExprKind::Split(r1, r2, o, s, Box::new(view)))
            }
            e:(p:place_expression() "." _ { Expr::new(ExprKind::PlaceExpr(p)) }
                / "(" _ e:expression() _ ")" _ "." _ { e })
                begin:position!() func:ident() place_end:position!() _
                kind_args:("::<" _ k:kind_argument() ** (_ "," _) _ ">" _ { k })?
                "(" _ args:expression() ** (_ "," _) _ ")" end:position!()
            {{
                let args = {
                            let mut result = Vec::with_capacity(args.len() + 1);
                    result.push(e);
                            result.extend(args.clone());
                            result
                };
                Expr::new(
                    ExprKind::App(
                        Path::InferFromFirstArg,
                        None,
                        Box::new(Expr::with_span(
                            ExprKind::PlaceExpr(PlaceExpr::new(PlaceExprKind::Ident(func))),
                            Span::new(begin, place_end)
                        )),
                        kind_args.unwrap_or(vec![]),
                        args
                    )
                )    
            }}
            begin:position!() func:ident() place_end:position!() _
                kind_args:("::<" _ k:kind_argument() ** (_ "," _) _ ">" _ { k })?
                "(" _ args:expression() ** (_ "," _) _ ")" end:position!()
            {{
                Expr::new(
                    ExprKind::App(
                        Path::Empty,
                        None,
                        Box::new(Expr::with_span(
                            ExprKind::PlaceExpr(PlaceExpr::new(PlaceExprKind::Ident(func))),
                            Span::new(begin, place_end)
                        )),
                        kind_args.unwrap_or(vec![]),
                        args
                    )
                )    
            }}
            path:(path:dty() "::" { path }) begin:position!() func:ident() place_end:position!() _
                kind_args:("::<" _ k:kind_argument() ** (_ "," _) _ ">" _ { k })?
                "(" _ args:expression() ** (_ "," _) _ ")" end:position!()
            {{
                let path = Path::DataTy(path);
                Expr::new(
                    ExprKind::App(
                        path,
                        None,
                        Box::new(Expr::with_span(
                            ExprKind::PlaceExpr(PlaceExpr::new(PlaceExprKind::Ident(func))),
                            Span::new(begin, place_end)
                        )),
                        kind_args.unwrap_or(vec![]),
                        args
                    )
                )    
            }}
            begin:position!() func:ident() end:position!() _
                kind_args:("::<" _ k:kind_argument() ** (_ "," _) _ ">" { k })
            {
                Expr::new(
                    ExprKind::DepApp(
                        Box::new(Expr::with_span(
                            ExprKind::PlaceExpr(PlaceExpr::new(PlaceExprKind::Ident(func))),
                            Span::new(begin, end)
                        )),
                        kind_args
                ))
            }
            begin:position!() struct_name:identifier() _
                kind_args:("<" _ k:kind_argument() ** (_ "," _) _ ">" _ { k })?
                "{" _ args:(i:ident() e:(_ ":" _ e:expression(){e})? {(i, e)}) ** (_ "," _)
                 _ "}"  end:position!() {{
                let args = args.iter().map(|(ident, expr_option)| {
                    match expr_option {
                        Some(e) => (ident.clone(), e.clone()),
                        None => (ident.clone(), Expr::new(ExprKind::PlaceExpr(
                            PlaceExpr::new(PlaceExprKind::Ident(ident.clone())))))
                    }}).collect();
                Expr::with_span(
                    ExprKind::StructInst(
                        struct_name,
                        kind_args.unwrap_or(vec![]),
                        args
                    ),
                    Span::new(begin, end)
                )
            }}
            l:literal() {
                Expr::with_type(
                    ExprKind::Lit(l),
                    Ty::new(TyKind::Data(utils::type_from_lit(&l)))
                )
            }
            p:place_expression() idx:(_ "[" _ n:nat() _ "]" {n})? expr:(_ "=" _ e:expression() {e})? {
                match expr {
                    None => match idx {
                        None => Expr::new(ExprKind::PlaceExpr(p)),
                        Some(idx) => Expr::new(ExprKind::Index(p,idx))
                    },
                    Some(expr) => match idx {
                        None => Expr::new(ExprKind::Assign(p, Box::new(expr))),
                        Some(idx) => Expr::new(ExprKind::IdxAssign(p, idx, Box::new(expr))),
                    }
                }
            }
            "&" _ prov:(v:prov_value() __ { v })? own:ownership() __ p:place_expression() idx:(_ "[" _ n:nat() _ "]" {n})? {
                match idx {
                    None => Expr::new(ExprKind::Ref(prov, own, p)),
                    Some(idx) => Expr::new(ExprKind::BorrowIndex(prov, own, p,idx))
                }
            }
            "[" _ expressions:expression() ** (_ "," _) _ "]" {
                Expr::new(ExprKind::Array(expressions))
            }
            // TODO unify single vs vec rules?
            "(" _ expression:expression() _ "," _ ")" {
                Expr::new(ExprKind::Tuple(vec![expression]))
            }
            "(" _ expressions:expression() **<2,> (_ "," _) _ ")" {
                Expr::new(ExprKind::Tuple(expressions))
            }
            "if" __ cond:expression() _ iftrue:block() _ iffalse:("else" _ iffalse:block() {
                iffalse })? {
                Expr::new( match iffalse {
                    Some(false_block) => ExprKind::IfElse(Box::new(cond), Box::new(iftrue), Box::new(false_block)),
                    None => ExprKind::If(Box::new(cond), Box::new(iftrue))
                })

            }
           "for_nat" __ ident:ident() __ "in" __ range:nat() _ body:block() {
                Expr::new(ExprKind::ForNat(ident, range, Box::new(body)))
            }
            "par_branch" __ par_collec:expression() _ "{" _
                branch:(branch_ident:ident() _ "=>" _
                    branch_body:expression() { (branch_ident, branch_body) }) **<1,> (_ "," _) _
            "}" {
                Expr::new(ExprKind::ParBranch(Box::new(par_collec),
                    branch.iter().map(|(i, _)| i.clone()).collect(),
                    branch.iter().map(|(_, b)| b.clone()).collect()))
            }
            decls:("decl" _ "{" _ decls:let_uninit() **<1,> (_ ";" _) _ "}" _ { decls })?
            "parfor" __ par_ident:maybe_ident() __ "in" __ parall_collec:expression() __
            "with" __ input_elems:ident() **<1,> (_ "," _) __
            "from" __ input:expression() **<1,> (_ "," _) _ body:block() {
                Expr::new(ExprKind::ParForWith(decls, par_ident, Box::new(parall_collec), input_elems, input, Box::new(body)))
            }
            "|" _ params:(lambda_parameter() ** (_ "," _)) _ "|" _
              "-" _ "[" _ exec:execution_resource() _ "]" _ "-" _ ">" _ ret_dty:dty() _
              body_expr:block() {
                Expr::new(ExprKind::Lambda(params, exec, Box::new(ret_dty), Box::new(body_expr)))
            }
            block:block() { block }
            expression: expr_helper() { expression }
        }

        rule maybe_ident() -> Option<Ident> =
            i:ident() { Some(i) }
            / "_" { None }

        rule block() -> Expr =
            prov_values:("<" _ prov_values:prov_value() ** (_ "," _)  _ ">" _ { prov_values })?
                "{" _ body:expression_seq() _ "}"
            {
                Expr::new(
                    ExprKind::Block(
                        if prov_values.is_some() { prov_values.unwrap() }
                        else { vec![] },
                        Box::new(body))
                )
            }

        rule let_uninit() -> Expr =
         begin:position!() "let" __ "mut" __ ident:ident() _ ":"
                _ ty:ty() end:position!()
            {
                Expr::with_span(
                    ExprKind::LetUninit(ident, Box::new(ty)),
                    Span::new(begin, end)
                )
            }

        // TODO make nat expressions aside from literals parsable.
        //  the current problem is, that a nat expression cannot be recognized as such, if it starts
        //  with an identifier, because identifiers are parsed generically. Just assuming the ident
        //  is nat would be wrong too (i.e., simply checking for nat first and then for generic ident).
        /// Parse a kind argument
        pub(crate) rule kind_argument() -> ArgKinded
            = !identifier() result:(
                n:nat() { ArgKinded::Nat(n) }
                / mem:memory_kind() { ArgKinded::Memory(mem) }
                / ty:ty() { match ty.ty { TyKind::Data(dty) => ArgKinded::DataTy(dty), _ => ArgKinded::Ty(ty) } }
                / prov:provenance() { ArgKinded::Provenance(prov) }
            ) { result }
            / ident:ident() { ArgKinded::Ident(ident)}

        /// Place expression
        pub(crate) rule place_expression() -> PlaceExpr
            = precedence!{
                "*" _ deref:@ { PlaceExpr::new(PlaceExprKind::Deref(Box::new(deref))) }
                --
                proj:@ _ "." _ n:nat_literal() { PlaceExpr::new(PlaceExprKind::Proj(
                    Box::new(proj), ProjEntry::TupleAccess(n)))}
                // The !(_ "(") makes sure this is not a method call on a struct
                struct_access:@ _ "." _ i:identifier() !(_ "(") {
                    PlaceExpr::new(PlaceExprKind::Proj(
                        Box::new(struct_access), ProjEntry::StructAccess(i))) }
                --
                begin:position!() pl_expr:@ end:position!() {
                    PlaceExpr {
                        span: Some(Span::new(begin, end)),
                        ..pl_expr
                    }
                }
                ident:ident() { PlaceExpr::new(PlaceExprKind::Ident(ident)) }
                "self" { PlaceExpr::new(PlaceExprKind::Ident(Ident::new("self"))) }
                "(" _ pl_expr:place_expression() _ ")" { pl_expr }
            }
            // = begin:position!() begin_derefs:(begin_deref:position!() "*" _ { begin_deref })*
            //     ident:ident()
            //     ns_with_ends:(_ ns_with_ends:(
            //         "." _ n:nat_literal() end_proj:position!() { (n, end_proj) })+ {ns_with_ends}
            //     )? end:position!()
            // {
            //     let ns_with_ends = ns_with_ends.unwrap_or(vec![]);
            //     let ident_span = ident.span.unwrap();
            //     let root = PlaceExpr::with_span(PlaceExprKind::Ident(ident), ident_span);
            //     // . operator binds stronger
            //     let proj = ns_with_ends.into_iter().fold(root,
            //         |prev, (n, end_proj) | {
            //             let begin = prev.span.unwrap().begin;
            //             PlaceExpr::with_span(
            //                 PlaceExprKind::Proj(Box::new(prev), n),
            //                 Span::new(begin, end_proj)
            //             )
            //     });
            //     // * operator binds weaker
            //     begin_derefs.iter().fold(proj,
            //         |prev, begin_deref| {
            //         let end = prev.span.unwrap().end;
            //         PlaceExpr::with_span(
            //             PlaceExprKind::Deref(Box::new(prev)),
            //             Span::new(*begin_deref, end)
            //         )
            //     })
            // }
            // / begin:position!() "(" _ pl_expr:place_expression() ")" end:position!()  {
            //     let mut ple = pl_expr;
            //     ple.span = Some(Span::new(begin, end));
            //     ple
            // }

        /// Parse nat token
        pub(crate) rule nat() -> Nat = precedence! {
            func:ident() _
                "(" _ args:nat() ** (_ "," _) _ ")" end:position!()
            {
                Nat::App(func, args)
            }
            x:(@) _ "+" _ y:@ { utils::make_binary_nat(BinOpNat::Add, x, y) }
            x:(@) _ "-" _ y:@ { utils::make_binary_nat(BinOpNat::Sub, x, y) }
            --
            x:(@) _ "*" _ y:@ { utils::make_binary_nat(BinOpNat::Mul, x, y) }
            x:(@) _ "/" _ y:@ { utils::make_binary_nat(BinOpNat::Div, x, y) }
            x:(@) _ "%" _ y:@ { utils::make_binary_nat(BinOpNat::Mod, x, y) }
            --
            literal:nat_literal() { Nat::Lit(literal) }
            name:ident() { Nat::Ident(name) }
            "(" _ n:nat() _ ")" { n }
        }
            // TODO: binary operations are currently disabled

        rule nat_literal() -> usize
            = s:$("0" / (['1'..='9']['0'..='9']*)) { ?
                // TODO: Getting the cause of the parse error is unstable for now. Fix this once
                //  int_error_matching becomes stable
                match s.parse::<usize>() {
                    Ok(val) => Ok(val),
                    Err(_) => { Err("Cannot parse natural number") }
                }
            }

        pub(crate) rule ty() -> Ty
            = begin:position!() dty:dty() end:position!() {
                Ty::with_span(TyKind::Data(dty), Span::new(begin, end))
            }

        /// Parse a type token
        pub(crate) rule dty() -> DataTy
            = first:dty_term() _ mems:("@" _ mem:memory_kind() _ {mem})* {
                mems.into_iter().fold(DataTy::new(first), |prev,mem| DataTy::new(DataTyKind::At(Box::new(prev), mem)))
            } 

        /// Helper for "type @ memory" left-recursion
        rule dty_term() -> DataTyKind
            = "f32" { DataTyKind::Scalar(ScalarTy::F32) }
            / "f64" { DataTyKind::Scalar(ScalarTy::F64) }
            / "i32" { DataTyKind::Scalar(ScalarTy::I32) }
            / "u32" { DataTyKind::Scalar(ScalarTy::U32) }
            / "bool" { DataTyKind::Scalar(ScalarTy::Bool) }
            / "()" { DataTyKind::Scalar(ScalarTy::Unit) }
            / "Gpu" { DataTyKind::Scalar(ScalarTy::Gpu) }
            / "Atomic<i32>" { DataTyKind::Atomic(ScalarTy::I32) }
            / "Atomic<bool>" {DataTyKind::Atomic(ScalarTy::Bool)}
            / th_hy:th_hy() { DataTyKind::ThreadHierchy(Box::new(th_hy)) }
            / name:identifier() _ "<" _ params:(k:kind_argument() ** (_ "," _) {k}) _ ">"
                { DataTyKind::Struct( StructDataType{
                    name, attributes: vec![], generic_args: params, })}
            // this could be also a structType. That is decided later
            / name:ident() { DataTyKind::Ident(name) }
            / "Self" { DataTyKind::Ident(Ident::new("Self")) }
            / "(" _ types:dty() ** ( _ "," _ ) _ ")" { DataTyKind::Tuple(types) }
            / "[" _ t:dty() _ ";" _ n:nat() _ "]" { DataTyKind::Array(Box::new(t), n) }
            / "[" _ "[" _ dty:dty() _ ";" _ n:nat() _ "]" _ "]" {
                DataTyKind::ArrayShape(Box::new(dty), n)
            }
            / "&" _ prov:(prv:provenance() __ { prv })? own:ownership() __ mem:memory_kind() __ dty:dty() {
                DataTyKind::Ref(match prov {
                    Some(prv) => prv,
                    None => Provenance::Ident(Ident::new_impli(&crate::ast::utils::fresh_name("$r")))
                }, own, mem, Box::new(dty))
            }
            / "_" { DataTyKind::Ident(Ident::new_impli(&crate::ast::utils::fresh_name("$d"))) }

        pub(crate) rule th_hy() -> ThreadHierchyTy =
        "BlockGrp" _ "<" _ n1:nat() _ ns:("," _ n2:nat() _ "," _ n3:nat() _ { (n2, n3) })? "," _
            "ThreadGrp" _ "<" _ m1:nat() _ ms:("," _ m2:nat() _ "," _ m3:nat() _ { (m2, m3) })?
                ">" _ ">" {
            let (n2, n3) = match ns {
                Some(n2_n3) => n2_n3,
                None => (Nat::Lit(1), Nat::Lit(1))
            };
            let (m2, m3) = match ms {
                Some(m2_m3) => m2_m3,
                None => (Nat::Lit(1), Nat::Lit(1))
            };
            ThreadHierchyTy::BlockGrp(n1, n2, n3, m1, m2, m3)
        }
        / "ThreadGrp" _ "<" _ n1:nat() _ ns:("," _ n2:nat() _ "," _ n3:nat() _ { (n2, n3) })? ">" {
            let (n2, n3) = match ns {
                Some(n2_n3) => n2_n3,
                None => (Nat::Lit(1), Nat::Lit(1))
            };
            ThreadHierchyTy::ThreadGrp(n1, n2, n3)
        }
        / "WarpGrp" _ "<" n:nat() _ ">" { ThreadHierchyTy::WarpGrp(n) }
        / "Warp" { ThreadHierchyTy::Warp }

        pub(crate) rule ownership() -> Ownership
        = "shrd" { Ownership::Shrd }
        / "uniq" { Ownership::Uniq }

        pub(crate) rule mutability() -> Mutability
        = "const" { Mutability::Const }
        / "mut" { Mutability::Mut }

        pub(crate) rule memory_kind() -> Memory
            = "cpu.mem" { Memory::CpuMem }
            / "gpu.global" { Memory::GpuGlobal }
            / "gpu.shared" { Memory::GpuShared }
            / name:ident() { Memory::Ident(name) }

        pub(crate) rule execution_resource() -> Exec
            = "cpu.thread" { Exec::CpuThread }
            / "gpu.grid" { Exec::GpuGrid }
            / "gpu.block" { Exec::GpuBlock }
            / "gpu.warp" { Exec::GpuWarp }
            / "gpu.thread" { Exec::GpuThread }

        pub(crate) rule kind() -> Kind
            = "nat" { Kind::Nat }
            / "mem" { Kind::Memory }
            / "ty" { Kind::Ty }
            / "dty" { Kind::DataTy }
            / "prv" { Kind::Provenance }

        rule ident() -> Ident
            = begin:position!() ident:$(identifier()) end:position!() {
                Ident::with_span(ident.into(), Span::new(begin, end))
            }

        rule provenance() -> Provenance
            = prov:prov_value() {
                Provenance::Value(prov)
            }
            / ident:ident() {
                Provenance::Ident(ident)
            }

        /// Identifier, but also allows leading ' for provenance names
        rule prov_value() -> String
        = s:$("'" identifier()) { s.into() }

        /// Parse an identifier
        rule identifier() -> String
        = s:$(!keyword() (['a'..='z'|'A'..='Z'] ['a'..='z'|'A'..='Z'|'0'..='9'|'_']*
            / ['_']+ ['a'..='z'|'A'..='Z'|'0'..='9'] ['a'..='z'|'A'..='Z'|'0'..='9'|'_']*))
        {
            s.into()
        }

        rule keyword() -> ()
            = (("crate" / "super" / "self" / "Self" / "const" / "mut" / "uniq" / "shrd" / "in" / "from" / "with" / "decl"
                / "f32" / "f64" / "i32" / "u32" / "bool" / "Atomic<i32>" / "Atomic<bool>" / "Gpu" / "nat" / "mem" / "ty" / "prv" / "own"
                / "let"("prov")? / "if" / "else" / "par_branch" / "parfor" / "for_nat" / "for" / "while" / "across" / "fn" / "struct"
                / "trait" / "where" / "impl" / "Grid" / "Block" / "Warp" / "Thread" / "with")
                !['a'..='z'|'A'..='Z'|'0'..='9'|'_']
            )
            / "cpu.mem" / "gpu.global" / "gpu.shared"
            / "cpu.thread" / "gpu.group" / "gpu.thread"

        // Literal may be one of Unit, bool, i32, u32, f32
        pub(crate) rule literal() -> Lit
            = "()" {
                Lit::Unit
            }
            / l:$("true" / "false") { ?
                match l.parse::<bool>() {
                    Ok(b) => Ok(Lit::Bool(b)),
                    Err(_) => Err("Error while parsing boolean literal")
                }
            }
            / l:$( ("-"? ((['1'..='9']['0'..='9']*) / "0") "." ['0'..='9']*)  (['e'|'E'] "-"?  ['0'..='9']*)? "f32"? ) { ?
                if (l.ends_with("f32")) {
                    match l[0..l.len()-3].parse::<f32>() {
                        Ok(val) => Ok(Lit::F32(val)),
                        Err(_) => Err("Error while parsing f32 literal")
                    }
                } else {
                    match l.parse::<f64>() {
                        Ok(val) => Ok(Lit::F64(val)),
                        Err(_) => Err("Error while parsing f64 literal")
                    }
                }
            }
            / l:$((("-"? ['1'..='9']['0'..='9']*) / "0") ("i32" / "u32" / "f32")?  ) { ?
                let literal = if (l.ends_with("i32") || l.ends_with("u32") || l.ends_with("f32")) {&l[0..l.len()-3]} else {l};
                if (l.ends_with("f32")) {
                    match literal.parse::<f32>() {
                        Ok(val) => Ok(Lit::F32(val)),
                        Err(_) => Err("Error while parsing f32 literal")
                    }
                } else if (l.ends_with("u32")) {
                    match literal.parse::<u32>() {
                        Ok(val) => Ok(Lit::U32(val)),
                        Err(_) => Err("Error while paring u32 literal")
                    }
                } else {
                    match literal.parse::<i32>() {
                        Ok(val) => Ok(Lit::I32(val)),
                        Err(_) => Err("Error while parsing i32 literal")
                    }
                }
            }

        /// Potential whitespace
        rule _() -> ()
            = quiet!{(
                [' '|'\n'|'\t'|'\r'] _) // 0 or more whitespaces
                / ("//" (!['\n'][_])* ['\n'] _) // Comment to EOL
                / ("/*" (!"*/"[_])* "*/" _) // Block comment
                / ""}

        /// At least one whitespace
        rule __() -> ()
            = quiet!{[' '|'\n'|'\t'|'\r'] _}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nat_literal() {
        assert_eq!(descend::nat("0"), Ok(Nat::Lit(0)), "cannot parse 0");
        assert_eq!(descend::nat("42"), Ok(Nat::Lit(42)), "cannot parse 42");
        assert!(
            descend::nat("100000000000000000000").is_err(),
            "overflow not handled"
        );
        assert!(descend::nat("-1").is_err(), "negative numbers not handled");
        assert!(descend::nat("3abc").is_err(), "garbage not handled");
        assert!(descend::nat("").is_err(), "matches empty");
    }

    #[test]
    fn nat_identifier() {
        assert_eq!(
            descend::nat("N"),
            Ok(Nat::Ident(Ident::new("N"))),
            "cannot parse N"
        );
        assert_eq!(
            descend::nat("my_long_ident"),
            Ok(Nat::Ident(Ident::new("my_long_ident"))),
            "cannot parse long identifer"
        );
    }

    #[test]
    fn nat_binary_operation() {
        // Test trivial cases
        assert_eq!(
            descend::nat("N+1"),
            Ok(utils::make_binary_nat(
                BinOpNat::Add,
                Nat::Ident(Ident::new("N")),
                Nat::Lit(1)
            )),
            "cannot parse N+1"
        );
        assert_eq!(
            descend::nat("N-1"),
            Ok(utils::make_binary_nat(
                BinOpNat::Sub,
                Nat::Ident(Ident::new("N")),
                Nat::Lit(1)
            )),
            "cannot parse N-1"
        );
        assert_eq!(
            descend::nat("N*1"),
            Ok(utils::make_binary_nat(
                BinOpNat::Mul,
                Nat::Ident(Ident::new("N")),
                Nat::Lit(1)
            )),
            "cannot parse N*1"
        );
        assert_eq!(
            descend::nat("N/1"),
            Ok(utils::make_binary_nat(
                BinOpNat::Div,
                Nat::Ident(Ident::new("N")),
                Nat::Lit(1)
            )),
            "cannot parse N/1"
        );
        assert_eq!(
            descend::nat("N%1"),
            Ok(utils::make_binary_nat(
                BinOpNat::Mod,
                Nat::Ident(Ident::new("N")),
                Nat::Lit(1)
            )),
            "cannot parse N%1"
        );
        // Test composite case with precedence
        assert_eq!(
            descend::nat("N+1*2"),
            Ok(utils::make_binary_nat(
                BinOpNat::Add,
                Nat::Ident(Ident::new("N")),
                utils::make_binary_nat(BinOpNat::Mul, Nat::Lit(1), Nat::Lit(2))
            )),
            "cannot parse N+1*2"
        );
        assert_eq!(
            descend::nat("(N+1)*2"),
            Ok(utils::make_binary_nat(
                BinOpNat::Mul,
                utils::make_binary_nat(BinOpNat::Add, Nat::Ident(Ident::new("N")), Nat::Lit(1)),
                Nat::Lit(2)
            )),
            "cannot parse (N+1)*2"
        );
    }

    #[test]
    fn ty_scalar() {
        assert_eq!(
            descend::ty("f32"),
            Ok(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                ScalarTy::F32
            ))))),
            "does not recognize f32 type"
        );
        assert_eq!(
            descend::ty("i32"),
            Ok(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                ScalarTy::I32
            ))))),
            "does not recognize i32 type"
        );
        assert_eq!(
            descend::ty("u32"),
            Ok(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                ScalarTy::U32
            ))))),
            "does not recognize u32 type"
        );
        assert_eq!(
            descend::ty("()"),
            Ok(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                ScalarTy::Unit
            ))))),
            "does not recognize unit type"
        );
        assert_eq!(
            descend::ty("bool"),
            Ok(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                ScalarTy::Bool
            ))))),
            "does not recognize Boolean type"
        );
    }

    #[test]
    fn ty_gpu() {
        assert_eq!(
            descend::ty("Gpu"),
            Ok(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                ScalarTy::Gpu
            ))))),
            "does not recognize GPU type"
        );
    }

    #[test]
    fn dty_tuple() {
        let ty_f32 = DataTy::new(DataTyKind::Scalar(ScalarTy::F32));
        let ty_i32 = DataTy::new(DataTyKind::Scalar(ScalarTy::I32));
        let ty_u32 = DataTy::new(DataTyKind::Scalar(ScalarTy::U32));
        let ty_unit = DataTy::new(DataTyKind::Scalar(ScalarTy::Unit));
        assert_eq!(
            descend::dty("(f32)"),
            Ok(DataTy::new(DataTyKind::Tuple(vec![ty_f32]))),
            "does not recognize (f32) tuple type"
        );
        assert_eq!(
            descend::dty("(i32,i32)"),
            Ok(DataTy::new(DataTyKind::Tuple(vec![ty_i32.clone(), ty_i32]))),
            "does not recognize (i32) tuple type"
        );
        assert_eq!(
            descend::dty("(u32,u32)"),
            Ok(DataTy::new(DataTyKind::Tuple(vec![ty_u32.clone(), ty_u32]))),
            "does not recognize (u32, u32) tuple type"
        );
        assert_eq!(
            descend::dty("((),(),())"),
            Ok(DataTy::new(DataTyKind::Tuple(vec![
                ty_unit.clone(),
                ty_unit.clone(),
                ty_unit.clone()
            ]))),
            "does not recognize (unit,unit,unit) tuple type"
        );
    }

    #[test]
    fn ty_array_and_array_view() {
        assert_eq!(
            descend::ty("[f32;42]"),
            Ok(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Array(
                Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::F32))),
                Nat::Lit(42)
            ))))),
            "does not recognize [f32;42] type"
        );
        assert_eq!(
            descend::ty("[u32;43]"),
            Ok(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Array(
                Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::U32))),
                Nat::Lit(43)
            ))),)),
            "does not recognize [u32;43] type"
        );
        // TODO: Implement identifer parsing in nat
        // assert_eq!(descend::ty("[();N]"), Ok(Ty::Array(Box::new(
        //     Ty::Scalar(ScalarTy::Unit)),
        //     Nat::Ident(Nat::new_ident("N")))
        // ), "does not recognize [();N] type");
        assert_eq!(
            descend::ty("[[i32;24]]"),
            Ok(Ty::new(TyKind::Data(DataTy::new(DataTyKind::ArrayShape(
                Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))),
                Nat::Lit(24)
            ))),)),
            "does not recognize [[f32;24]] type"
        );
    }

    #[test]
    fn ty_identifier() {
        assert_eq!(
            descend::ty("T"),
            Ok(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ident(
                Ident::new("T")
            ))))),
            "does not recognize T type"
        );
    }

    #[test]
    fn ty_reference() {
        assert_eq!(
            descend::ty("&'a uniq cpu.mem i32"),
            Ok(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
                Provenance::Value("'a".into()),
                Ownership::Uniq,
                Memory::CpuMem,
                Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::I32)))
            ))),)),
            "does not recognize type of unique i32 reference in cpu heap with provenance 'a"
        );
        assert_eq!(descend::ty("&b shrd gpu.global [f32;N]"), Ok(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
                        Provenance::Ident(Ident::new("b")),
                        Ownership::Shrd,
                        Memory::GpuGlobal,
                        Box::new(DataTy::new(DataTyKind::Array(
                            Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::F32))),
                            Nat::Ident(Ident::new("N"))
                        )))
                    ))),
        )), "does not recognize type of shared [f32] reference in gpu global memory with provenance b");
    }

    #[test]
    fn ty_memory_kind() {
        assert_eq!(
            descend::ty("i32 @ cpu.mem"),
            Ok(Ty::new(TyKind::Data(DataTy::new(DataTyKind::At(
                Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))),
                Memory::CpuMem
            ))),)),
            "does not recognize f32 @ cpu.stack type"
        );
        assert_eq!(
            descend::ty("[f32;42] @ gpu.global"),
            Ok(Ty::new(TyKind::Data(DataTy::new(DataTyKind::At(
                Box::new(DataTy::new(DataTyKind::Array(
                    Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::F32))),
                    Nat::Lit(42)
                ))),
                Memory::GpuGlobal
            ))),)),
            "does not recognize [f32;42] @ gpu.global type"
        );
    }

    #[test]
    fn ownership() {
        assert_eq!(
            descend::ownership("shrd"),
            Ok(Ownership::Shrd),
            "does not recognize shrd ownership qualifier"
        );
        assert_eq!(
            descend::ownership("uniq"),
            Ok(Ownership::Uniq),
            "does not recognize uniq ownership qualifier"
        );
    }

    #[test]
    fn mutability() {
        assert_eq!(
            descend::mutability("const"),
            Ok(Mutability::Const),
            "does not recognize const mutability qualifier"
        );
        assert_eq!(
            descend::mutability("mut"),
            Ok(Mutability::Mut),
            "does not recognize mut mutability qualifier"
        );
    }

    #[test]
    fn memory_kind() {
        assert_eq!(
            descend::memory_kind("cpu.mem"),
            Ok(Memory::CpuMem),
            "does not recognize cpu.stack memory kind"
        );
        assert_eq!(
            descend::memory_kind("cpu.mem"),
            Ok(Memory::CpuMem),
            "does not recognize cpu.heap memory kind"
        );
        assert_eq!(
            descend::memory_kind("gpu.global"),
            Ok(Memory::GpuGlobal),
            "does not recognize gpu.global memory kind"
        );
        assert_eq!(
            descend::memory_kind("gpu.shared"),
            Ok(Memory::GpuShared),
            "does not recognize gpu.shared memory kind"
        );
        assert_eq!(
            descend::memory_kind("M"),
            Ok(Memory::Ident(Ident::new("M"))),
            "does not recognize M memory kind"
        );
    }

    #[test]
    fn execution_resource() {
        assert_eq!(
            descend::execution_resource("cpu.thread"),
            Ok(Exec::CpuThread),
            "does not recognize cpu.stack memory kind"
        );
        assert_eq!(
            descend::execution_resource("gpu.block"),
            Ok(Exec::GpuBlock),
            "does not recognize gpu.block memory kind"
        );
        assert_eq!(
            descend::execution_resource("gpu.thread"),
            Ok(Exec::GpuThread),
            "does not recognize gpu.global memory kind"
        );
    }

    #[test]
    fn literal() {
        assert_eq!(descend::literal("()"), Ok(Lit::Unit));
        assert_eq!(
            descend::literal("true"),
            Ok(Lit::Bool(true)),
            "does not parse boolean correctly"
        );
        assert_eq!(
            descend::literal("False").is_err(),
            true,
            "wrongfully parses misspelled boolean"
        );
        assert_eq!(
            descend::literal("12345"),
            Ok(Lit::I32(12345)),
            "does not parse i32 correctly"
        );
        assert_eq!(
            descend::literal("789i32"),
            Ok(Lit::I32(789)),
            "does not parse i32 correctly"
        );
        assert_eq!(
            descend::literal("-1i32"),
            Ok(Lit::I32(-1)),
            "does not correctly parse 1e05i32 to i32"
        );
        assert_eq!(
            descend::literal("1f32"),
            Ok(Lit::F32(1.)),
            "does not correctly parse 1f32 to f32"
        );
        // TODO: Do proper float comparison (test error against threshold)
        assert_eq!(
            descend::literal("1.0f32"),
            Ok(Lit::F32(1.0)),
            "does not parse f32 correctly"
        );
        assert_eq!(
            descend::literal("2.0f32"),
            Ok(Lit::F32(2.0)),
            "does not parse f32 correctly"
        );
        assert_eq!(
            descend::literal("777.7e0f32"),
            Ok(Lit::F32(777.7)),
            "does not parse f32 correctly"
        );
        assert_eq!(
            descend::literal("777.7e01f32"),
            Ok(Lit::F32(7777.0)),
            "does not parse f32 correctly"
        );
        assert_eq!(
            descend::literal("1.0e2f32"),
            Ok(Lit::F32(100.0)),
            "does not parse f32 in scientific notation correctly"
        );
        assert_eq!(
            descend::literal("1.0e-2f32"),
            Ok(Lit::F32(0.01)),
            "does not parse f32 in scientific notation correctly"
        );
        assert_eq!(
            descend::literal("3.7f32"),
            Ok(Lit::F32(3.7)),
            "does not parse f32 correctly"
        );
        assert_eq!(
            descend::literal("3.75e3f32"),
            Ok(Lit::F32(3750.0)),
            "does not parse scientific notation f32 correctly"
        );
        assert_eq!(
            descend::literal("-1234.5e-0005f32"),
            Ok(Lit::F32(-0.012345)),
            "does not parse negative scientific notation f32 correctly"
        );
        assert_eq!(
            descend::literal("3.14159265358979323846264338327950288f32"), // std::f64::consts::PI
            Ok(Lit::F32(3.1415927)),
            "not parsing f32 float as expected"
        );
        assert_eq!(
            descend::literal("12345ad").is_err(),
            true,
            "incorrectly parsing invalid literal"
        );
        assert_eq!(
            descend::literal("e54").is_err(),
            true,
            "incorrectly parsing e-notation only to literal"
        );
        assert_eq!(
            descend::literal("-i32").is_err(),
            true,
            "incorrectly parsing 'negative data type' to literal"
        );
    }

    #[test]
    fn kind() {
        assert_eq!(
            descend::kind("nat"),
            Ok(Kind::Nat),
            "does not recognize nat kind"
        );
        assert_eq!(
            descend::kind("mem"),
            Ok(Kind::Memory),
            "does not recognize mem kind"
        );
        assert_eq!(
            descend::kind("ty"),
            Ok(Kind::Ty),
            "does not recognize ty kind"
        );
        assert_eq!(
            descend::kind("prv"),
            Ok(Kind::Provenance),
            "does not recognize prv kind"
        );
    }

    #[test]
    fn place_expression() {
        assert_eq!(
            descend::place_expression("*x"),
            Ok(PlaceExpr::new(PlaceExprKind::Deref(Box::new(
                PlaceExpr::new(PlaceExprKind::Ident(Ident::new("x")))
            )))),
            "does not recognize place expression *x"
        );
        assert_eq!(
            descend::place_expression("x.0"),
            Ok(PlaceExpr::new(PlaceExprKind::Proj(
                Box::new(PlaceExpr::new(PlaceExprKind::Ident(Ident::new("x")))),
                ProjEntry::TupleAccess(0)
            ))),
            "does not recognize place expression projection `x.0`"
        );
        assert_eq!(
            descend::place_expression("*x.0"),
            Ok(PlaceExpr::new(PlaceExprKind::Deref(Box::new(
                PlaceExpr::new(PlaceExprKind::Proj(
                    Box::new(PlaceExpr::new(PlaceExprKind::Ident(Ident::new("x")))),
                    ProjEntry::TupleAccess(0)
                ))
            )))),
            "does not recognize place expression `*x.0`"
        );
    }

    #[test]
    fn correctly_recognize_place_expression_vs_proj_expression() {
        let zero_literal = 0;
        let one_literal = 1;
        // Place expressions
        assert_eq!(
            descend::expression("x.0"),
            Ok(Expr::new(ExprKind::PlaceExpr(PlaceExpr::new(
                PlaceExprKind::Proj(
                    Box::new(PlaceExpr::new(PlaceExprKind::Ident(Ident::new("x")))),
                    ProjEntry::TupleAccess(0)
                )
            )))),
            "does not recognize place expression projection `x.0`"
        );
        assert_eq!(
            descend::expression("*x.0"),
            Ok(Expr::new(ExprKind::PlaceExpr(PlaceExpr::new(
                PlaceExprKind::Deref(Box::new(PlaceExpr::new(PlaceExprKind::Proj(
                    Box::new(PlaceExpr::new(PlaceExprKind::Ident(Ident::new("x")))),
                    ProjEntry::TupleAccess(0)
                ))))
            )))),
            "does not recognize place expression `*x.0`"
        );

        // No place expressions
        assert_eq!(
            descend::expression("f::<x>().0"),
            Ok(Expr::new(ExprKind::Proj(
                Box::new(Expr::new(ExprKind::App(
                    Path::Empty,
                    None,
                    Box::new(Expr::new(ExprKind::PlaceExpr(PlaceExpr::new(
                        PlaceExprKind::Ident(Ident::new("f"))
                    )))),
                    vec![ArgKinded::Ident(Ident::new("x"))],
                    vec![]
                ))),
                ProjEntry::TupleAccess(zero_literal)
            ))),
            "does not recognize projection on function application"
        );
        assert_eq!(
            descend::expression("(x, y, z).1"),
            Ok(Expr::new(ExprKind::Proj(
                Box::new(Expr::new(ExprKind::Tuple(vec![
                    Expr::new(ExprKind::PlaceExpr(PlaceExpr::new(PlaceExprKind::Ident(
                        Ident::new("x")
                    )))),
                    Expr::new(ExprKind::PlaceExpr(PlaceExpr::new(PlaceExprKind::Ident(
                        Ident::new("y")
                    )))),
                    Expr::new(ExprKind::PlaceExpr(PlaceExpr::new(PlaceExprKind::Ident(
                        Ident::new("z")
                    ))))
                ]))),
                ProjEntry::TupleAccess(one_literal)
            ))),
            "does not recognize projection on tuple view expression"
        );
    }

    #[test]
    fn expression_literal() {
        assert_eq!(
            descend::expression("7"),
            Ok(Expr::with_type(
                ExprKind::Lit(Lit::I32(7)),
                Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))))
            ))
        );
        dbg!(descend::expression("7").unwrap());
    }

    #[test]
    fn expression_addition() {
        assert_eq!(
            descend::expression("7+8"),
            Ok(Expr::new(ExprKind::BinOp(
                BinOp::Add,
                Box::new(Expr::with_type(
                    ExprKind::Lit(Lit::I32(7)),
                    Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))))
                )),
                Box::new(Expr::with_type(
                    ExprKind::Lit(Lit::I32(8)),
                    Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))))
                ))
            ),))
        );
    }

    #[test]
    fn expression_parenthesis() {
        assert_eq!(
            descend::expression_seq("(5+6) * 7"),
            Ok(Expr::new(ExprKind::BinOp(
                BinOp::Mul,
                Box::new(Expr::new(ExprKind::BinOp(
                    BinOp::Add,
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::I32(5)),
                        Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))))
                    )),
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::I32(6)),
                        Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))))
                    ))
                ),)),
                Box::new(Expr::with_type(
                    ExprKind::Lit(Lit::I32(7)),
                    Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))))
                ))
            ),))
        );
    }

    #[test]
    fn expression_place_expr() {
        assert_eq!(
            descend::expression_seq("someIdentifier"),
            Ok(Expr::new(ExprKind::PlaceExpr(PlaceExpr::new(
                PlaceExprKind::Ident(Ident::new("someIdentifier"))
            ))))
        );
        assert_eq!(
            descend::expression_seq("*x"),
            Ok(Expr::new(ExprKind::PlaceExpr(PlaceExpr::new(
                PlaceExprKind::Deref(Box::new(PlaceExpr::new(PlaceExprKind::Ident(Ident::new(
                    "x"
                )))))
            ))))
        );
        assert_eq!(
            descend::expression_seq("**x.7"),
            Ok(Expr::new(ExprKind::PlaceExpr(PlaceExpr::new(
                PlaceExprKind::Deref(Box::new(PlaceExpr::new(PlaceExprKind::Deref(Box::new(
                    PlaceExpr::new(PlaceExprKind::Proj(
                        Box::new(PlaceExpr::new(PlaceExprKind::Ident(Ident::new("x")))),
                        ProjEntry::TupleAccess(7)
                    ))
                )))))
            ))))
        );
        assert_eq!(
            descend::expression_seq("x.2.3"),
            Ok(Expr::new(ExprKind::PlaceExpr(PlaceExpr::new(
                PlaceExprKind::Proj(
                    Box::new(PlaceExpr::new(PlaceExprKind::Proj(
                        Box::new(PlaceExpr::new(PlaceExprKind::Ident(Ident::new("x")))),
                        ProjEntry::TupleAccess(2)
                    ))),
                    ProjEntry::TupleAccess(3)
                )
            ))))
        );
    }

    #[test]
    fn expression_indexing() {
        assert_eq!(
            descend::expression_seq("place_expression[12]"),
            Ok(Expr::new(ExprKind::Index(
                PlaceExpr::new(PlaceExprKind::Ident(Ident::new("place_expression"))),
                Nat::Lit(12)
            )))
        );
    }

    #[test]
    fn expression_assignment() {
        assert_eq!(
            descend::expression_seq("var_token = 7.3e2f32"),
            Ok(Expr::new(ExprKind::Assign(
                PlaceExpr::new(PlaceExprKind::Ident(Ident::new("var_token"))),
                Box::new(Expr::with_type(
                    ExprKind::Lit(Lit::F32(730.0)),
                    Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::F32))))
                ))
            )))
        );
        assert_eq!(
            descend::expression_seq("*var_token = 3 + 4"),
            Ok(Expr::new(ExprKind::Assign(
                PlaceExpr::new(PlaceExprKind::Deref(Box::new(PlaceExpr::new(
                    PlaceExprKind::Ident(Ident::new("var_token"))
                )))),
                Box::new(Expr::new(ExprKind::BinOp(
                    BinOp::Add,
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::I32(3)),
                        Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))))
                    )),
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::I32(4)),
                        Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))))
                    ))
                )))
            )))
        );
    }

    #[test]
    fn expression_references() {
        assert_eq!(
            descend::expression_seq("&'prov uniq variable"),
            Ok(Expr::new(ExprKind::Ref(
                Some(String::from("'prov")),
                Ownership::Uniq,
                PlaceExpr::new(PlaceExprKind::Ident(Ident::new("variable")))
            )))
        );
        assert_eq!(
            descend::expression_seq("&'prov uniq var[7]"),
            Ok(Expr::new(ExprKind::BorrowIndex(
                Some(String::from("'prov")),
                Ownership::Uniq,
                PlaceExpr::new(PlaceExprKind::Ident(Ident::new("var"))),
                Nat::Lit(7)
            ),))
        );
        assert_eq!(
            descend::expression_seq("&'prov uniq var[token]"),
            Ok(Expr::new(ExprKind::BorrowIndex(
                Some(String::from("'prov")),
                Ownership::Uniq,
                PlaceExpr::new(PlaceExprKind::Ident(Ident::new("var"))),
                Nat::Ident(Ident::new("token"))
            ),))
        );
        let result = descend::expression_seq("&'a uniq var[7][3]");
        assert!(result.is_err());
    }

    #[test]
    fn expression_array() {
        assert_eq!(
            descend::expression_seq("[12, x[3], true]"),
            Ok(Expr::new(ExprKind::Array(vec![
                Expr::with_type(
                    ExprKind::Lit(Lit::I32(12)),
                    Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))))
                ),
                Expr::new(ExprKind::Index(
                    PlaceExpr::new(PlaceExprKind::Ident(Ident::new("x"))),
                    Nat::Lit(3)
                )),
                Expr::with_type(
                    ExprKind::Lit(Lit::Bool(true)),
                    Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                        ScalarTy::Bool
                    ))))
                )
            ])))
        );
    }

    #[test]
    fn expression_array_missing_parentheses() {
        let result = descend::expression_seq("[12, x[3], true)");
        assert!(result.is_err());
        let result = descend::expression_seq("[12, x[3], true]]");
        assert!(result.is_err());
        let result = descend::expression_seq("[12, x[3], true");
        assert!(result.is_err());
        let result = descend::expression_seq("([12, x[3], true)]");
        assert!(result.is_err());
    }

    #[test]
    fn expression_tupel() {
        assert_eq!(
            descend::expression_seq("(12, x[3], true)"),
            Ok(Expr::new(ExprKind::Tuple(vec![
                Expr::with_type(
                    ExprKind::Lit(Lit::I32(12)),
                    Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))))
                ),
                Expr::new(ExprKind::Index(
                    PlaceExpr::new(PlaceExprKind::Ident(Ident::new("x"))),
                    Nat::Lit(3)
                )),
                Expr::with_type(
                    ExprKind::Lit(Lit::Bool(true)),
                    Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                        ScalarTy::Bool
                    ))))
                )
            ])))
        );
    }

    #[test]
    fn expression_if_else() {
        macro_rules! common_expr {
            ($binop: expr) => {
                Box::new(Expr::new(ExprKind::BinOp(
                    $binop,
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::I32(7)),
                        Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32)))),
                    )),
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::I32(8)),
                        Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32)))),
                    )),
                )))
            };
        }
        assert_eq!(
            descend::expression_seq("if 7<8 <>{7+8} else <>{7*8}"),
            Ok(Expr::new(ExprKind::IfElse(
                common_expr!(BinOp::Lt),
                Box::new(Expr::new(ExprKind::Block(vec![], common_expr!(BinOp::Add)))),
                Box::new(Expr::new(ExprKind::Block(vec![], common_expr!(BinOp::Mul)))),
            )))
        );
    }

    #[test]
    fn expression_for_loop() {
        let x = Ident::new("x");
        assert_eq!(
            descend::expression_seq("for x in [1,2,3] <>{x = x+1}"),
            Ok(Expr::new(ExprKind::For(
                x.clone(),
                Box::new(Expr::new(ExprKind::Array(vec![
                    Expr::with_type(
                        ExprKind::Lit(Lit::I32(1)),
                        Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))))
                    ),
                    Expr::with_type(
                        ExprKind::Lit(Lit::I32(2)),
                        Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))))
                    ),
                    Expr::with_type(
                        ExprKind::Lit(Lit::I32(3)),
                        Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))))
                    )
                ]))),
                Box::new(Expr::new(ExprKind::Block(
                    vec![],
                    Box::new(Expr::new(ExprKind::Assign(
                        PlaceExpr::new(PlaceExprKind::Ident(x.clone())),
                        Box::new(Expr::new(ExprKind::BinOp(
                            BinOp::Add,
                            Box::new(Expr::new(ExprKind::PlaceExpr(PlaceExpr::new(
                                PlaceExprKind::Ident(x.clone())
                            )))),
                            Box::new(Expr::with_type(
                                ExprKind::Lit(Lit::I32(1)),
                                Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                                    ScalarTy::I32
                                ))))
                            ))
                        ),))
                    ),))
                )))
            ),))
        );
    }

    #[test]
    fn expression_for_loop_negative() {
        let result_expect_ident = descend::expression_seq("for (1+2) in [1,2,3] {x = x+1}");
        assert!(result_expect_ident.is_err());
    }

    #[test]
    fn expression_let() {
        assert_eq!(
            descend::expression_seq("let mut x : f32 = 17.123f32"),
            Ok(Expr::new(ExprKind::Let(
                Pattern::Ident(Mutability::Mut, Ident::new("x")),
                Box::new(Some(Ty::new(TyKind::Data(DataTy::new(
                    DataTyKind::Scalar(ScalarTy::F32)
                ))))),
                Box::new(Expr::with_type(
                    ExprKind::Lit(Lit::F32(17.123)),
                    Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::F32))))
                ))
            ),))
        );
    }

    #[test]
    fn expression_let_negative() {
        // Does there always have to be another instruction after let ?
        let result = descend::expression_seq("let mut x : 32 = 17.123f32;");
        assert!(result.is_err());
        let result = descend::expression_seq("let mut x:bool@gpu.shared@ = false;");
        assert!(result.is_err());
        let result = descend::expression_seq("let x:bool@Memory.Location = false;");
        assert!(result.is_err());
    }

    #[test]
    fn expressions_expect_matched_parentheses() {
        let result = descend::expression("(1+2");
        assert!(result.is_err());

        let result = descend::expression("(1+2))");
        assert!(result.is_err());

        let result = descend::expression("((1+2)");
        assert!(result.is_err());

        let result = descend::expression("1+2)");
        assert!(result.is_err());

        let result = descend::expression("1+2(");
        assert!(result.is_err());

        let result = descend::expression(")1+2");
        assert!(result.is_err());

        let result = descend::expression("(1+2)");
        assert!(result.is_ok());
    }

    #[test]
    fn expression_parenthesis_overriding_precedence() {
        // "natural" operator precendence without parenthesis
        assert_eq!(
            descend::expression("-1 + 2 * 3 + 4 + 5 * 6 * 7"),
            Ok(Expr::new(ExprKind::BinOp(
                BinOp::Add,
                Box::new(Expr::new(ExprKind::BinOp(
                    BinOp::Add,
                    Box::new(Expr::new(ExprKind::BinOp(
                        BinOp::Add,
                        Box::new(Expr::new(ExprKind::UnOp(
                            UnOp::Neg,
                            Box::new(Expr::with_type(
                                ExprKind::Lit(Lit::I32(1)),
                                Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                                    ScalarTy::I32
                                ))))
                            ))
                        ))),
                        Box::new(Expr::new(ExprKind::BinOp(
                            BinOp::Mul,
                            Box::new(Expr::with_type(
                                ExprKind::Lit(Lit::I32(2)),
                                Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                                    ScalarTy::I32
                                ))))
                            )),
                            Box::new(Expr::with_type(
                                ExprKind::Lit(Lit::I32(3)),
                                Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                                    ScalarTy::I32
                                ))))
                            ))
                        )))
                    ))),
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::I32(4)),
                        Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))))
                    ))
                ))),
                Box::new(Expr::new(ExprKind::BinOp(
                    BinOp::Mul,
                    Box::new(Expr::new(ExprKind::BinOp(
                        BinOp::Mul,
                        Box::new(Expr::with_type(
                            ExprKind::Lit(Lit::I32(5)),
                            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))))
                        )),
                        Box::new(Expr::with_type(
                            ExprKind::Lit(Lit::I32(6)),
                            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))))
                        ))
                    ))),
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::I32(7)),
                        Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))))
                    ))
                )))
            ),))
        );

        // precedences overridden via parentheses
        assert_eq!(
            descend::expression("-(1 + 2) * ((3 + (4 + 5) * 6) * 7)"),
            Ok(Expr::new(ExprKind::BinOp(
                BinOp::Mul,
                Box::new(Expr::new(ExprKind::UnOp(
                    UnOp::Neg,
                    Box::new(Expr::new(ExprKind::BinOp(
                        BinOp::Add,
                        Box::new(Expr::with_type(
                            ExprKind::Lit(Lit::I32(1)),
                            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))))
                        )),
                        Box::new(Expr::with_type(
                            ExprKind::Lit(Lit::I32(2)),
                            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))))
                        ))
                    ),))
                ),)),
                Box::new(Expr::new(ExprKind::BinOp(
                    BinOp::Mul,
                    Box::new(Expr::new(ExprKind::BinOp(
                        BinOp::Add,
                        Box::new(Expr::with_type(
                            ExprKind::Lit(Lit::I32(3)),
                            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))))
                        )),
                        Box::new(Expr::new(ExprKind::BinOp(
                            BinOp::Mul,
                            Box::new(Expr::new(ExprKind::BinOp(
                                BinOp::Add,
                                Box::new(Expr::with_type(
                                    ExprKind::Lit(Lit::I32(4)),
                                    Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                                        ScalarTy::I32
                                    ))))
                                )),
                                Box::new(Expr::with_type(
                                    ExprKind::Lit(Lit::I32(5)),
                                    Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                                        ScalarTy::I32
                                    ))))
                                ))
                            ))),
                            Box::new(Expr::with_type(
                                ExprKind::Lit(Lit::I32(6)),
                                Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(
                                    ScalarTy::I32
                                ))))
                            ))
                        )))
                    ))),
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::I32(7)),
                        Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))))
                    ))
                )))
            ),))
        );
    }

    #[test]
    fn global_fun_def_all_function_kinds() {
        // all currently available kinds are tested
        let src = r#"fn test_kinds<n: nat, a: prv, t: ty, m: mem>(
            ha_array: &a uniq cpu.mem [i32; n]
        ) -[cpu.thread]-> () <>{
            42
        }"#;
        let body = r#"42"#;

        let result = descend::fun_def(src).expect("Parsing failed");

        // TODO: Do proper check against expected AST
        let name = "test_kinds".into();
        let generic_params = vec![
            IdentKinded::new(&Ident::new("n"), Kind::Nat),
            IdentKinded::new(&Ident::new("a"), Kind::Provenance),
            IdentKinded::new(&Ident::new("t"), Kind::Ty),
            IdentKinded::new(&Ident::new("m"), Kind::Memory),
        ];
        let params = vec![ParamDecl {
            ident: Ident::new("ha_array"),
            ty: Some(Ty::new(TyKind::Data(DataTy::new(DataTyKind::Ref(
                Provenance::Ident(Ident::new("a")),
                Ownership::Uniq,
                Memory::CpuMem,
                Box::new(DataTy::new(DataTyKind::Array(
                    Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))),
                    Nat::Ident(Ident::new("n")),
                ))),
            ))))),
            mutbl: Mutability::Const,
        }];
        let ret_dty = DataTy::new(DataTyKind::Scalar(ScalarTy::Unit));
        let exec = Exec::CpuThread;
        let prv_rels = vec![];

        let intended = FunDef {
            name,
            param_decls: params,
            constraints: vec![],
            exec,
            prv_rels,
            body_expr: Expr::new(ExprKind::Block(
                vec![],
                Box::new(descend::expression(body).unwrap()),
            )),
            generic_params,
            ret_dty,
        };

        // assert_eq!(result.name, intended.name);
        // assert_eq!(result.params, intended.params);
        // assert_eq!(result.exec, intended.exec);
        // assert_eq!(result.prv_rels, intended.prv_rels);
        // assert_eq!(result.body_expr, intended.body_expr);
        // assert_eq!(result.generic_params, intended.generic_params);
        // assert_eq!(result.ret_dty, intended.ret_dty);
        assert_eq!(result, intended);
    }

    #[test]
    fn global_fun_def_kind_parameters_optional() {
        // test both versions with and without <> pointy brackets
        let src_1 = r#"fn no_kinds(
            ha_array: &'a uniq cpu.mem [i32; n],
            hb_array: &'b shrd cpu.mem [i32; n]
        ) -[cpu.thread]-> () <>{
            let answer_to_everything :i32 = 42;
            answer_to_everything
        }"#;
        let src_2 = r#"fn no_kinds<>(
            ha_array: &'a uniq cpu.mem [i32; n],
            hb_array: &'b shrd cpu.mem [i32; n]
        ) -[cpu.thread]-> () <>{
            let answer_to_everything :i32 = 42;
            answer_to_everything
        }"#;

        let result_1 = descend::fun_def(src_1);
        let result_2 = descend::fun_def(src_2);

        print!("{:?}", result_1);

        assert!(result_1.is_ok());
        assert!(result_2.is_ok());
    }

    #[test]
    fn global_fun_def_wrong_kinds_cause_error() {
        // kind type is spelled wrong
        let src = r#"fn wrong_kind_spelling<n: nat, a: prov, b: prv>(
            ha_array: &'a uniq cpu.heap [i32; n],
            hb_array: &'b shrd cpu.heap [i32; n]
        ) -[cpu.thread]-> () {
            let answer_to_everything :i32 = 42;
            answer_to_everything
        }"#;

        let result = descend::fun_def(src);

        assert!(result.is_err());
    }

    #[test]
    fn global_fun_def_no_function_parameters_required() {
        let src = r#"fn no_params<n: nat, a: prv, b: prv>() -[cpu.thread]-> () <>{            
            let answer_to_everything :i32 = 42;
            answer_to_everything
        }"#;

        let result = descend::fun_def(src);
        assert!(result.is_ok());
    }

    //span testing
    #[test]
    fn span_test_let_expression() {
        let line_col_source = SourceCode::new("let mut result : i32 = true".to_string());

        //span from expression after assertion
        let no_syntax_error_but_semantics_error =
            descend::expression_seq("let mut result : i32 = true");
        let result = match no_syntax_error_but_semantics_error {
            Ok(Expr {
                expr: ExprKind::Let(_, _, expr),
                ..
            }) => expr
                .span
                .map(|span| line_col_source.get_line_col(span.begin)),
            _ => None,
        };
        assert_eq!(
            result,
            Some((0, 23)),
            "cannot extract correct line and column from span"
        );

        //span from variable identifier
        let no_syntax_error_but_semantics_error =
            descend::expression_seq("let mut result : i32 = true");
        let result = match no_syntax_error_but_semantics_error {
            Ok(Expr {
                expr: ExprKind::Let(Pattern::Ident(_, ident), _, _),
                ..
            }) => ident
                .span
                .map(|span| line_col_source.get_line_col(span.begin)),
            err => {
                eprintln!("{:?}", err);
                None
            }
        };
        assert_eq!(
            result,
            Some((0, 8)),
            "cannot extract correct line and column from span"
        );
    }

    #[test]
    fn while_loop() {
        let src = r#"while 1 <= 2 <>{ let x = 5 }"#;
        let result = descend::expression(src);
        print!("{:?}", result.as_ref().unwrap());

        println!();
        assert_eq!(
            result,
            Ok(Expr::new(ExprKind::While(
                Box::new(Expr::new(ExprKind::BinOp(
                    BinOp::Le,
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::I32(1)),
                        Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))))
                    )),
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::I32(2)),
                        Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))))
                    ))
                ))),
                Box::new(Expr::new(ExprKind::Block(
                    vec![],
                    Box::new(Expr::new(ExprKind::Let(
                        Pattern::Ident(Mutability::Const, Ident::new("x")),
                        Box::new(None),
                        Box::new(Expr::with_type(
                            ExprKind::Lit(Lit::I32(5)),
                            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))))
                        ))
                    )))
                )))
            )))
        )
    }

    #[test]
    fn compil_unit_test_one() {
        let src = r#"
        
        fn foo() -[cpu.thread]-> () <>{
            42
        }
        
        "#;
        let result =
            descend::compil_unit(src).expect("Cannot parse compilation unit with one function");
        assert_eq!(result.len(), 1);
    }

    #[test]
    fn compil_unit_test_multiple() {
        let src = r#"
        
        fn foo() -[cpu.thread]-> () <>{
            42
        }

        fn bar() -[cpu.thread]-> () <>{
            24
        }


        fn baz() -[cpu.thread]-> () <>{
            1337
        }
        
        "#;
        let result = descend::compil_unit(src)
            .expect("Cannot parse compilation unit with multiple functions");
        assert_eq!(result.len(), 3);
    }

    #[test]
    fn compil_unit_test_fun_calls() {
        let src = r#"
        trait Eq {
            fn eq(&shrd cpu.mem self) -[cpu.thread]-> () { () }
        }
        struct Point {}
        impl Eq for Point {}
        fn foo<T>(t: T) -[cpu.thread]-> () where T:Eq {
            let p: Point = Point {};
            foo();
            Point::eq(p);
            p.eq();
            eq(p); //This should not typecheck
            T::eq(t);
            t.eq()
        }
        
        "#;
        let result =
            descend::compil_unit(src).expect("Cannot parse compilation unit with different function calls");
        assert_eq!(result.len(), 4);
    }

    #[test]
    fn compil_struct_decl() {
        let src = "struct Test ;";
        let result = descend::struct_def(src).expect("Cannot parse empty struct");

        let name = String::from("Test");
        let generic_params: Vec<IdentKinded> = vec![];
        let constraints: Vec<Constraint> = vec![];
        let decls: Vec<StructField> = vec![];

        assert_eq!(result,
            StructDef {name, generic_params, constraints, decls});
    }

    #[test]
    fn compil_struct_decl2() {
        let src = "struct Test { }";
        let result = descend::struct_def(src).expect("Cannot parse empty struct");

        let name = String::from("Test");
        let generic_params: Vec<IdentKinded> = vec![];
        let constraints: Vec<Constraint> = vec![];
        let decls: Vec<StructField> = vec![];

        assert_eq!(result,
            StructDef {name, generic_params, constraints, decls})
    }

    #[test]
    fn compil_struct_decl3() {
        let src = "struct Test { a: i32, b: f32 }";
        let result = descend::struct_def(src).expect("Cannot parse struct");

        let name = String::from("Test");
        let generic_params: Vec<IdentKinded> = vec![];
        let constraints: Vec<Constraint> = vec![];
        let name_a = String::from("a");
        let name_b = String::from("b");
        let ty_a = DataTy::new(DataTyKind::Scalar(ScalarTy::I32));
        let ty_b = DataTy::new(DataTyKind::Scalar(ScalarTy::F32));
        let field1 = StructField{name: name_a, ty: ty_a};
        let field2 = StructField{name: name_b, ty: ty_b};
        let decls: Vec<StructField> = vec![field1, field2];

        assert_eq!(result,
            StructDef {name, generic_params, constraints, decls});
    }

    #[test]
    fn compil_struct_decl4() {
        let src = "struct Test<T: dty, Q: dty> where Q:Number { }";
        let result = descend::struct_def(src).expect("Cannot parse empty struct with generics");

        let name = String::from("Test");
        let gen_param1 = Ident::with_span(String::from("T"), Span::new(12, 13));
        let gen_param2 = Ident::with_span(String::from("Q"), Span::new(20, 21));
        let generic_params: Vec<IdentKinded> = vec![
            IdentKinded::new(&gen_param1, Kind::DataTy),
            IdentKinded::new(&gen_param2, Kind::DataTy)];
        let constraints: Vec<Constraint> = vec![
            Constraint{
                param: DataTy::with_span(
                    DataTyKind::Ident(Ident::with_span(String::from("Q"), Span::new(34, 35))),
                    Span::new(32, 33)),
                trait_bound: TraitMonoType { name: String::from("Number"), generics: vec![] }}];
        let decls: Vec<StructField> = vec![];

        assert_eq!(result,
            StructDef {name, generic_params, constraints, decls});
    }

    #[test]
    fn compil_trait_decl() {
        let src = r#"trait Eq {
            fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
            fn eq2(&shrd cpu.mem self, test: &shrd cpu.mem Self) -[cpu.thread]-> bool {
                false
            }
        }"#;
        let result = descend::trait_def(src).expect("Cannot parse trait");

        assert_eq!(result.decls.len(), 2);
        let params1 = 
            match &result.decls[0] {
                AssociatedItem::FunDecl(fun_decl) => fun_decl.param_decls.clone(),
                _ => vec![]
            };
        let params2 = 
            match &result.decls[1] {
                AssociatedItem::FunDef(fun_decl) => fun_decl.param_decls.clone(),
                _ => vec![]
            };

        let name = String::from("Eq");
        let generic_params: Vec<IdentKinded> = vec![];
        let constraints: Vec<Constraint> = vec![];
        let decls: Vec<AssociatedItem> = vec![
            AssociatedItem::FunDecl(
                FunDecl{name: String::from("eq"),
                    generic_params: vec![],
                    constraints: vec![],
                    param_decls: params1,
                    ret_dty: DataTy::new(DataTyKind::Scalar(ScalarTy::Bool)),
                    exec: Exec::CpuThread,
                    prv_rels: vec![]}),
            AssociatedItem::FunDef(
                FunDef{name: String::from("eq2"),
                    generic_params: vec![],
                    constraints: vec![],
                    param_decls: params2,
                    ret_dty: DataTy::new(DataTyKind::Scalar(ScalarTy::Bool)),
                    exec: Exec::CpuThread,
                    prv_rels: vec![],
                    body_expr: Expr::new(ExprKind::Block(vec![],
                        Box::new(Expr::with_type(
                            ExprKind::Lit(Lit::Bool(false)),
                            Ty::new(TyKind::Data(DataTy::new(DataTyKind::Scalar(ScalarTy::Bool))))
                    ))))}),
        ];

        assert_eq!(result,
            TraitDef {name, generic_params, constraints, decls, supertraits: vec![]});        
    }

    #[test]
    fn compil_trait_decl2() {
        let src = r#"trait Ord: Eq {
            fn lt(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
            fn le(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
        }"#;

        let result = descend::trait_def(src).expect("Cannot parse empty struct");
        let supertraits = vec![
            TraitMonoType { name: String::from("Eq"), generics: vec![] },
        ];
        assert_eq!(result.constraints, vec![]);
        assert_eq!(result.supertraits, supertraits);
        assert_eq!(result.decls.len(), 2);
    }

    #[test]
    fn compil_trait_decl3() {
        let src = r#"trait Ord: Eq + Eq2 {
            fn lt(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
            fn le(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
        }"#;

        let result = descend::trait_def(src).expect("Cannot parse empty struct");
        let supertraits = vec![
            TraitMonoType { name: String::from("Eq"), generics: vec![] },
            TraitMonoType { name: String::from("Eq2"), generics: vec![] },
        ];
        assert_eq!(result.constraints, vec![]);
        assert_eq!(result.supertraits, supertraits);
        assert_eq!(result.decls.len(), 2);
    }

    #[test]
    fn compil_struct_and_trait() {
        let src = r#"
        struct Point {
            x: i32,
            y: i32
        }
        trait Eq {
            const important_const: f32;
            const magic_number: i32 = 42;
            fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
        }
        impl Eq for Point {
            fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Point) -[cpu.thread]-> bool {
                self.x == other.x && self.y == other.y
            }
        }
        struct GenericStruct<N: nat, Q: dty, S: dty> where Q: Number, S: SomeTrait {
            x: T
        }
        impl <T: dty, Q: dty, S: dty> GenericStruct where S: SomeTrait, Q: Number {
            fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Point) -[cpu.thread]-> bool {
                self.x == other.x && self.x == other.y
            }
        }
        fn bar() -[cpu.thread] -> Point {
            let x = 3;
            Point { x, y: 42 }
        }
        fn main() -[cpu.thread] -> () {
            let (p1, p2) = (Point {x: 3, y: 4}, Point {x: 4, y: 5});
            let test = Point::eq(p1, &shrd p2);
            let are_equal = p1.eq(&shrd p2);
            let x = bar().x
        }
        "#;
        let result = descend::compil_unit(src).expect("Cannot parse struct and trait");
        assert_eq!(result.len(), 7);
    }

    #[test]
    fn non_place_expr_assigment() {
        let src = r#"
        fn main() -[cpu.thread] -> () {
            bar().x = 42
        }
        "#;
        descend::compil_unit(src).expect_err("Assigment to non place_expr not possible");
    }

    #[test]
    fn test_struct_datatype() {
        let src = r#"
        fn main() -[cpu.thread] -> (){
            let p: Point<i32, i32> = x
        }
        "#;
        let result = descend::compil_unit(src).expect("Cannot use struct datatypes");
        assert_eq!(result.len(), 1);

        let letty =
            if let Item::FunDef(fun_def) = &result[0] {
                if let ExprKind::Block(_, expr) = &fun_def.body_expr.expr {
                    if let ExprKind::Let(_, ty, _) = &expr.expr {
                        ty.clone().unwrap().ty
                    } else {
                        panic!("Cannot recognize let expr");
                    }
                } else {
                    panic!("Cannot recognize block expr");
                }
            } else {
                panic!("Cannot recognize fundef");
            };

        if let TyKind::Data(dataty) = letty {
            assert_eq!(dataty,
                DataTy::with_span(
                    DataTyKind::Struct(StructDataType{
                            name: String::from("Point"),
                            attributes: vec![],
                            generic_args: vec![
                                ArgKinded::DataTy(DataTy::new(
                                    DataTyKind::Scalar(ScalarTy::I32))),
                                ArgKinded::DataTy(DataTy::new(
                                    DataTyKind::Scalar(ScalarTy::I32))),
                            ],
                        }),
                    Span::new(59, 64)));
        } else {
            panic!("Cannot recognize datatype");
        }
    }

    #[test]
    fn test_struct_datatype2() {
        let src = r#"
        struct Point {
            x: i32
        }
        fn main() -[cpu.thread] -> (){
            let p: Point = x
        }
        "#;
        let result = parse(
            &SourceCode::new(String::from(src)))
            .expect("Cannot use struct datatypes").item_defs;
        assert_eq!(result.len(), 2);

        let letty = 
            if let Item::FunDef(fun_def) = &result[1] {
                if let ExprKind::Block(_, expr) = &fun_def.body_expr.expr {
                    if let ExprKind::Let(_, ty, _) = &expr.expr {
                        ty.clone().unwrap().ty
                    } else {
                        panic!("Cannot recognize let expr");
                    }
                } else {
                    panic!("Cannot recognize block expr");
                }
            } else {
                panic!("Cannot recognize fundef");
            };

        let struct_ty = StructDataType{
            name: String::from("Point"),
            attributes: vec![
                StructField {
                    name: String::from("x"),
                    ty: DataTy::new(DataTyKind::Scalar(ScalarTy::I32))
                }
            ],
            generic_args: vec![],
        };

        if let TyKind::Data(dataty) = letty {
            assert_eq!(dataty,
                DataTy::with_span(
                    DataTyKind::Struct(struct_ty),
                    Span::new(59, 64)));
        } else {
            panic!("Cannot recognize datatype");
        }
    }

    #[test]
    fn test_struct_datatype3() {
        let src = r#"
        struct Point<T: dty> {
            x: T,
            y: T
        }
        fn main() -[cpu.thread] -> (){
            let p: Point<i32> = x
        }
        "#;
        let result = parse(
            &SourceCode::new(String::from(src)))
            .expect("Cannot use struct datatypes").item_defs;
        assert_eq!(result.len(), 2);

        let letty = 
            if let Item::FunDef(fun_def) = &result[1] {
                if let ExprKind::Block(_, expr) = &fun_def.body_expr.expr {
                    if let ExprKind::Let(_, ty, _) = &expr.expr {
                        ty.clone().unwrap().ty
                    } else {
                        panic!("Cannot recognize let expr");
                    }
                } else {
                    panic!("Cannot recognize block expr");
                }
            } else {
                panic!("Cannot recognize fundef");
            };

        let struct_ty = StructDataType{
            name: String::from("Point"),
            attributes: vec![
                StructField {
                    name: String::from("x"),
                    ty: DataTy::new(DataTyKind::Scalar(ScalarTy::I32))
                },
                StructField {
                    name: String::from("y"),
                    ty: DataTy::new(DataTyKind::Scalar(ScalarTy::I32))
                }
            ],
            generic_args: vec![
                ArgKinded::DataTy(DataTy::new(
                    DataTyKind::Scalar(ScalarTy::I32)))
            ],
        };

        if let TyKind::Data(dataty) = letty {
            assert_eq!(dataty,
                DataTy::with_span(
                    DataTyKind::Struct(struct_ty),
                    Span::new(59, 64)));
        } else {
            panic!("Cannot recognize datatype");
        }
    }

    #[test]
    fn test_parse_struct_and_trait() {
        let src = r#"
        struct Point {
            x: i32,
            y: i32
        }
        trait Eq {
            fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
        }
        impl Eq for Point {
            fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
                self.x == other.x && self.y == other.y
            }
        }
        impl Eq for i32 {
            fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
                self == other
            }
        }
        "#;
        let result = parse(
            &SourceCode::new(String::from(src)))
            .expect("Cannot parse structs, traits and impls").item_defs;
        assert_eq!(result.len(), 4);
    }

    #[test]
    fn test_replace_self() {
        let src = r#"
        struct Point {
            x: i32,
            y: i32
        }
        impl Point {
            fn getX(self) -[cpu.thread]-> i32 {
                self.x
            }
        }
        "#;
        let struct_ty = StructDataType{
            name: String::from("Point"),
            attributes: vec![
                StructField {
                    name: String::from("x"),
                    ty: DataTy::new(DataTyKind::Scalar(ScalarTy::I32))
                },
                StructField {
                    name: String::from("y"),
                    ty: DataTy::new(DataTyKind::Scalar(ScalarTy::I32))
                }
            ],
            generic_args: vec![],
        };
        let result = parse(
            &SourceCode::new(String::from(src)))
            .expect("Cannot parse structs and impl").item_defs;
        assert_eq!(result.len(), 2);
        if let Item::ImplDef(impl_def) = &result[1] {
            assert_eq!(impl_def.decls.len(), 1);
            if let AssociatedItem::FunDef(fun_def) = &impl_def.decls[0] {
                assert_eq!(fun_def.param_decls.len(), 1);
                assert_eq!(fun_def.param_decls[0].ident.name, "self");
                assert_eq!(fun_def.param_decls[0].ty.as_ref().unwrap(),
                    &Ty::new(TyKind::Data(DataTy::new(DataTyKind::Struct(
                        struct_ty
                    )))))
            } else {
                panic!("Does not recognize FunDef")
            }
        } else {
            panic!("Does not recognize ImplDef")
        }
    }
}