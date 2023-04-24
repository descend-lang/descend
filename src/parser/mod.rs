//! Module for components related to parsing
pub mod source;
mod utils;

use crate::ast::*;
use core::iter;
use error::ParseError;
use std::collections::HashMap;

use crate::error::ErrorReported;
pub use source::*;

use crate::ast::visit_mut::VisitMut;

pub fn parse<'a>(source: &'a SourceCode<'a>) -> Result<CompilUnit, ErrorReported> {
    let parser = Parser::new(source);
    let mut fun_defs = parser.parse().map_err(|err| err.emit())?;
    for fun_def in &mut fun_defs {
        replace_arg_kinded_idents(fun_def);
        replace_exec_idents_with_specific_execs(fun_def);
    }
    Ok(CompilUnit::new(fun_defs, source))
}

#[derive(Debug)]
struct Parser<'a> {
    source: &'a SourceCode<'a>,
}

impl<'a> Parser<'a> {
    fn new(source: &'a SourceCode<'a>) -> Self {
        Parser { source }
    }

    fn parse(&self) -> Result<Vec<FunDef>, ParseError<'_>> {
        descend::compil_unit(self.source.str()).map_err(|peg_err| ParseError::new(self, peg_err))
    }
}

fn replace_arg_kinded_idents(fun_def: &mut FunDef) {
    struct ReplaceArgKindedIdents {
        ident_names_to_kinds: HashMap<Box<str>, Kind>,
    }
    impl ReplaceArgKindedIdents {
        fn subst_in_gen_args(&self, gen_args: &mut [ArgKinded]) {
            for gen_arg in gen_args {
                if let ArgKinded::Ident(ident) = gen_arg {
                    let to_be_kinded = ident.clone();
                    match self.ident_names_to_kinds.get(&ident.name).unwrap() {
                        Kind::Provenance => {
                            *gen_arg = ArgKinded::Provenance(Provenance::Ident(to_be_kinded))
                        }
                        Kind::Memory => *gen_arg = ArgKinded::Memory(Memory::Ident(to_be_kinded)),
                        Kind::Nat => *gen_arg = ArgKinded::Nat(Nat::Ident(to_be_kinded)),
                        Kind::DataTy => {
                            *gen_arg =
                                ArgKinded::DataTy(DataTy::new(DataTyKind::Ident(to_be_kinded)))
                        }
                    }
                }
            }
        }
    }

    impl VisitMut for ReplaceArgKindedIdents {
        fn visit_expr(&mut self, expr: &mut Expr) {
            match &mut expr.expr {
                ExprKind::Block(block) => {
                    self.ident_names_to_kinds.extend(
                        block
                            .prvs
                            .iter()
                            .map(|prv| (prv.clone().into_boxed_str(), Kind::Provenance)),
                    );
                    self.visit_expr(&mut block.body)
                }
                ExprKind::DepApp(f, gen_args) => {
                    self.visit_expr(f);
                    self.subst_in_gen_args(gen_args);
                }
                ExprKind::AppKernel(app_kernel) => {
                    let AppKernel {
                        fun,
                        gen_args,
                        args,
                        ..
                    } = app_kernel.as_mut();
                    self.visit_expr(fun);
                    self.subst_in_gen_args(gen_args);
                    visit_mut::walk_list!(self, visit_expr, args)
                }
                ExprKind::App(f, gen_args, args) => {
                    self.visit_expr(f);
                    self.subst_in_gen_args(gen_args);
                    visit_mut::walk_list!(self, visit_expr, args)
                }
                ExprKind::ForNat(ident, _, body) => {
                    self.ident_names_to_kinds
                        .extend(iter::once((ident.name.clone(), Kind::Nat)));
                    self.visit_expr(body)
                }
                _ => visit_mut::walk_expr(self, expr),
            }
        }

        fn visit_view(&mut self, view: &mut View) {
            self.subst_in_gen_args(&mut view.gen_args);
            for v in &mut view.args {
                self.visit_view(v)
            }
        }

        fn visit_fun_def(&mut self, fun_def: &mut FunDef) {
            self.ident_names_to_kinds = fun_def
                .generic_params
                .iter()
                .map(|IdentKinded { ident, kind }| (ident.name.clone(), *kind))
                .collect();
            visit_mut::walk_fun_def(self, fun_def)
        }
    }
    let mut replace = ReplaceArgKindedIdents {
        ident_names_to_kinds: HashMap::new(),
    };
    replace.visit_fun_def(fun_def);
}

fn replace_exec_idents_with_specific_execs(fun_def: &mut FunDef) {
    struct ReplaceExecIdents {
        ident_names_to_exec_expr: Vec<(Box<str>, ExecExpr)>,
    }
    impl VisitMut for ReplaceExecIdents {
        fn visit_pl_expr(&mut self, pl_expr: &mut PlaceExpr) {
            match &mut pl_expr.pl_expr {
                PlaceExprKind::Select(ple, exec) => {
                    self.visit_pl_expr(ple);
                    expand_exec_expr(&self.ident_names_to_exec_expr, exec);
                }
                _ => visit_mut::walk_pl_expr(self, pl_expr),
            }
        }

        fn visit_indep(&mut self, indep: &mut Indep) {
            expand_exec_expr(&self.ident_names_to_exec_expr, &mut indep.split_exec);
            for (i, (ident, branch)) in indep
                .branch_idents
                .iter()
                .zip(&mut indep.branch_bodies)
                .enumerate()
            {
                let branch_exec_expr = ExecExpr::new(indep.split_exec.exec.clone().split_proj(
                    indep.dim_compo,
                    indep.pos.clone(),
                    i as u8,
                ));
                self.ident_names_to_exec_expr
                    .push((ident.name.clone(), branch_exec_expr));
                self.visit_expr(branch);
                self.ident_names_to_exec_expr.pop();
            }
        }

        fn visit_sched(&mut self, sched: &mut Sched) {
            expand_exec_expr(&self.ident_names_to_exec_expr, &mut sched.sched_exec);
            let mut body_exec = ExecExpr::new(sched.sched_exec.exec.clone().distrib(sched.dim));
            if let Some(ident) = &sched.inner_exec_ident {
                self.ident_names_to_exec_expr
                    .push((ident.name.clone(), body_exec));
            }
            self.visit_block(&mut sched.body);
            self.ident_names_to_exec_expr.pop();
        }

        fn visit_expr(&mut self, expr: &mut Expr) {
            match &mut expr.expr {
                ExprKind::Sync(exec) => {
                    for exec in exec {
                        expand_exec_expr(&self.ident_names_to_exec_expr, exec);
                    }
                }
                _ => visit_mut::walk_expr(self, expr),
            }
        }
    }

    fn expand_exec_expr(exec_mapping: &[(Box<str>, ExecExpr)], exec_expr: &mut ExecExpr) {
        match &exec_expr.exec.base {
            BaseExec::CpuThread | BaseExec::GpuGrid(_, _) => {}
            BaseExec::Ident(ident) => {
                if let Some(exec) = get_exec_expr(exec_mapping, ident) {
                    let new_base = exec.exec.base.clone();
                    let mut new_exec_path = exec.exec.path.clone();
                    new_exec_path.append(&mut exec_expr.exec.path.clone());
                    exec_expr.exec.base = new_base;
                    exec_expr.exec.path = new_exec_path;
                };
            }
        }
    }

    fn get_exec_expr(exec_mapping: &[(Box<str>, ExecExpr)], ident: &Ident) -> Option<ExecExpr> {
        for (i, exec) in exec_mapping.iter().rev() {
            if i == &ident.name {
                return Some(exec.clone());
            }
        }
        None
    }

    let mut replace_exec_idents = ReplaceExecIdents {
        ident_names_to_exec_expr: vec![],
    };
    replace_exec_idents.visit_fun_def(fun_def);
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
            let line_num =
                u32::try_from(self.err.location.line).expect("Source file is unexpectedly large");
            let column_num =
                u32::try_from(self.err.location.column).expect("Source file is unexpectedly large");
            let snippet = single_line_parse_snippet(
                self.parser.source,
                &label,
                line_num,
                column_num,
                column_num + 1,
            );
            println!("{}", DisplayList::from(snippet));
            ErrorReported
        }
    }

    fn single_line_parse_snippet<'a>(
        source: &'a SourceCode<'a>,
        label: &'a str,
        line_num: u32,
        begin_column: u32,
        end_column: u32,
    ) -> Snippet<'a> {
        // 1-based offsets to 0-based offsets
        crate::error::single_line_snippet(
            source,
            label,
            label,
            line_num - 1,
            begin_column - 1,
            end_column - 1,
        )
    }
}

peg::parser! {
    pub(crate) grammar descend() for str {

        pub(crate) rule compil_unit() -> Vec<FunDef>
            = _ funcs:(fun:global_fun_def() { fun }) ** _ _ {
                funcs
            }

        pub(crate) rule global_fun_def() -> FunDef
            = "fn" __ ident:ident() _ generic_params:("<" _ t:(kind_parameter() ** (_ "," _)) _ ">" {t})? _
            "(" _ param_decls:(fun_parameter() ** (_ "," _)) _ ")" _
            "-" _ "[" _ exec_decl:ident_exec() _ "]" _ "-" _ ">" _ ret_dty:dty() _
            body:block() {
                let generic_params = match generic_params {
                    Some(generic_params) => generic_params,
                    None => vec![]
                };
                FunDef {
                  ident,
                  generic_params,
                  param_decls,
                  ret_dty,
                  exec_decl,
                  prv_rels: vec![],
                  body: Box::new(body)
                }
            }

        rule ident_exec() -> IdentExec =
            exec_ident:ident() _ ":" _ exec_ty: exec_ty() {
                IdentExec::new(exec_ident, exec_ty)
            }

        rule kind_parameter() -> IdentKinded
            = name:ident() _ ":" _ kind:kind() {
                IdentKinded::new(&name, kind)
            }

        rule fun_parameter() -> ParamDecl
            = mutbl:(m:mutability() __ {m})? ident:ident() _ ":" _ ty:ty() {
                let mutbl = mutbl.unwrap_or(Mutability::Const);
                ParamDecl { ident, ty:Some(ty), mutbl }
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
                    ExprKind::Let(pattern, typ.map(Box::new), Box::new(expr)),
                    Span::new(begin, end)
                )
            }
            / let_uninit()
            / "for" __ ident:ident() __ "in" __ collection:expression()
                _ body:block_expr()
            {
                Expr::new(ExprKind::For(ident, Box::new(collection), Box::new(body)))
            }
            / "while" __ cond:expression() __ body:block_expr() {
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
            // e:(@) ns:("." _ n:nat_literal() {n})+ {
            //     ns.into_iter().fold(e,
            //         |prev, n| Expr::new(ExprKind::Proj(Box::new(prev), n))
            //     )
            // }

            begin:position!() func:ident() place_end:position!() _
                kind_args:kind_args()?
                args:args() end:position!()
            {
                Expr::new(
                    ExprKind::App(
                        Box::new(Expr::with_span(
                            ExprKind::PlaceExpr(Box::new(PlaceExpr::new(PlaceExprKind::Ident(func)))),
                            Span::new(begin, place_end)
                        )),
                        kind_args.unwrap_or(vec![]),
                        args
                    )
                )
            }
            begin:position!() func:ident() end:position!() _ kind_args:kind_args() {
                Expr::new(
                    ExprKind::DepApp(
                        Box::new(Expr::with_span(
                            ExprKind::PlaceExpr(Box::new(PlaceExpr::new(PlaceExprKind::Ident(func)))),
                            Span::new(begin, end)
                        )),
                        kind_args
                ))
            }
            func:ident() _ "::<<<" _ grid_dim:dim() _ "," _ block_dim:dim()
                mshrd:(_ ";" _ shrd_mem_dtys: dty() ** (_ "," _)
                    mprvs:(_ ";" _ prvs:prov_value() ** (_ "," _) { prvs })? {
                        (shrd_mem_dtys, mprvs)
                })? _ ">>>"
                mkind_arg_list:(_ klist:kind_args() { klist })?
                args:args() {
                    let (shared_mem_dtys, shared_mem_prvs) = if let Some((dtys, prvs)) = mshrd {
                        let prvs = if let Some(prvs) = prvs { prvs } else { vec![] };
                        (dtys, prvs)
                    } else { (vec![], vec![]) };
                    let gen_args = if let Some(gen_args) = mkind_arg_list { gen_args }
                    else { vec![] };
                    Expr::new(ExprKind::AppKernel(Box::new(AppKernel {
                        grid_dim, block_dim, shared_mem_dtys, shared_mem_prvs,
                        fun: Box::new(Expr::new(ExprKind::PlaceExpr(Box::new(
                                PlaceExpr::new(PlaceExprKind::Ident(func))))
                            )),
                        gen_args,
                        args,
                    })))
            }
            l:literal() {
                Expr::with_type(
                    ExprKind::Lit(l),
                    Ty::new(TyKind::Data(Box::new(utils::type_from_lit(&l))))
                )
            }
            "sync" maybe_exec:(_ "(" _ exec:exec_expr() _ ")" { exec })?  {
                Expr::new(ExprKind::Sync(maybe_exec))
            }
            e:pl_expr_maybe_assignment() { e }
            "&" _ prov:(v:prov_value() __ { v })? own:ownership() __ p:place_expression() {
                Expr::new(ExprKind::Ref(prov, own, Box::new(p)))
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
            "if" __ cond:expression() _ iftrue:block_expr() _ iffalse:("else" _ iffalse:block_expr() {
                iffalse })? {
                Expr::new( match iffalse {
                    Some(false_block) => ExprKind::IfElse(Box::new(cond), Box::new(iftrue), Box::new(false_block)),
                    None => ExprKind::If(Box::new(cond), Box::new(iftrue))
                })
            }
            "for_nat" __ ident:ident() __ "in" __ range:nat() _ body:block_expr() {
                Expr::new(ExprKind::ForNat(ident, range, Box::new(body)))
            }
            "indep" _ "(" _ dim:dim_component() _ ")" __ n:nat() __ exec:exec_expr() _ "{" _
                branch:(branch_ident:ident() _ "=>" _
                    branch_body:expression() { (branch_ident, branch_body) }) **<1,> (_ "," _) _
            "}" {
                Expr::new(ExprKind::Indep(Box::new(Indep::new(dim,
                    n, exec,
                    branch.iter().map(|(i, _)| i.clone()).collect(),
                    branch.iter().map(|(_, b)| b.clone()).collect()))))
            }
            "sched" sched:(_ "(" _ dim:dim_component() _ ")" { dim })? __
                inner_exec_ident:maybe_ident() __ "in" __ sched_exec:exec_expr() _ body:block() {
                Expr::new(ExprKind::Sched(Box::new(Sched::new(match sched {
                    Some(d) => d,
                    None => DimCompo::X,
                }, inner_exec_ident, sched_exec, body))))
            }
            "|" _ params:(lambda_parameter() ** (_ "," _)) _ "|" _
              "-" _ "[" _ exec_decl:ident_exec() _ "]" _ "-" _ ">" _ ret_dty:dty() _
              body_expr:block_expr() {
                Expr::new(ExprKind::Lambda(params, exec_decl, Box::new(ret_dty), Box::new(body_expr)))
            }
            block:block_expr() { block }
            expression: expr_helper() { expression }
        }

        rule pl_expr_maybe_assignment() -> Expr =
            p:place_expression()
            expr:(_ "=" _ e:expression() {e})? {
                match expr {
                    None => Expr::new(ExprKind::PlaceExpr(Box::new(p))),
                    Some(expr) => Expr::new(ExprKind::Assign(Box::new(p), Box::new(expr))),
                }
            }

        rule maybe_ident() -> Option<Ident> =
            i:ident() { Some(i) }
            / "_" { None }

        rule dim_component() -> DimCompo =
            "X" { DimCompo::X }
        /   "Y" { DimCompo::Y }
        /   "Z" { DimCompo::Z }

        rule block_expr() -> Expr =
            block:block() {
                Expr::new(ExprKind::Block(block))
            }

        rule block() -> Block =
            prov_values:("<" _ prov_values:prov_value() ** (_ "," _)  _ ">" _ { prov_values })?
                "{" _ body:expression_seq() _ "}"
            {
                    if prov_values.is_some() { Block::with_prvs(prov_values.unwrap(), body) }
                    else { Block::new(body) }
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
        rule args() -> Vec<Expr> = "(" _ args:expression() ** (_ "," _) _ ")" { args }
        rule kind_args() -> Vec<ArgKinded> = "::<" _ k:kind_argument() ** (_ "," _) _ ">" { k }
        // TODO make nat expressions aside from literals parsable.
        //  the current problem is, that a nat expression cannot be recognized as such, if it starts
        //  with an identifier, because identifiers are parsed generically. Just assuming the ident
        //  is nat would be wrong too (i.e., simply checking for nat first and then for generic ident).
        /// Parse a kind argument
        pub(crate) rule kind_argument() -> ArgKinded
            = !identifier() result:(
                n:nat() { ArgKinded::Nat(n) }
                / mem:memory_kind() { ArgKinded::Memory(mem) }
                / dty:dty() { ArgKinded::DataTy(dty) }
                / prov:provenance() { ArgKinded::Provenance(prov) }
            ) { result }
            / ident:ident() { ArgKinded::Ident(ident)}

        /// Place expression
        pub(crate) rule place_expression() -> PlaceExpr
            = precedence!{
                "*" _ deref:@ {
                    PlaceExpr::new(PlaceExprKind::Deref(Box::new(deref)))
                }
                --
                pl_expr:@ _ "[" _ ".." _ split_pos:nat() _ ".." _ "]" {
                    PlaceExpr::new(
                        PlaceExprKind::View(Box::new(pl_expr),
                            Box::new(View { name: Ident::new("split_at"),
                                gen_args: vec![ArgKinded::Nat(split_pos)], args: vec![] })))
                }
                pl_expr:@ _ "[" _ idx:nat() _ "]" {
                    PlaceExpr::new(PlaceExprKind::Idx(Box::new(pl_expr), Box::new(idx)))
                }
                pl_expr:@ exec:(_ "[" _ "[" _ exec:exec_expr() _ "]" _ "]"{ exec }) {
                    PlaceExpr::new(PlaceExprKind::Select(Box::new(pl_expr), Box::new(exec)))
                }
                --
                proj:@ _ "." _ n:nat_literal() { PlaceExpr::new(PlaceExprKind::Proj(Box::new(proj), n)) }
                pl_expr:@ _ "." _ v:view_app() { PlaceExpr::new(PlaceExprKind::View(Box::new(pl_expr), Box::new(v))) }
                --
                begin:position!() pl_expr:@ end:position!() {
                    PlaceExpr {
                        span: Some(Span::new(begin, end)),
                        ..pl_expr
                    }
                }
                ident:ident() { PlaceExpr::new(PlaceExprKind::Ident(ident)) }
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

        pub(crate) rule view_app() -> View =
            view_ident:view_ident() mkargs:(_ kargs:kind_args() { kargs })?
                margs:(_ "(" _ args: view_app() **<1,> (_ "," _) _ ")" { args })? {
                    View { name: view_ident,
                        gen_args: mkargs.unwrap_or_default(),
                        args: margs.unwrap_or_default()
                    }
            }

        /// Parse nat token
        pub(crate) rule nat() -> Nat = precedence! {
            func:ident() _
                "(" _ args:nat() ** (_ "," _) _ ")" end:position!()
            {
                Nat::App(func, args.into_boxed_slice())
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
                Ty::with_span(TyKind::Data(Box::new(dty)), Span::new(begin, end))
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
            / name:ident() { DataTyKind::Ident(name) }
            / "(" _ types:dty() ** ( _ "," _ ) _ ")" { DataTyKind::Tuple(types) }
            / "[" _ t:dty() _ ";" _ n:nat() _ "]" { DataTyKind::Array(Box::new(t), n) }
            / "[" _ "[" _ dty:dty() _ ";" _ n:nat() _ "]" _ "]" {
                DataTyKind::ArrayShape(Box::new(dty), n)
            }
            / "&" _ prov:(prv:provenance() __ { prv })? own:ownership() __ mem:memory_kind() __ dty:dty() {
                DataTyKind::Ref(Box::new(RefDty::new(match prov {
                    Some(prv) => prv,
                    None => Provenance::Ident(Ident::new_impli(&crate::ast::utils::fresh_name("r")))
                }, own, mem, dty)))
            }
            / "_" { DataTyKind::Ident(Ident::new_impli(&crate::ast::utils::fresh_name("d"))) }

        rule exec_expr() -> ExecExpr =
            begin:position!() exec:exec() end:position!() {
                ExecExpr { exec: Box::new(exec), ty: None, span: Some(Span::new(begin,end)) }
            }

        rule exec() -> Exec =
            base:base_exec()
            maybe_exec_path_elems:(_ "." _  exec_path_elems: exec_path_elem() **<1,> _ "." _ { exec_path_elems })? {
                if let Some(path) = maybe_exec_path_elems {
                    Exec::with_path(base, path)
                } else { Exec::new(base) }
            }

        rule base_exec() -> BaseExec =
            ident:ident() { BaseExec::Ident(ident) }
            / "cpu.thread" { BaseExec::CpuThread }
            / "gpu.grid" _ "<" _ gdim:dim() _ "," _ bdim:dim() _ ">" { BaseExec::GpuGrid(gdim, bdim) }

        rule exec_path_elem() -> ExecPathElem =
            "distrib" _ "<" _ dim_compo:dim_component() _ ">" { ExecPathElem::Distrib(dim_compo) }
            / "split_proj" _ "<" _ dim_compo:dim_component() _ "," _ pos:nat() _ "," _ proj:("0" { 0 }/ "1" { 1 }) _ ">" {
                ExecPathElem::SplitProj(Box::new(SplitProj::new(dim_compo, pos, proj)))
            }

        rule exec_ty() -> ExecTy =
            begin:position!() exec:exec_ty_kind() end:position!() {
            ExecTy { ty: exec, span: Some(Span::new(begin,end)) }
        }

        rule exec_ty_kind() -> ExecTyKind =
            "cpu.thread" {
                ExecTyKind::CpuThread
            }
            / "gpu.grid" _ "<" _ g_dim:dim() _ "," _ b_dim:dim() _ ">" {
                ExecTyKind::GpuGrid(g_dim, b_dim)
            }
            / "gpu.block" _ "<" _ b_dim:dim() _ ">" {
                ExecTyKind::GpuBlock(b_dim)
            }
            / "gpu.global_threads" _ "<" _ t_dim:dim() _ ">" {
                ExecTyKind::GpuGlobalThreads(t_dim)
            }
            / "gpu.block_grp" _ "<" _ g_dim:dim() _ "," _ b_dim:dim() _ ">" {
                ExecTyKind::GpuBlockGrp(g_dim, b_dim)
            }
            / "gpu.thread_grp" _ "<" _ t_dim:dim() _ ">" {
                ExecTyKind::GpuThreadGrp(t_dim)
            }
            / "gpu.thread" {
                ExecTyKind::GpuThread
            }
            / "view" {
                ExecTyKind::View
            }

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

        pub(crate) rule kind() -> Kind
            = "nat" { Kind::Nat }
            / "mem" { Kind::Memory }
            / "dty" { Kind::DataTy }
            / "prv" { Kind::Provenance }

        rule dim() -> Dim
            = "XYZ" _ "<" _ dim3d:dim3d() _ ">" { Dim::XYZ(Box::new(dim3d)) }
            / "XY" _ "<" _ dim2d:dim2d() _ ">" { Dim::XY(Box::new(dim2d)) }
            / "XZ" _ "<" _ dim2d:dim2d() _ ">" { Dim::XZ(Box::new(dim2d)) }
            / "YZ" _ "<" _ dim2d:dim2d() _ ">" { Dim::YZ(Box::new(dim2d)) }
            / "X" _ "<" _ dim1d:dim1d() _ ">" { Dim::X(Box::new(dim1d)) }
            / "Y" _ "<" _ dim1d:dim1d() _ ">" { Dim::Y(Box::new(dim1d)) }
            / "Z" _ "<" _ dim1d:dim1d() _ ">" { Dim::Z(Box::new(dim1d)) }

        rule dim3d() -> Dim3d = n1:nat() _ "," _ n2:nat() _ "," _ n3:nat() { Dim3d(n1, n2, n3) }
        rule dim2d() -> Dim2d = n1:nat() _ "," _ n2:nat() { Dim2d(n1, n2) }
        rule dim1d() -> Dim1d = n:nat() { Dim1d(n) }

        rule ident() -> Ident
            = begin:position!() ident:$(identifier()) end:position!() {
                Ident::with_span(ident, Span::new(begin, end))
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

        // Take care! The order of keywords matters.
        //
        // For example: if "in" comes before "indep", then
        // "in" matches when parsing "indep". The negative lookahead at the end then checks that there
        // are no follow-up symbols. But there is still "dep" left to be parsed.
        // Therefore, the rule fails, even though it should have succeeded.
        rule keyword() -> ()
            = (("crate" / "super" / "self" / "Self" / "const" / "mut" / "uniq" / "shrd" / "indep" / "in" / "to_thread_grp" / "to" / "with"
                / "f32" / "f64" / "i32" / "u32" / "bool" / "Atomic<i32>" / "Atomic<bool>" / "Gpu" / "nat" / "mem" / "ty" / "prv" / "own"
                / "let"("prov")? / "if" / "else" / "sched" / "for_nat" / "for" / "while" / "fn" / "with" / "split_exec" / "split"
                / "cpu.mem" / "gpu.global" / "gpu.shared" / "sync"
                / "cpu.thread" / "gpu.grid" / "gpu.block" / "gpu.global_threads" / "gpu.block_grp" / "gpu.thread_grp" / "gpu.thread" / "view"
                / view_name())
                !['a'..='z'|'A'..='Z'|'0'..='9'|'_']
            )

        rule view_name() -> ()
            = ("to_view" / "grp" / "map" / "transp" / "join" / "rev")

        rule view_identifier() -> String =
            s:$(&view_name() (['a'..='z'|'A'..='Z'] ['a'..='z'|'A'..='Z'|'0'..='9'|'_']*
            / ['_']+ ['a'..='z'|'A'..='Z'|'0'..='9'] ['a'..='z'|'A'..='Z'|'0'..='9'|'_']*))
        {
            s.into()
        }

        rule view_ident() -> Ident =
            begin:position!() ident:$(view_identifier()) end:position!() {
                Ident::with_span(ident, Span::new(begin, end))
            }

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
        rule _() = quiet!{ (whitespace_char() / inline_comment() / line_comment())* }
        /// At least one whitespace
        rule __() = quiet!{ (whitespace_char() / inline_comment() / line_comment())+ }

        rule whitespace_char() = [' '|'\n'|'\t'|'\r'] // 0 or more whitespaces
        rule line_comment() = "//" (!['\n'][_])* (['\n'] / ![_]) // Comment to EOL
        rule inline_comment() = "/*" (!"*/"[_])* "*/"  // Block comment

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
            Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
                DataTyKind::Scalar(ScalarTy::F32)
            ))))),
            "does not recognize f32 type"
        );
        assert_eq!(
            descend::ty("i32"),
            Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
                DataTyKind::Scalar(ScalarTy::I32)
            ))))),
            "does not recognize i32 type"
        );
        assert_eq!(
            descend::ty("u32"),
            Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
                DataTyKind::Scalar(ScalarTy::U32)
            ))))),
            "does not recognize u32 type"
        );
        assert_eq!(
            descend::ty("()"),
            Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
                DataTyKind::Scalar(ScalarTy::Unit)
            ))))),
            "does not recognize unit type"
        );
        assert_eq!(
            descend::ty("bool"),
            Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
                DataTyKind::Scalar(ScalarTy::Bool)
            ))))),
            "does not recognize Boolean type"
        );
    }

    #[test]
    fn ty_gpu() {
        assert_eq!(
            descend::ty("Gpu"),
            Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
                DataTyKind::Scalar(ScalarTy::Gpu)
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
                ty_unit
            ]))),
            "does not recognize (unit,unit,unit) tuple type"
        );
    }

    #[test]
    fn ty_array_and_array_view() {
        assert_eq!(
            descend::ty("[f32;42]"),
            Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
                DataTyKind::Array(
                    Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::F32))),
                    Nat::Lit(42)
                )
            ))))),
            "does not recognize [f32;42] type"
        );
        assert_eq!(
            descend::ty("[u32;43]"),
            Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
                DataTyKind::Array(
                    Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::U32))),
                    Nat::Lit(43)
                )
            ))))),
            "does not recognize [u32;43] type"
        );
        // TODO: Implement identifer parsing in nat
        // assert_eq!(descend::ty("[();N]"), Ok(Ty::Array(Box::new(
        //     Ty::Scalar(ScalarTy::Unit)),
        //     Nat::Ident(Nat::new_ident("N")))
        // ), "does not recognize [();N] type");
        assert_eq!(
            descend::ty("[[i32;24]]"),
            Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
                DataTyKind::ArrayShape(
                    Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))),
                    Nat::Lit(24)
                )
            ))))),
            "does not recognize [[f32;24]] type"
        );
    }

    #[test]
    fn ty_identifier() {
        assert_eq!(
            descend::ty("T"),
            Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
                DataTyKind::Ident(Ident::new("T"))
            ))))),
            "does not recognize T type"
        );
    }

    #[test]
    fn ty_reference() {
        assert_eq!(
            descend::ty("&'a uniq cpu.mem i32"),
            Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
                DataTyKind::Ref(Box::new(RefDty::new(
                    Provenance::Value("'a".into()),
                    Ownership::Uniq,
                    Memory::CpuMem,
                    DataTy::new(DataTyKind::Scalar(ScalarTy::I32))
                )))
            ))))),
            "does not recognize type of unique i32 reference in cpu heap with provenance 'a"
        );
        assert_eq!(descend::ty("&b shrd gpu.global [f32;N]"), Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Ref(
            Box::new(RefDty::new(
                        Provenance::Ident(Ident::new("b")),
                        Ownership::Shrd,
                        Memory::GpuGlobal,
                        DataTy::new(DataTyKind::Array(
                            Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::F32))),
                            Nat::Ident(Ident::new("N"))
                        ))
                    )))))),
        )), "does not recognize type of shared [f32] reference in gpu global memory with provenance b");
    }

    #[test]
    fn ty_memory_kind() {
        assert_eq!(
            descend::ty("i32 @ cpu.mem"),
            Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
                DataTyKind::At(
                    Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))),
                    Memory::CpuMem
                )
            ))))),
            "does not recognize f32 @ cpu.stack type"
        );
        assert_eq!(
            descend::ty("[f32;42] @ gpu.global"),
            Ok(Ty::new(TyKind::Data(Box::new(DataTy::new(
                DataTyKind::At(
                    Box::new(DataTy::new(DataTyKind::Array(
                        Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::F32))),
                        Nat::Lit(42)
                    ))),
                    Memory::GpuGlobal
                )
            ))))),
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

    // #[test]
    // fn execution_resource() {
    //     assert_eq!(
    //         descend::execution_resource("cpu.thread"),
    //         Ok(Exec::CpuThread),
    //         "does not recognize cpu.stack memory kind"
    //     );
    //     assert_eq!(
    //         descend::execution_resource("gpu.block"),
    //         Ok(Exec::GpuBlock(1)),
    //         "does not recognize gpu.block memory kind"
    //     );
    //     assert_eq!(
    //         descend::execution_resource("gpu.thread"),
    //         Ok(Exec::GpuThread),
    //         "does not recognize gpu.global memory kind"
    //     );
    // }

    #[test]
    fn literal() {
        assert_eq!(descend::literal("()"), Ok(Lit::Unit));
        assert_eq!(
            descend::literal("true"),
            Ok(Lit::Bool(true)),
            "does not parse boolean correctly"
        );
        assert!(
            descend::literal("False").is_err(),
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
        assert!(
            descend::literal("12345ad").is_err(),
            "incorrectly parsing invalid literal"
        );
        assert!(
            descend::literal("e54").is_err(),
            "incorrectly parsing e-notation only to literal"
        );
        assert!(
            descend::literal("-i32").is_err(),
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
            descend::kind("dty"),
            Ok(Kind::DataTy),
            "does not recognize dty kind"
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
                0
            ))),
            "does not recognize place expression projection `x.0`"
        );
        assert_eq!(
            descend::place_expression("*x.0"),
            Ok(PlaceExpr::new(PlaceExprKind::Deref(Box::new(
                PlaceExpr::new(PlaceExprKind::Proj(
                    Box::new(PlaceExpr::new(PlaceExprKind::Ident(Ident::new("x")))),
                    0
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
            Ok(Expr::new(ExprKind::PlaceExpr(Box::new(PlaceExpr::new(
                PlaceExprKind::Proj(
                    Box::new(PlaceExpr::new(PlaceExprKind::Ident(Ident::new("x")))),
                    0
                )
            ))))),
            "does not recognize place expression projection `x.0`"
        );
        assert_eq!(
            descend::expression("*x.0"),
            Ok(Expr::new(ExprKind::PlaceExpr(Box::new(PlaceExpr::new(
                PlaceExprKind::Deref(Box::new(PlaceExpr::new(PlaceExprKind::Proj(
                    Box::new(PlaceExpr::new(PlaceExprKind::Ident(Ident::new("x")))),
                    0
                ))))
            ))))),
            "does not recognize place expression `*x.0`"
        );

        // No place expressions
        // assert_eq!(
        //     descend::expression("f::<x>().0"),
        //     Ok(Expr::new(ExprKind::Proj(
        //         Box::new(Expr::new(ExprKind::App(
        //             Box::new(Expr::new(ExprKind::PlaceExpr(Box::new(PlaceExpr::new(
        //                 PlaceExprKind::Ident(Ident::new("f"))
        //             ))))),
        //             vec![ArgKinded::Ident(Ident::new("x"))],
        //             vec![]
        //         ))),
        //         zero_literal
        //     ))),
        //     "does not recognize projection on function application"
        // );
        // assert_eq!(
        //     descend::expression("(x, y, z).1"),
        //     Ok(Expr::new(ExprKind::Proj(
        //         Box::new(Expr::new(ExprKind::Tuple(vec![
        //             Expr::new(ExprKind::PlaceExpr(Box::new(PlaceExpr::new(
        //                 PlaceExprKind::Ident(Ident::new("x"))
        //             )))),
        //             Expr::new(ExprKind::PlaceExpr(Box::new(PlaceExpr::new(
        //                 PlaceExprKind::Ident(Ident::new("y"))
        //             )))),
        //             Expr::new(ExprKind::PlaceExpr(Box::new(PlaceExpr::new(
        //                 PlaceExprKind::Ident(Ident::new("z"))
        //             ))))
        //         ]))),
        //         one_literal
        //     ))),
        //     "does not recognize projection on tuple view expression"
        // );
    }

    #[test]
    fn expression_literal() {
        assert_eq!(
            descend::expression("7"),
            Ok(Expr::with_type(
                ExprKind::Lit(Lit::I32(7)),
                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                    ScalarTy::I32
                )))))
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
                    Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                        ScalarTy::I32
                    )))))
                )),
                Box::new(Expr::with_type(
                    ExprKind::Lit(Lit::I32(8)),
                    Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                        ScalarTy::I32
                    )))))
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
                        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                            ScalarTy::I32
                        )))))
                    )),
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::I32(6)),
                        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                            ScalarTy::I32
                        )))))
                    ))
                ),)),
                Box::new(Expr::with_type(
                    ExprKind::Lit(Lit::I32(7)),
                    Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                        ScalarTy::I32
                    )))))
                ))
            ),))
        );
    }

    #[test]
    fn expression_place_expr() {
        assert_eq!(
            descend::expression_seq("someIdentifier"),
            Ok(Expr::new(ExprKind::PlaceExpr(Box::new(PlaceExpr::new(
                PlaceExprKind::Ident(Ident::new("someIdentifier"))
            )))))
        );
        assert_eq!(
            descend::expression_seq("*x"),
            Ok(Expr::new(ExprKind::PlaceExpr(Box::new(PlaceExpr::new(
                PlaceExprKind::Deref(Box::new(PlaceExpr::new(PlaceExprKind::Ident(Ident::new(
                    "x"
                )))))
            )))))
        );
        assert_eq!(
            descend::expression_seq("**x.7"),
            Ok(Expr::new(ExprKind::PlaceExpr(Box::new(PlaceExpr::new(
                PlaceExprKind::Deref(Box::new(PlaceExpr::new(PlaceExprKind::Deref(Box::new(
                    PlaceExpr::new(PlaceExprKind::Proj(
                        Box::new(PlaceExpr::new(PlaceExprKind::Ident(Ident::new("x")))),
                        7
                    ))
                )))))
            )))))
        );
        assert_eq!(
            descend::expression_seq("x.2.3"),
            Ok(Expr::new(ExprKind::PlaceExpr(Box::new(PlaceExpr::new(
                PlaceExprKind::Proj(
                    Box::new(PlaceExpr::new(PlaceExprKind::Proj(
                        Box::new(PlaceExpr::new(PlaceExprKind::Ident(Ident::new("x")))),
                        2
                    ))),
                    3
                )
            )))))
        );
    }

    #[test]
    fn expression_indexing() {
        assert_eq!(
            descend::expression_seq("place_expression[12]"),
            Ok(Expr::new(ExprKind::PlaceExpr(Box::new(PlaceExpr::new(
                PlaceExprKind::Idx(
                    Box::new(PlaceExpr::new(PlaceExprKind::Ident(Ident::new(
                        "place_expression"
                    )))),
                    Box::new(Nat::Lit(12))
                )
            )),)))
        );
    }

    #[test]
    fn expression_assignment() {
        assert_eq!(
            descend::expression_seq("var_token = 7.3e2f32"),
            Ok(Expr::new(ExprKind::Assign(
                Box::new(PlaceExpr::new(PlaceExprKind::Ident(Ident::new(
                    "var_token"
                )))),
                Box::new(Expr::with_type(
                    ExprKind::Lit(Lit::F32(730.0)),
                    Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                        ScalarTy::F32
                    )))))
                ))
            )))
        );
        assert_eq!(
            descend::expression_seq("*var_token = 3 + 4"),
            Ok(Expr::new(ExprKind::Assign(
                Box::new(PlaceExpr::new(PlaceExprKind::Deref(Box::new(
                    PlaceExpr::new(PlaceExprKind::Ident(Ident::new("var_token")))
                )))),
                Box::new(Expr::new(ExprKind::BinOp(
                    BinOp::Add,
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::I32(3)),
                        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                            ScalarTy::I32
                        )))))
                    )),
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::I32(4)),
                        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                            ScalarTy::I32
                        )))))
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
                Box::new(PlaceExpr::new(PlaceExprKind::Ident(Ident::new("variable"))))
            )))
        );
        // assert_eq!(
        //     descend::expression_seq("&'prov uniq var[7]"),
        //     Ok(Expr::new(ExprKind::BorrowIndex(
        //         Some(String::from("'prov")),
        //         Ownership::Uniq,
        //         Box::new(PlaceExpr::new(PlaceExprKind::Ident(Ident::new("var")))),
        //         Nat::Lit(7)
        //     ),))
        // );
        // assert_eq!(
        //     descend::expression_seq("&'prov uniq var[token]"),
        //     Ok(Expr::new(ExprKind::BorrowIndex(
        //         Some(String::from("'prov")),
        //         Ownership::Uniq,
        //         Box::new(PlaceExpr::new(PlaceExprKind::Ident(Ident::new("var")))),
        //         Nat::Ident(Ident::new("token"))
        //     ),))
        // );
        let result = descend::expression_seq("&'a uniq var[7][3]");
        assert!(result.is_ok());
    }

    #[test]
    fn expression_array() {
        assert_eq!(
            descend::expression_seq("[12, x[3], true]"),
            Ok(Expr::new(ExprKind::Array(vec![
                Expr::with_type(
                    ExprKind::Lit(Lit::I32(12)),
                    Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                        ScalarTy::I32
                    )))))
                ),
                Expr::new(ExprKind::PlaceExpr(Box::new(PlaceExpr::new(
                    PlaceExprKind::Idx(
                        Box::new(PlaceExpr::new(PlaceExprKind::Ident(Ident::new("x")))),
                        Box::new(Nat::Lit(3))
                    )
                )))),
                Expr::with_type(
                    ExprKind::Lit(Lit::Bool(true)),
                    Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                        ScalarTy::Bool
                    )))))
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

    // #[test]
    // fn expression_tupel() {
    //     assert_eq!(
    //         descend::expression_seq("(12, x[3], true)"),
    //         Ok(Expr::new(ExprKind::Tuple(vec![
    //             Expr::with_type(
    //                 ExprKind::Lit(Lit::I32(12)),
    //                 Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
    //                     ScalarTy::I32
    //                 )))))
    //             ),
    //             Expr::new(ExprKind::Index(
    //                 Box::new(PlaceExpr::new(PlaceExprKind::Ident(Ident::new("x")))),
    //                 Nat::Lit(3)
    //             )),
    //             Expr::with_type(
    //                 ExprKind::Lit(Lit::Bool(true)),
    //                 Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
    //                     ScalarTy::Bool
    //                 )))))
    //             )
    //         ])))
    //     );
    // }

    #[test]
    fn expression_if_else() {
        macro_rules! common_expr {
            ($binop: expr) => {
                Box::new(Expr::new(ExprKind::BinOp(
                    $binop,
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::I32(7)),
                        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                            ScalarTy::I32,
                        ))))),
                    )),
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::I32(8)),
                        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                            ScalarTy::I32,
                        ))))),
                    )),
                )))
            };
        }
        assert_eq!(
            descend::expression_seq("if 7<8 <>{7+8} else <>{7*8}"),
            Ok(Expr::new(ExprKind::IfElse(
                common_expr!(BinOp::Lt),
                Box::new(Expr::new(ExprKind::Block(Block {
                    prvs: vec![],
                    body: common_expr!(BinOp::Add)
                }))),
                Box::new(Expr::new(ExprKind::Block(Block {
                    prvs: vec![],
                    body: common_expr!(BinOp::Mul)
                }))),
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
                        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                            ScalarTy::I32
                        )))))
                    ),
                    Expr::with_type(
                        ExprKind::Lit(Lit::I32(2)),
                        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                            ScalarTy::I32
                        )))))
                    ),
                    Expr::with_type(
                        ExprKind::Lit(Lit::I32(3)),
                        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                            ScalarTy::I32
                        )))))
                    )
                ]))),
                Box::new(Expr::new(ExprKind::Block(Block::new(Expr::new(
                    ExprKind::Assign(
                        Box::new(PlaceExpr::new(PlaceExprKind::Ident(x.clone()))),
                        Box::new(Expr::new(ExprKind::BinOp(
                            BinOp::Add,
                            Box::new(Expr::new(ExprKind::PlaceExpr(Box::new(PlaceExpr::new(
                                PlaceExprKind::Ident(x.clone())
                            ))))),
                            Box::new(Expr::with_type(
                                ExprKind::Lit(Lit::I32(1)),
                                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                                    ScalarTy::I32
                                )))))
                            ))
                        ),))
                    ),
                )))))
            )))
        )
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
                Some(Box::new(Ty::new(TyKind::Data(Box::new(DataTy::new(
                    DataTyKind::Scalar(ScalarTy::F32)
                )))))),
                Box::new(Expr::with_type(
                    ExprKind::Lit(Lit::F32(17.123)),
                    Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                        ScalarTy::F32
                    )))))
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
                                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                                    ScalarTy::I32
                                )))))
                            ))
                        ))),
                        Box::new(Expr::new(ExprKind::BinOp(
                            BinOp::Mul,
                            Box::new(Expr::with_type(
                                ExprKind::Lit(Lit::I32(2)),
                                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                                    ScalarTy::I32
                                )))))
                            )),
                            Box::new(Expr::with_type(
                                ExprKind::Lit(Lit::I32(3)),
                                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                                    ScalarTy::I32
                                )))))
                            ))
                        )))
                    ))),
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::I32(4)),
                        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                            ScalarTy::I32
                        )))))
                    ))
                ))),
                Box::new(Expr::new(ExprKind::BinOp(
                    BinOp::Mul,
                    Box::new(Expr::new(ExprKind::BinOp(
                        BinOp::Mul,
                        Box::new(Expr::with_type(
                            ExprKind::Lit(Lit::I32(5)),
                            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                                ScalarTy::I32
                            )))))
                        )),
                        Box::new(Expr::with_type(
                            ExprKind::Lit(Lit::I32(6)),
                            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                                ScalarTy::I32
                            )))))
                        ))
                    ))),
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::I32(7)),
                        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                            ScalarTy::I32
                        )))))
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
                            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                                ScalarTy::I32
                            )))))
                        )),
                        Box::new(Expr::with_type(
                            ExprKind::Lit(Lit::I32(2)),
                            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                                ScalarTy::I32
                            )))))
                        ))
                    ),))
                ),)),
                Box::new(Expr::new(ExprKind::BinOp(
                    BinOp::Mul,
                    Box::new(Expr::new(ExprKind::BinOp(
                        BinOp::Add,
                        Box::new(Expr::with_type(
                            ExprKind::Lit(Lit::I32(3)),
                            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                                ScalarTy::I32
                            )))))
                        )),
                        Box::new(Expr::new(ExprKind::BinOp(
                            BinOp::Mul,
                            Box::new(Expr::new(ExprKind::BinOp(
                                BinOp::Add,
                                Box::new(Expr::with_type(
                                    ExprKind::Lit(Lit::I32(4)),
                                    Ty::new(TyKind::Data(Box::new(DataTy::new(
                                        DataTyKind::Scalar(ScalarTy::I32)
                                    ))))
                                )),
                                Box::new(Expr::with_type(
                                    ExprKind::Lit(Lit::I32(5)),
                                    Ty::new(TyKind::Data(Box::new(DataTy::new(
                                        DataTyKind::Scalar(ScalarTy::I32)
                                    ))))
                                ))
                            ))),
                            Box::new(Expr::with_type(
                                ExprKind::Lit(Lit::I32(6)),
                                Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                                    ScalarTy::I32
                                )))))
                            ))
                        )))
                    ))),
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::I32(7)),
                        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                            ScalarTy::I32
                        )))))
                    ))
                )))
            ),))
        );
    }

    #[test]
    fn global_fun_def_all_function_kinds() {
        // all currently available kinds are tested
        let src = r#"fn test_kinds<n: nat, a: prv, d: dty, m: mem>(
            ha_array: &a uniq cpu.mem [i32; n]
        ) -[ex: cpu.thread]-> () <>{
            42
        }"#;
        let body = r#"42"#;

        let result = descend::global_fun_def(src).expect("Parsing failed");

        let generic_params = vec![
            IdentKinded::new(&Ident::new("n"), Kind::Nat),
            IdentKinded::new(&Ident::new("a"), Kind::Provenance),
            IdentKinded::new(&Ident::new("d"), Kind::DataTy),
            IdentKinded::new(&Ident::new("m"), Kind::Memory),
        ];
        let params = vec![ParamDecl {
            ident: Ident::new("ha_array"),
            ty: Some(Ty::new(TyKind::Data(Box::new(DataTy::new(
                DataTyKind::Ref(Box::new(RefDty::new(
                    Provenance::Ident(Ident::new("a")),
                    Ownership::Uniq,
                    Memory::CpuMem,
                    DataTy::new(DataTyKind::Array(
                        Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::I32))),
                        Nat::Ident(Ident::new("n")),
                    )),
                ))),
            ))))),
            mutbl: Mutability::Const,
        }];
        let ret_dty = DataTy::new(DataTyKind::Scalar(ScalarTy::Unit));
        let exec = IdentExec::new(Ident::new("ex"), ExecTy::new(ExecTyKind::CpuThread));
        let prv_rels = vec![];

        let intended = FunDef {
            ident: Ident::new("test_kinds"),
            param_decls: params,
            exec_decl: exec,
            prv_rels,
            body: Box::new(Block::new(descend::expression(body).unwrap())),
            generic_params,
            ret_dty,
        };

        assert_eq!(result.ident, intended.ident);
        assert_eq!(result.param_decls, intended.param_decls);
        assert_eq!(result.exec_decl, intended.exec_decl);
        assert_eq!(result.prv_rels, intended.prv_rels);
        assert_eq!(result.body, intended.body);
        assert_eq!(result.generic_params, intended.generic_params);
        assert_eq!(result.ret_dty, intended.ret_dty);
        assert_eq!(result, intended);
    }

    #[test]
    fn global_fun_def_kind_parameters_optional() {
        // test both versions with and without <> pointy brackets
        let src_1 = r#"fn no_kinds(
            ha_array: &'a uniq cpu.mem [i32; n],
            hb_array: &'b shrd cpu.mem [i32; n]
        ) -[t: cpu.thread]-> () <>{
            let answer_to_everything :i32 = 42;
            answer_to_everything
        }"#;
        let src_2 = r#"fn no_kinds<>(
            ha_array: &'a uniq cpu.mem [i32; n],
            hb_array: &'b shrd cpu.mem [i32; n]
        ) -[t: cpu.thread]-> () <>{
            let answer_to_everything :i32 = 42;
            answer_to_everything
        }"#;

        let result_1 = descend::global_fun_def(src_1);
        let result_2 = descend::global_fun_def(src_2);

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
        ) -[t: cpu.thread]-> () {
            let answer_to_everything :i32 = 42;
            answer_to_everything
        }"#;

        let result = descend::global_fun_def(src);

        assert!(result.is_err());
    }

    #[test]
    fn global_fun_def_no_function_parameters_required() {
        let src = r#"fn no_params<n: nat, a: prv, b: prv>() -[t: cpu.thread]-> () <>{            
            let answer_to_everything :i32 = 42;
            answer_to_everything
        }"#;

        let result = descend::global_fun_def(src);
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
                        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                            ScalarTy::I32
                        )))))
                    )),
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::I32(2)),
                        Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                            ScalarTy::I32
                        )))))
                    ))
                ))),
                Box::new(Expr::new(ExprKind::Block(Block::new(Expr::new(
                    ExprKind::Let(
                        Pattern::Ident(Mutability::Const, Ident::new("x")),
                        None,
                        Box::new(Expr::with_type(
                            ExprKind::Lit(Lit::I32(5)),
                            Ty::new(TyKind::Data(Box::new(DataTy::new(DataTyKind::Scalar(
                                ScalarTy::I32
                            )))))
                        ))
                    )
                )))))
            )))
        )
    }

    #[test]
    fn compil_unit_test_one() {
        let src = r#"
        
        fn foo() -[t: cpu.thread]-> () <>{
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
        
        fn foo() -[t: cpu.thread]-> () <>{
            42
        }

        fn bar() -[t: cpu.thread]-> () <>{
            24
        }


        fn baz() -[t: cpu.thread]-> () <>{
            1337
        }
        
        "#;
        let result = descend::compil_unit(src)
            .expect("Cannot parse compilation unit with multiple functions");
        assert_eq!(result.len(), 3);
    }
}
