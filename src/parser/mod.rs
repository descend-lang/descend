//! Module for components related to parsing

mod helpers;
mod source;
use peg::{error::ParseError, str::LineCol};
pub use source::*;

use crate::ast::ty::{Nat, Ty, ScalarData, ExecLoc, Memory, Provenance, Kind, GlobalFunDef, FrameExpr, IdentKinded, KindedArg};
use crate::ty_check::ty_ctx::IdentTyped;
use crate::ast::{Ownership, Mutability, Ident, Lit, PlaceExpr, Expr, ExprKind, BinOp, UnOp, Span};

use crate::dsl::fun_ty;

pub fn parse_global_fun_def(src: &str) -> Result<GlobalFunDef, ParseError<LineCol>> {
    descend::global_fun_def(src)
}

peg::parser!{
    pub(crate) grammar descend() for str {

        // TODO: PreDeclaredGlobalFun missing Syntax
        pub(crate) rule global_fun_def() -> GlobalFunDef
            = "fn" __ name:identifier() _ ty_idents:("<" _ t:(kind_parameter() ** (_ "," _)) _ ">" {t})? _
            "(" _ params:(fun_parameter() ** (_ "," _)) _ ")" _
            "-[" _ exec:execution_location() _ "]->" _ ret_ty:ty() _
            "{" _ body_expr:expression_seq() _"}" {
                // TODO: Kick this out of the AST?
                let mut f_ty = fun_ty(
                    params
                        .iter()
                        .map(|ident| -> Ty { ident.ty.clone() })
                        .collect(),
                    &FrameExpr::FrTy(vec![]),
                    exec,
                    &ret_ty,
                );
                let ty_idents = match ty_idents {
                    Some(ty_idents) => ty_idents,
                    None => vec![]
                };
                GlobalFunDef {
                  name,
                  ty_idents,
                  params,
                  ret_ty,
                  exec,
                  prv_rels: vec![], // TODO: What even is this?
                  body_expr,
                  fun_ty: f_ty
                }
            }

        rule kind_parameter() -> IdentKinded
            = name:ident() _ ":" _ kind:kind() {
                IdentKinded::new(&name, kind)
            }

        rule fun_parameter() -> IdentTyped
            = ident:ident() _ ":" _ ty:ty() {
                IdentTyped { ident, ty }
            }

        /// Parse a sequence of expressions (might also just be one)
        pub(crate) rule expression_seq() -> Expr
            = start:position!() head:expression() _ ";" _ tail:expression_seq()? end:position!() {
                match tail{
                    None => head,
                    Some(tail) => {
                        let tail_ty = tail.ty.clone();
                        Expr {
                            expr: ExprKind::Seq(Box::new(head), Box::new(tail)),
                            ty: tail_ty,
                            span: Some(Span::new(start, end))
                        }
                    }
                }
            }
            / start:position!() "let" __ m:(m:mutability() __ {m})? ident:ident() _ ":" _ ty:ty() _ "=" _ expr:expression() _ ";" _
                tail:expression_seq() end:position!()
            {
                let tail_ty = tail.ty.clone();
                Expr {
                    expr:ExprKind::Let(m.unwrap_or(Mutability::Const), ident, ty, Box::new(expr), Box::new(tail)),
                    ty: tail_ty,
                    span: Some(Span::new(start, end))
                }
            }
            / expr:expression() { expr }

        /// Parse an expression
        pub(crate) rule expression() -> Expr = precedence!{
            x:(@) _ "&&" _ y:@ { helpers::make_binary(BinOp::And, x, y) }
            x:(@) _ "||" _ y:@ { helpers::make_binary(BinOp::Or, x, y) }
            --
            x:(@) _ "==" _ y:@ { helpers::make_binary(BinOp::Eq, x, y) }
            x:(@) _ "!=" _ y:@ { helpers::make_binary(BinOp::Neq, x, y) }
            x:(@) _ "<" _ y:@ { helpers::make_binary(BinOp::Lt, x, y) }
            x:(@) _ "<=" _ y:@ { helpers::make_binary(BinOp::Le, x, y) }
            x:(@) _ ">" _ y:@ { helpers::make_binary(BinOp::Gt, x, y) }
            x:(@) _ ">=" _ y:@ { helpers::make_binary(BinOp::Ge, x, y) }
            --
            x:(@) _ "+" _ y:@ { helpers::make_binary(BinOp::Add, x, y) }
            x:(@) _ "-" _ y:@ { helpers::make_binary(BinOp::Sub, x, y) }
            --
            x:(@) _ "*" _ y:@ { helpers::make_binary(BinOp::Mul, x, y) }
            x:(@) _ "/" _ y:@ { helpers::make_binary(BinOp::Div, x, y) }
            x:(@) _ "%" _ y:@ { helpers::make_binary(BinOp::Mod, x, y) }
            --
            "-" _ x:(@) { helpers::make_unary(UnOp::Neg, x) }
            "!" _ x:(@) { helpers::make_unary(UnOp::Not, x) }
            --
            start:position!() expr:@ end:position!() {
                let expr: Expr = Expr {
                    span: Some(Span::new(start, end)),
                    ..expr
                };
                expr
            }
            // TODO: Integrate this properly into the precedence parser (irrelevant for now
            // since there are no lambda functions yet)
            start:position!() func:place_expression() place_end:position!() _ 
                kind_args:("<" _ k:kind_argument() ** (_ "," _) _ ">" _ { k })? 
                "(" _ args:expression() ** (_ "," _) _ ")" end:position!() 
            {
                helpers::make_function_application(
                    Expr::with_span(
                        ExprKind::PlaceExpr(func),
                        Span::new(start, place_end)
                    ),
                    kind_args, args, Span::new(start, end))
            }
            l:literal() {
                // Do not use a let statement here. It makes rust-peg angry
                Expr::with_type(
                    ExprKind::Lit(l.clone()),
                    helpers::type_from_lit(&l)
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
                        Some(_) => unimplemented!() // TODO: Implement array assignment
                    }
                }
            }
            "&" _ prov:provenance() __ own:ownership() __ p:place_expression() idx:(_ "[" _ n:nat() _ "]" {n})? {
                match idx {
                    None => Expr::new(ExprKind::Ref(prov, own, p)),
                    Some(idx) => Expr::new(ExprKind::BorrowIndex(prov, own, p,idx))
                }
            }
            "[" _ expressions:expression() ** (_ "," _) _ "]" {
                Expr::new(ExprKind::Array(expressions))
            }
            "(" _ expression:expression() _ "," _ ")" {
                Expr::new(ExprKind::Tuple(vec![expression]))
            }
            "(" _ expressions:expression() **<2,> (_ "," _) _ ")" {
                Expr::new(ExprKind::Tuple(expressions))
            }
            "if" _ cond:expression() _ "{" _ iftrue:expression_seq() _ "}" _ "else" _ "{" _ iffalse:expression_seq() _ "}" {
                Expr::new(
                    ExprKind::IfElse(Box::new(cond), Box::new(iftrue), Box::new(iffalse))
                )
            }
            "letprov" _ "<" _ identifier() ** (_ "," _)  _ ">" _
                "{" _ body:expression_seq() _ "}"
            {
                // TODO: ast structure for letprov? Return body for now
                body
            }
            sync_threads:("sync_threads" _ "[" _ gpu_expr:expression() _ ";" _ threads:nat() _ "]" _ {(gpu_expr, threads)})?
                "for" __ ident:ident() __ "in" _ collection:expression() _ "{" _ body:expression_seq() _ "}"
            {
                match sync_threads {
                    None => Expr::new(ExprKind::For(ident, Box::new(collection), Box::new(body))),
                    Some((gpu_expr, threads)) => Expr::new(
                        ExprKind::ParForGlobalSync(
                            Box::new(gpu_expr), threads,
                            ident, Box::new(collection), Box::new(body)),
                    )
                }
            }
            // Parentheses to override precedence
            "(" _ expression:expression() _ ")" { expression }
        } 

        /// Parse a kind argument
        pub(crate) rule kind_argument() -> KindedArg
            = o:ownership() { KindedArg::Own(o) }
            / !identifier() result:(
                n:nat() { KindedArg::Nat(n) }
                / mem:memory_kind() { KindedArg::Memory(mem) }
                / ty:ty() { KindedArg::Ty(ty) }
                / prov:provenance() { KindedArg::Provenance(prov) }
            ) { result }
            / ident:ident() { KindedArg::Ident(ident)}

        /// Place expression
        pub(crate) rule place_expression() -> PlaceExpr
            = derefs:("*" _)* name:ident() _ ns:("." _ n:nat() _ {n})* {
                let root = PlaceExpr::Var(name);
                // . operator binds stronger
                let proj = ns.into_iter().fold(root, |prev,n| PlaceExpr::Proj(Box::new(prev), n));
                // * operator binds weaker
                derefs.iter().fold(proj, |prev,_| PlaceExpr::Deref(Box::new(prev)))
                // TODO: Allow parentheses for priority override?
            }

        /// Parse nat token
        pub(crate) rule nat() -> Nat 
            = s:$("0" / (['1'..='9']['0'..='9']*)) { ?
                // TODO: Getting the cause of the parse error is unstable for now. Fix this once 
                // int_error_matching becomes stable
                match s.parse::<usize>() {
                    Ok(val) => Ok(Nat::Lit(val)),
                    Err(_) => { Err("Cannot parse natural number") }
                }
            }
            / name:ident() {
                Nat::Ident(name)
            }
            // TODO: binary operations are currently disabled
            // TODO: Add 0b, 0o and 0x prefixes for binary, octal and hexadecimal?

        /// Parse a type token
        pub(crate) rule ty() -> Ty
            = first:ty_term() _ mems:("@" _ mem:memory_kind() _ {mem})* {
                mems.into_iter().fold(first, |prev,mem| Ty::At(Box::new(prev), mem))
            }

        /// Helper for "type @ memory" left-recursion
        rule ty_term() -> Ty
            = "f32" { Ty::Scalar(ScalarData::F32) }
            / "i32" { Ty::Scalar(ScalarData::I32) }
            / "bool" { Ty::Scalar(ScalarData::Bool) }
            / "()" { Ty::Scalar(ScalarData::Unit) }
            / "GPU" { Ty::GPU }
            / name:ident() { Ty::Ident(name) }
            / "(" _ types:ty() ** ( _ "," _ ) _ ")" { Ty::Tuple(types) }
            / "[" _ t:ty() _ ";" _ n:nat() _ "]" { Ty::Array(Box::new(t), n) }
            / "[[" _ t:ty() _ ";" _ n:nat() _ "]]" { Ty::ArrayView(Box::new(t), n) }
            / "&" _ prov:provenance() _ own:ownership() _ mem:memory_kind() _ ty:ty() {
                Ty::Ref(prov, own, mem, Box::new(ty))
            }

        pub(crate) rule ownership() -> Ownership
        = "shrd" { Ownership::Shrd }
        / "uniq" { Ownership::Uniq }

        pub(crate) rule mutability() -> Mutability
        = "const" { Mutability::Const }
        / "mut" { Mutability::Mut }

        pub(crate) rule memory_kind() -> Memory
            = "cpu.stack" { Memory::CpuStack }
            / "cpu.heap" { Memory::CpuHeap }
            / "gpu.global" { Memory::GpuGlobal }
            / "gpu.shared" { Memory::GpuShared }
            / name:ident() { Memory::Ident(name) }

        pub(crate) rule execution_location() -> ExecLoc
            = "cpu.thread" { ExecLoc::CpuThread }
            / "gpu.group" { ExecLoc::GpuGroup }
            / "gpu.thread" { ExecLoc::GpuThread }

        pub(crate) rule kind() -> Kind
            = "nat" { Kind::Nat }
            / "mem" { Kind::Memory }
            / "ty" { Kind::Ty }
            / "prv" { Kind::Provenance }
            / "frm" { Kind::Frame }
            /// "own" { } // TODO: Unimplemented in AST

        rule ident() -> Ident
            = start:position!() ident:$(identifier()) end:position!() {
                Ident::with_span(ident.into(), Span::new(start, end))
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
            = (("crate" / "super" / "self" / "Self" / "const" / "mut" / "uniq" / "shrd"
                / "f32" / "i32" / "bool" / "GPU" / "nat" / "mem" / "ty" / "prv" / "frm" / "own"
                / "let"("prov")? / "if" / "else" / "for" / "in" / "sync_threads" / "fn")
                !['a'..='z'|'A'..='Z'|'0'..='9'|'_']
            )
            / "cpu.stack" / "cpu.heap" / "gpu.global" / "gpu.shared"
            / "cpu.thread" / "gpu.group" / "gpu.thread"
        
        // Literal may be one of Unit, bool, i32, f32
        pub(crate) rule literal() -> Lit
            = &"()" {
                Lit::Unit
            }
            / l:$("true" / "false") { ?
                match l.parse::<bool>() {
                    Ok(b) => Ok(Lit::Bool(b)),
                    Err(_) => Err("Error while parsing boolean literal")
                }
            }
            / l:$( ("-"? ((['1'..='9']['0'..='9']*) / "0") "." ['0'..='9']*)  (['e'|'E'] "-"?  ['0'..='9']*)? "f32"? ) { ?
                let literal = if (l.ends_with("f32")) {&l[0..l.len()-3]} else {l};
                match literal.parse::<f32>() {
                    Ok(val) => Ok(Lit::Float(val)),
                    Err(_) => Err("Error while parsing f32 literal")
                }
            }
            / l:$((("-"? ['1'..='9']['0'..='9']*) / "0") ("i32" / "f32")?  ) { ?
                let literal = if (l.ends_with("i32") || l.ends_with("f32")) {&l[0..l.len()-3]} else {l};
                if (l.ends_with("f32")) {
                    match literal.parse::<f32>() {
                        Ok(val) => Ok(Lit::Float(val)),
                        Err(_) => Err("Error while parsing f32 literal")
                    }
                }
                else {
                    match literal.parse::<i32>() {
                        Ok(val) => Ok(Lit::Int(val)),
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
        assert!(descend::nat("100000000000000000000").is_err(), "overflow not handled");
        assert!(descend::nat("-1").is_err(), "negative numbers not handled");
        assert!(descend::nat("3abc").is_err(), "garbage not handled");
        assert!(descend::nat("").is_err(), "matches empty");
    }

    #[test]
    #[ignore = "Unimplemented"]
    fn nat_identifier() {
        assert_eq!(descend::nat("N"), Ok(Nat::Ident(Ident::new("N"))), "cannot parse N");
        assert_eq!(descend::nat("my_long_ident"), Ok(Nat::Ident(Ident::new("my_long_ident"))),
            "cannot parse long identifer");
    }

    #[test]
    #[ignore = "Unimplemented"]
    fn nat_binary_operation() {
        todo!()
    }

    #[test]
    fn ty_scalar() {
        assert_eq!(descend::ty("f32"), Ok(Ty::Scalar(ScalarData::F32)), 
            "does not recognize f32 type");
        assert_eq!(descend::ty("i32"), Ok(Ty::Scalar(ScalarData::I32)), 
            "does not recognize i32 type");
        assert_eq!(descend::ty("()"), Ok(Ty::Scalar(ScalarData::Unit)), 
            "does not recognize unit type");
        assert_eq!(descend::ty("bool"), Ok(Ty::Scalar(ScalarData::Bool)), 
            "does not recognize Boolean type");
    }

    #[test]
    fn ty_gpu() {
        assert_eq!(descend::ty("GPU"), Ok(Ty::GPU), 
            "does not recognize GPU type");
    }

    #[test]
    fn ty_tuple() {
        let ty_f32 = Ty::Scalar(ScalarData::F32);
        let ty_i32 = Ty::Scalar(ScalarData::I32);
        let ty_unit = Ty::Scalar(ScalarData::Unit);
        assert_eq!(descend::ty("(f32)"), Ok(Ty::Tuple(vec![ty_f32])), 
            "does not recognize (f32) tuple type");
        assert_eq!(descend::ty("(i32,i32)"), Ok(Ty::Tuple(vec![ty_i32.clone(), ty_i32])), 
            "does not recognize (i32) tuple type");
        assert_eq!(descend::ty("((),(),())"), Ok(Ty::Tuple(vec![
            ty_unit.clone(), ty_unit.clone(), ty_unit.clone()])), 
            "does not recognize (unit,unit,unit) tuple type");
    }

    #[test]
    fn ty_array_view() {
        assert_eq!(descend::ty("[f32;42]"), Ok(Ty::Array(Box::new(
            Ty::Scalar(ScalarData::F32)),
            Nat::Lit(42)
        )), "does not recognize [f32;42] type");
        // TODO: Implement identifer parsing in nat
        // assert_eq!(descend::ty("[();N]"), Ok(Ty::Array(Box::new(
        //     Ty::Scalar(ScalarData::Unit)),
        //     Nat::Ident(Nat::new_ident("N")))
        // ), "does not recognize [();N] type");
        assert_eq!(descend::ty("[[i32;24]]"), Ok(Ty::ArrayView(Box::new(
            Ty::Scalar(ScalarData::I32)),
            Nat::Lit(24)
        )), "does not recognize [[f32;24]] type");
    }

    #[test]
    fn ty_identifier() {
        assert_eq!(descend::ty("T"), Ok(Ty::Ident(Ident::new("T"))), 
            "does not recognize T type");
    }

    #[test]
    fn ty_reference() {
        assert_eq!(descend::ty("&'a uniq cpu.heap i32"), Ok(Ty::Ref(
                Provenance::Value("'a".into()),
                Ownership::Uniq,
                Memory::CpuHeap,
                Box::new(Ty::Scalar(ScalarData::I32))
            )), "does not recognize type of unique i32 reference in cpu heap with provenance 'a");
        assert_eq!(descend::ty("&b shrd gpu.global [f32;N]"), Ok(Ty::Ref(
                Provenance::Ident(Ident::new("b")),
                Ownership::Shrd,
                Memory::GpuGlobal,
                Box::new(Ty::Array(
                    Box::new(Ty::Scalar(ScalarData::F32)),
                    Nat::Ident(Ident::new("N"))
                ))
            )), "does not recognize type of shared [f32] reference in gpu global memory with provenance b");
    }

    #[test]
    fn ty_memory_kind() {
        assert_eq!(descend::ty("i32 @ cpu.stack"), Ok(Ty::At(
            Box::new(Ty::Scalar(ScalarData::I32)),
            Memory::CpuStack
        )), "does not recognize f32 @ cpu.stack type");
        assert_eq!(descend::ty("[f32;42] @ gpu.global"), Ok(Ty::At(
            Box::new(Ty::Array(Box::new(Ty::Scalar(ScalarData::F32)), Nat::Lit(42))),
            Memory::GpuGlobal
        )), "does not recognize [f32;42] @ gpu.global type");
    }

    #[test]
    fn ownership() {
        assert_eq!(descend::ownership("shrd"), Ok(Ownership::Shrd), 
            "does not recognize shrd ownership qualifier");
        assert_eq!(descend::ownership("uniq"), Ok(Ownership::Uniq), 
            "does not recognize uniq ownership qualifier");
    }

    #[test]
    #[ignore = "Mutability does not implement Eq"]
    fn mutability() {
        // TODO: Missing Eq implementation in AST
        // assert_eq!(descend::mutability("const"), Ok(Mutability::Const), 
        //     "does not recognize const mutability qualifier");
        // assert_eq!(descend::mutability("mut"), Ok(Mutability::Mut), 
        //     "does not recognize mut mutability qualifier");
    }

    #[test]
    fn memory_kind() {
        assert_eq!(descend::memory_kind("cpu.stack"), Ok(Memory::CpuStack), 
            "does not recognize cpu.stack memory kind");
        assert_eq!(descend::memory_kind("cpu.heap"), Ok(Memory::CpuHeap), 
            "does not recognize cpu.heap memory kind");
        assert_eq!(descend::memory_kind("gpu.global"), Ok(Memory::GpuGlobal), 
            "does not recognize gpu.global memory kind");
        assert_eq!(descend::memory_kind("gpu.shared"), Ok(Memory::GpuShared), 
            "does not recognize gpu.shared memory kind");
        assert_eq!(descend::memory_kind("M"), Ok(Memory::Ident(Ident::new("M"))), 
            "does not recognize M memory kind");
    }

    #[test]
    fn execution_location() {
        assert_eq!(descend::execution_location("cpu.thread"), Ok(ExecLoc::CpuThread), 
            "does not recognize cpu.stack memory kind");
        assert_eq!(descend::execution_location("gpu.group"), Ok(ExecLoc::GpuGroup), 
            "does not recognize cpu.heap memory kind");
        assert_eq!(descend::execution_location("gpu.thread"), Ok(ExecLoc::GpuThread), 
            "does not recognize gpu.global memory kind");
    }

    #[test]
    fn literal() {
        assert_eq!(descend::literal("true"), Ok(Lit::Bool(true)), "does not parse boolean correctly");
        assert_eq!(descend::literal("False").is_err(), true, "wrongfully parses misspelled boolean");
        assert_eq!(descend::literal("12345"), Ok(Lit::Int(12345)), "does not parse i32 correctly");
        assert_eq!(descend::literal("789i32"), Ok(Lit::Int(789)), "does not parse i32 correctly");
        assert_eq!(descend::literal("-1i32"), Ok(Lit::Int(-1)), "does not correctly parse 1e05i32 to i32");
        assert_eq!(descend::literal("1f32"), Ok(Lit::Float(1.)), "does not correctly parse 1f32 to f32");
        // TODO: Do proper float comparison (test error against threshold)
        assert_eq!(descend::literal("1.0"), Ok(Lit::Float(1.0)), "does not parse f32 correctly");
        assert_eq!(descend::literal("2.0f32"), Ok(Lit::Float(2.0)), "does not parse f32 correctly");
        assert_eq!(descend::literal("777.7e0f32"), Ok(Lit::Float(777.7)), "does not parse f32 correctly");
        assert_eq!(descend::literal("777.7e01f32"), Ok(Lit::Float(7777.0)), "does not parse f32 correctly");
        assert_eq!(descend::literal("1.0e2"), Ok(Lit::Float(100.0)), "does not parse f32 in scientific notation correctly");
        assert_eq!(descend::literal("1.0e-2"), Ok(Lit::Float(0.01)), "does not parse f32 in scientific notation correctly");
        assert_eq!(descend::literal("3.7f32"), Ok(Lit::Float(3.7)), "does not parse f32 correctly");
        assert_eq!(descend::literal("3.75e3"), Ok(Lit::Float(3750.0)), "does not parse scientific notation f32 correctly");
        assert_eq!(descend::literal("-1234.5e-0005"), Ok(Lit::Float(-0.012345)), "does not parse negative scientific notation f32 correctly");
        assert_eq!(descend::literal("3.14159265358979323846264338327950288"), // std::f64::consts::PI
                                    Ok(Lit::Float(3.1415927)), "not parsing f32 float as expected");
        assert_eq!(descend::literal("12345ad").is_err(), true, "incorrectly parsing invalid literal");
        assert_eq!(descend::literal("e54").is_err(), true, "incorrectly parsing e-notation only to literal");
        assert_eq!(descend::literal("-i32").is_err(), true, "incorrectly parsing 'negative data type' to literal");
    }

    #[test]
    fn kind() {
        assert_eq!(descend::kind("nat"), Ok(Kind::Nat), 
            "does not recognize nat kind");
        assert_eq!(descend::kind("mem"), Ok(Kind::Memory), 
            "does not recognize mem kind");
        assert_eq!(descend::kind("ty"), Ok(Kind::Ty), 
            "does not recognize ty kind");
        assert_eq!(descend::kind("prv"), Ok(Kind::Provenance), 
            "does not recognize prv kind");
        assert_eq!(descend::kind("frm"), Ok(Kind::Frame), 
            "does not recognize frm kind");
    }

    #[test]
    fn place_expression() {
        assert_eq!(descend::place_expression("*x"), Ok(
            PlaceExpr::Deref(Box::new(
                PlaceExpr::Var(Ident::new("x"))
            ))), "does not recognize place expression *x");
        assert_eq!(descend::place_expression("x.0"), Ok(
            PlaceExpr::Proj(
                Box::new(PlaceExpr::Var(Ident::new("x"))),
                Nat::Lit(0)
            )), "does not recognize place expression *x");
        assert_eq!(descend::place_expression("*x.0"), Ok(
            PlaceExpr::Deref(Box::new(
                PlaceExpr::Proj(
                    Box::new(PlaceExpr::Var(Ident::new("x"))),
                    Nat::Lit(0)
            )))), "does not recognize place expression *x.0");
    }
    
    #[test]
    fn expression_literal() {
        assert_eq!(descend::expression("7"), Ok(Expr::with_type(
            ExprKind::Lit(Lit::Int(7)),
            Ty::Scalar(ScalarData::I32)
        )));
        dbg!(descend::expression("7").unwrap());
    }

    #[test]
    fn expression_addition() {
        assert_eq!(descend::expression("7+8"), Ok(Expr::new(
            ExprKind::Binary(
                BinOp::Add,
                Box::new(Expr::with_type(
                    ExprKind::Lit(Lit::Int(7)),
                    Ty::Scalar(ScalarData::I32)
                )),
                Box::new(Expr::with_type(
                    ExprKind::Lit(Lit::Int(8)),
                    Ty::Scalar(ScalarData::I32)
                ))),
        )));
    }

    #[test]
    fn expression_parenthesis() {
        assert_eq!(descend::expression_seq("(5+6) * 7"), Ok(Expr::new(
            ExprKind::Binary(
                BinOp::Mul,
                Box::new(Expr::new(ExprKind::Binary(
                    BinOp::Add, 
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::Int(5)),
                        Ty::Scalar(ScalarData::I32)
                    )),
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::Int(6)),
                        Ty::Scalar(ScalarData::I32)
                    ))),
                )),
                Box::new(Expr::with_type(
                    ExprKind::Lit(Lit::Int(7)),
                    Ty::Scalar(ScalarData::I32)
                ))),
        )));
    }

    #[test]
    fn expression_place_expr() {
        assert_eq!(descend::expression_seq("someIdentifier"), Ok(Expr::new(
            ExprKind::PlaceExpr(PlaceExpr::Var(Ident::new("someIdentifier")))
        )));
        assert_eq!(descend::expression_seq("*x"), Ok(Expr::new(
            ExprKind::PlaceExpr(
                PlaceExpr::Deref(
                    Box::new(PlaceExpr::Var(Ident::new("x"))))),
        )));
        assert_eq!(descend::expression_seq("**x.7"), Ok(Expr::new(
            ExprKind::PlaceExpr(
                PlaceExpr::Deref(
                    Box::new(PlaceExpr::Deref(
                        Box::new(PlaceExpr::Proj(
                            Box::new(PlaceExpr::Var(Ident::new("x"))),
                            Nat::Lit(7)
            )))))),
        )));
        assert_eq!(descend::expression_seq("x.2.3"), Ok(Expr::new(
            ExprKind::PlaceExpr(
                PlaceExpr::Proj(
                    Box::new(PlaceExpr::Proj(
                        Box::new(PlaceExpr::Var(Ident::new("x"))),
                        Nat::Lit(2))),
                    Nat::Lit(3)
            )),
        )));
    }

    #[test]
    fn expression_indexing() {
        assert_eq!(descend::expression_seq("place_expression[12]"), Ok(Expr::new(
            ExprKind::Index(
                PlaceExpr::Var(Ident::new("place_expression")),
                Nat::Lit(12))
        )));
    }

    #[test]
    fn expression_assignment() {
        assert_eq!(descend::expression_seq("var_token = 7.3e2"), Ok(Expr::new(
            ExprKind::Assign(
                PlaceExpr::Var(Ident::new("var_token")),
                Box::new(Expr::with_type(
                    ExprKind::Lit(Lit::Float(730.0)),
                    Ty::Scalar(ScalarData::F32)
            )))
        )));
        assert_eq!(descend::expression_seq("*var_token = 3 + 4"), Ok(Expr::new(
            ExprKind::Assign(
                PlaceExpr::Deref(
                    Box::new(PlaceExpr::Var(Ident::new("var_token")))
                ), 
                Box::new(Expr::new(ExprKind::Binary(
                    BinOp::Add,
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::Int(3)),
                        Ty::Scalar(ScalarData::I32)
                    )),
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::Int(4)),
                        Ty::Scalar(ScalarData::I32)
                )))
            )))
        )));
    }

    #[test]
    fn expression_references() {
        assert_eq!(descend::expression_seq("&'prov uniq variable"), Ok(Expr::new(
            ExprKind::Ref(
                Provenance::Value(String::from("'prov")),
                Ownership::Uniq,
                PlaceExpr::Var(Ident::new("variable"))),
        )));
        assert_eq!(descend::expression_seq("&prov_var shrd variable"), Ok(Expr::new(
            ExprKind::Ref(
                Provenance::Ident(Ident::new("prov_var")),
                Ownership::Shrd,
                PlaceExpr::Var(Ident::new("variable"))),
        )));
        assert_eq!(descend::expression_seq("&'prov uniq var[7]"), Ok(Expr::new(
            ExprKind::BorrowIndex(
                Provenance::Value(String::from("'prov")), 
                Ownership::Uniq,
                PlaceExpr::Var(Ident::new("var")),
                Nat::Lit(7)),
        )));
        assert_eq!(descend::expression_seq("&'prov uniq var[token]"), Ok(Expr::new(
            ExprKind::BorrowIndex(
                Provenance::Value(String::from("'prov")),
                Ownership::Uniq,
                PlaceExpr::Var(Ident::new("var")),
                Nat::Ident(Ident::new("token"))),
        )));
        let result = descend::expression_seq("&'a uniq var[7][3]");
        assert!(result.is_err());
    }

    #[test]
    fn expression_array() {
        assert_eq!(descend::expression_seq("[12, x[3], true]"), Ok(Expr::new(
            ExprKind::Array(vec![
                Expr::with_type(
                    ExprKind::Lit(Lit::Int(12)),
                    Ty::Scalar(ScalarData::I32)
                ),
                Expr::new(
                    ExprKind::Index(
                        PlaceExpr::Var(Ident::new("x")),
                        Nat::Lit(3)
                    )
                ),
                Expr::with_type(
                    ExprKind::Lit(Lit::Bool(true)),
                    Ty::Scalar(ScalarData::Bool)
                )
            ])
        )));
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
        assert_eq!(descend::expression_seq("(12, x[3], true)"), Ok(Expr::new(
            ExprKind::Tuple(vec![
                Expr::with_type(
                    ExprKind::Lit(Lit::Int(12)),
                    Ty::Scalar(ScalarData::I32)
                ),
                Expr::new(
                    ExprKind::Index(
                        PlaceExpr::Var(Ident::new("x")),
                        Nat::Lit(3)
                    )
                ),
                Expr::with_type(
                    ExprKind::Lit(Lit::Bool(true)),
                    Ty::Scalar(ScalarData::Bool)
                )
            ])
        )));
    }

    #[test]
    fn expression_if_else() {
        macro_rules! common_expr {
            ($binop: expr) => {
                Box::new(Expr::new(ExprKind::Binary(
                    $binop, 
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::Int(7)),
                        Ty::Scalar(ScalarData::I32)
                    )),
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::Int(8)),
                        Ty::Scalar(ScalarData::I32)
                    ))
                )))
            }
        };
        assert_eq!(descend::expression_seq("if 7<8 {7+8} else {7*8}"), Ok(Expr::new(
            ExprKind::IfElse(
                common_expr!(BinOp::Lt),
                common_expr!(BinOp::Add),
                common_expr!(BinOp::Mul),
        ))));
    }

    #[test]
    fn expression_for_loop() {
        let x = Ident::new("x");
        assert_eq!(descend::expression_seq("for x in [1,2,3] {x = x+1}"), Ok(Expr::new(
            ExprKind::For(
                x.clone(), 
                Box::new(Expr::new(ExprKind::Array(vec![
                    Expr::with_type(
                        ExprKind::Lit(Lit::Int(1)),
                        Ty::Scalar(ScalarData::I32)
                    ),
                    Expr::with_type(
                        ExprKind::Lit(Lit::Int(2)),
                        Ty::Scalar(ScalarData::I32)
                    ),
                    Expr::with_type(
                        ExprKind::Lit(Lit::Int(3)),
                        Ty::Scalar(ScalarData::I32)
                )]))),
                Box::new(Expr::new(
                    ExprKind::Assign(
                        PlaceExpr::Var(x.clone()),
                        Box::new(Expr::new(ExprKind::Binary(
                            BinOp::Add,
                            Box::new(Expr::new(
                                ExprKind::PlaceExpr(PlaceExpr::Var(x.clone()))
                            )),
                            Box::new(Expr::with_type(
                                ExprKind::Lit(Lit::Int(1)),
                                Ty::Scalar(ScalarData::I32)
                            ))),
                    ))),
                ))),
        )));
    }

    #[test]
    fn expression_for_loop_negative() {
        let result_expect_ident = descend::expression_seq("for (1+2) in [1,2,3] {x = x+1}");
        assert!(result_expect_ident.is_err());
    }

    #[test]
    fn expression_sync_threads() {
        let elems = Ident::new("elems");
        assert_eq!(descend::expression_seq("sync_threads[gpu; 1024] for elems in elems_grouped {*elems.0 = *elems.0 + *elems.1;}"), Ok(Expr::new(
            ExprKind::ParForGlobalSync(
                Box::new(Expr::new(ExprKind::PlaceExpr(PlaceExpr::Var(Ident::new("gpu"))))),
                Nat::Lit(1024),
                elems.clone(),
                Box::new(Expr::new(ExprKind::PlaceExpr(PlaceExpr::Var(Ident::new("elems_grouped"))))),
                Box::new(Expr::new(ExprKind::Assign(
                    PlaceExpr::Deref(
                        Box::new(PlaceExpr::Proj(
                            Box::new(PlaceExpr::Var(elems.clone())),
                            Nat::Lit(0)))),
                    Box::new(Expr::new(ExprKind::Binary(
                        BinOp::Add,
                        Box::new(Expr::new(ExprKind::PlaceExpr(
                            PlaceExpr::Deref(
                                Box::new(PlaceExpr::Proj(
                                    Box::new(PlaceExpr::Var(elems.clone())),
                                    Nat::Lit(0))))
                        ))),
                        Box::new(Expr::new(ExprKind::PlaceExpr(
                            PlaceExpr::Deref(
                                Box::new(PlaceExpr::Proj(
                                    Box::new(PlaceExpr::Var(elems.clone())),
                                    Nat::Lit(1))))
                        )))
                    )))
                )))
            )
        )));
        //Negative test
        let result = descend::expression_seq("sync_threads[gpu; 10.24] for elems in elems_grouped {*elems.0 = *elems.0 + *elems.1;}");
        assert!(result.is_err()); //expected Integer - read Float
    }

    #[test]
    fn expression_let() {
        assert_eq!(descend::expression_seq("let mut x : f32 = 17.123f32; true"), Ok(Expr::with_type(
            ExprKind::Let(
                Mutability::Mut,
                Ident::new("x"),
                Ty::Scalar(ScalarData::F32),
                Box::new(Expr::with_type(
                    ExprKind::Lit(Lit::Float(17.123)),
                    Ty::Scalar(ScalarData::F32)
                )),
                Box::new(Expr::with_type(
                    ExprKind::Lit(Lit::Bool(true)),
                    Ty::Scalar(ScalarData::Bool)
                ))
            ),
            Ty::Scalar(ScalarData::Bool)
        )));
    }

    #[test]
    fn expression_let_negative() {
        // Does there always have to be another instruction after let ?
        let result = descend::expression_seq("let mut x : f32 = 17.123f32;");
        assert!(result.is_err());
        let result = descend::expression_seq("let mut x : 32 = 17.123f32; true");
        assert!(result.is_err());
        let result = descend::expression_seq("let mut x:bool@gpu.shared@ = false; true");
        assert!(result.is_err());
        let result = descend::expression_seq("let x = 17.123; true");
        assert!(result.is_err());
        let result = descend::expression_seq("let x:bool@Memory.Location = false; true");
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
        assert_eq!(descend::expression("-1 + 2 * 3 + 4 + 5 * 6 * 7"), Ok(Expr::new(
            ExprKind::Binary(BinOp::Add,
                Box::new(Expr::new(ExprKind::Binary(
                    BinOp::Add,
                    Box::new(Expr::new(ExprKind::Binary(
                        BinOp::Add,
                        Box::new(Expr::new(ExprKind::Unary(UnOp::Neg,
                            Box::new(Expr::with_type(
                                ExprKind::Lit(Lit::Int(1)),
                                Ty::Scalar(ScalarData::I32)
                            ))
                        ))),
                        Box::new(Expr::new(ExprKind::Binary(
                            BinOp::Mul,
                            Box::new(Expr::with_type(
                                ExprKind::Lit(Lit::Int(2)),
                                Ty::Scalar(ScalarData::I32)
                            )),
                            Box::new(Expr::with_type(
                                ExprKind::Lit(Lit::Int(3)),
                                Ty::Scalar(ScalarData::I32)
                            ))
                        )))
                    ))),
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::Int(4)),
                        Ty::Scalar(ScalarData::I32)                  
                    ))
                ))),
                Box::new(Expr::new(ExprKind::Binary(
                    BinOp::Mul,
                    Box::new(Expr::new(ExprKind::Binary(
                        BinOp::Mul,
                        Box::new(Expr::with_type(
                            ExprKind::Lit(Lit::Int(5)),
                            Ty::Scalar(ScalarData::I32)
                        )),
                        Box::new(Expr::with_type(
                            ExprKind::Lit(Lit::Int(6)),
                            Ty::Scalar(ScalarData::I32)
                        )))
                    )),
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::Int(7)),
                        Ty::Scalar(ScalarData::I32)
                    )))
                ))
            ),
        )));

        // precedences overridden via parentheses
        assert_eq!(descend::expression("-(1 + 2) * ((3 + (4 + 5) * 6) * 7)"), Ok(Expr::new(
            ExprKind::Binary(
                BinOp::Mul, 
                Box::new(Expr::new(ExprKind::Unary(
                    UnOp::Neg, 
                    Box::new(Expr::new(ExprKind::Binary(
                        BinOp::Add, 
                        Box::new(Expr::with_type(
                            ExprKind::Lit(Lit::Int(1)),
                            Ty::Scalar(ScalarData::I32)
                        )), 
                        Box::new(Expr::with_type(
                            ExprKind::Lit(Lit::Int(2)),
                            Ty::Scalar(ScalarData::I32)
                        ))),
                    ))),
                )), 
                Box::new(Expr::new(ExprKind::Binary(
                    BinOp::Mul, 
                    Box::new(Expr::new(ExprKind::Binary(
                        BinOp::Add, 
                        Box::new(Expr::with_type(
                            ExprKind::Lit(Lit::Int(3)),
                            Ty::Scalar(ScalarData::I32)
                        )),
                        Box::new(Expr::new(ExprKind::Binary(
                            BinOp::Mul, 
                            Box::new(Expr::new(ExprKind::Binary(
                                BinOp::Add, 
                                Box::new(Expr::with_type(
                                    ExprKind::Lit(Lit::Int(4)),
                                    Ty::Scalar(ScalarData::I32)
                                )), 
                                Box::new(Expr::with_type(
                                    ExprKind::Lit(Lit::Int(5)),
                                    Ty::Scalar(ScalarData::I32)
                                ))
                            ))),
                            Box::new(Expr::with_type(
                                ExprKind::Lit(Lit::Int(6)),
                                Ty::Scalar(ScalarData::I32)
                            ))
                        )))
                    ))), 
                    Box::new(Expr::with_type(
                        ExprKind::Lit(Lit::Int(7)),
                        Ty::Scalar(ScalarData::I32)
                    ))
                )))
            ),
        )));
    }

    #[test]
    fn global_fun_def_vector_add() {
        let src = r#"fn inplace_vector_add<n: nat, a: prv, b: prv>(
        ha_array: &'a uniq cpu.heap [i32; n],
        hb_array: &'b shrd cpu.heap [i32; n]
    ) -[cpu.thread]-> () {
        letprov <a, b, c, d, e, f, g, h> {
            let gpu: GPU = gpu(/* GPU info */);
        
            let mut a_array: [i32; n] @ gpu.global = copy_to_gpu<c, 'a, [i32; n]>(&c uniq gpu, ha_array);
            let b_array: [i32; n] @ gpu.global = copy_to_gpu<[i32; n]>(&d uniq gpu, hb_array);
        
            let view_a: [[&a uniq gpu.global i32; n]] = to_view<a, uniq, gpu.global, n, i32>(&a uniq a_array);
            let view_b: [[&b shrd gpu.global i32; n]] = to_view<b, shrd, gpu.global, n, i32>(&b shrd b_array);
            let elems_grouped_for_threads: [[(&a uniq gpu.global i32, &b shrd gpu.global i32); n]] =
            zip<n, &a uniq gpu.global i32, &b shrd gpu.global i32>(view_a, view_b);
            // hoisted runtime check: n == 64 * 1024
            sync_threads[gpu; 1024] for elems in elems_grouped_for_threads { // elems: (&a uniq gpu.global i32, &b uniq gpu.global i32)
                *elems.0 = *elems.0 + *elems.1; // elems.0: &a uniq gpu.global i32
            };
            copy_to_host<n, g, 'a, i32>(&g shrd a_array, ha_array);
        }
    }"#;
    let result = descend::global_fun_def(src);
    match &result {
        Err(e) => println!("{}", e),
        _ => {}
    };

    let expr_seq = r#"let gpu: GPU = gpu(/* GPU info */);
        
    let mut a_array: [i32; n] @ gpu.global = copy_to_gpu<c, 'a, [i32; n]>(&c uniq gpu, ha_array);
    let b_array: [i32; n] @ gpu.global = copy_to_gpu<[i32; n]>(&d uniq gpu, hb_array);

    let view_a: [[&a uniq gpu.global i32; n]] = to_view<a, uniq, gpu.global, n, i32>(&a uniq a_array);
    let view_b: [[&b shrd gpu.global i32; n]] = to_view<b, shrd, gpu.global, n, i32>(&b shrd b_array);
    let elems_grouped_for_threads: [[(&a uniq gpu.global i32, &b shrd gpu.global i32); n]] =
    zip<n, &a uniq gpu.global i32, &b shrd gpu.global i32>(view_a, view_b);
    // hoisted runtime check: n == 64 * 1024
    sync_threads[gpu; 1024] for elems in elems_grouped_for_threads { // elems: (&a uniq gpu.global i32, &b uniq gpu.global i32)
        *elems.0 = *elems.0 + *elems.1; // elems.0: &a uniq gpu.global i32
    };
    copy_to_host<n, g, 'a, i32>(&g shrd a_array, ha_array);"#;

    // TODO: Do proper check against expected AST
    let name = "inplace_vector_add".into();
    let ty_idents = vec!{
        IdentKinded::new(&Ident::new("n"), Kind::Nat),
        IdentKinded::new(&Ident::new("a"), Kind::Provenance),
        IdentKinded::new(&Ident::new("b"), Kind::Provenance),
    };
    let params = vec!{
        IdentTyped::new(Ident::new("ha_array"), Ty::Ref(
            Provenance::Value("\'a".into()), 
            Ownership::Uniq,
            Memory::CpuHeap,
            Box::new(Ty::Array(Box::new(Ty::Scalar(ScalarData::I32)), Nat::Ident(Ident::new("n"))))
        )),
        IdentTyped::new(Ident::new("hb_array"), Ty::Ref(
            Provenance::Value("\'b".into()), 
            Ownership::Shrd,
            Memory::CpuHeap,
            Box::new(Ty::Array(Box::new(Ty::Scalar(ScalarData::I32)), Nat::Ident(Ident::new("n"))))
        )),
    };
    let ret_ty = Ty::Scalar(ScalarData::Unit);
    let exec = ExecLoc::CpuThread;
    let prv_rels = vec![];

    let f_ty = fun_ty(
        params
            .iter()
            .map(|ident| -> Ty { ident.ty.clone() })
            .collect(),
        &FrameExpr::FrTy(vec![]),
        exec,
        &ret_ty,
    );

    let intended = GlobalFunDef{
        name,
        ty_idents,
        params,
        ret_ty,
        exec,
        prv_rels,
        body_expr: descend::expression_seq(&expr_seq).unwrap(),
        fun_ty: f_ty
      };
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), intended, "Something was not parsed as intended")
    }

    #[test]
    fn global_fun_def_all_function_kinds() {
        // all currently available kinds are tested
        let src = r#"fn test_kinds<n: nat, a: prv, t: ty, m: mem, f: frm>(
            ha_array: &'a uniq cpu.heap [i32; n]
        ) -[cpu.thread]-> () {
            letprov <some, stuff> {     
                let answer_to_everything :i32 = 42;
                answer_to_everything
            }
        }"#;
        let body = r#"let answer_to_everything :i32 = 42;
            answer_to_everything"#;

        let result = descend::global_fun_def(src);

        // TODO: Do proper check against expected AST
        let name = "test_kinds".into();
        let ty_idents = vec!{
            IdentKinded::new(&Ident::new("n"), Kind::Nat),
            IdentKinded::new(&Ident::new("a"), Kind::Provenance),
            IdentKinded::new(&Ident::new("t"), Kind::Ty),
            IdentKinded::new(&Ident::new("m"), Kind::Memory),
            IdentKinded::new(&Ident::new("f"), Kind::Frame),
        };
        let params = vec!{
            IdentTyped::new(Ident::new("ha_array"), Ty::Ref(
                Provenance::Value("\'a".into()), 
                Ownership::Uniq,
                Memory::CpuHeap,
                Box::new(Ty::Array(Box::new(Ty::Scalar(ScalarData::I32)), Nat::Ident(Ident::new("n"))))
            )),
        };
        let ret_ty = Ty::Scalar(ScalarData::Unit);
        let exec = ExecLoc::CpuThread;
        let prv_rels = vec![];

        let f_ty = fun_ty(
            params
                .iter()
                .map(|ident| -> Ty { ident.ty.clone() })
                .collect(),
            &FrameExpr::FrTy(vec![]),
            exec,
            &ret_ty,
        );

        let intended = GlobalFunDef{
            name,
            ty_idents,
            params,
            ret_ty,
            exec,
            prv_rels,
            body_expr: descend::expression_seq(body).unwrap(),
            fun_ty: f_ty
        };

        assert_eq!(result.unwrap(), intended);
    }

    #[test]
    fn global_fun_def_kind_parameters_optional() {
        // test both versions with and without <> pointy brackets
        let src_1 = r#"fn no_kinds(
            ha_array: &'a uniq cpu.heap [i32; n],
            hb_array: &'b shrd cpu.heap [i32; n]
        ) -[cpu.thread]-> () {
            let answer_to_everything :i32 = 42;
            answer_to_everything
        }"#;
        let src_2 = r#"fn no_kinds<>(
            ha_array: &'a uniq cpu.heap [i32; n],
            hb_array: &'b shrd cpu.heap [i32; n]
        ) -[cpu.thread]-> () {
            let answer_to_everything :i32 = 42;
            answer_to_everything
        }"#;

        let result_1 = descend::global_fun_def(src_1);
        let result_2 = descend::global_fun_def(src_2);

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

        let result = descend::global_fun_def(src);

        assert!(result.is_err());
    }

    #[test]
    fn global_fun_def_no_function_parameters_required() {
        let src = r#"fn no_params<n: nat, a: prv, b: prv>() -[cpu.thread]-> () {            
            let answer_to_everything :i32 = 42;
            answer_to_everything
        }"#;

        let result = descend::global_fun_def(src);
        assert!(result.is_ok());
    }

    // TODO: This test is to be completed when binary operations for Nat Type are implemented
    /*
    #[test]
    fn par_reduce() {
        let src = r#"fn par_reduce<n: nat, a: prv>(     // update to current syntax: 'a => a for prv
        ha_array: &'a uniq cpu.heap [i32; n]
    ) -[cpu.thread]-> i32 {
        letprov <e, g, r, s, h> {
            let gpu: GPU = gpu(/* GPU info */);
            let mut gpu_arr : [i32; n] = copy_to_gpu<g, 'a, [i32; n]>(&g uniq gpu, ha_array);
                // // Modified: added ` : [i32; n]`, parse broke here otherwise
            let view_arr: [[&r shrd gpu.global i32; n]] = 
                to_view<r, uniq, gpu.global, n, i32>(&r uniq gpu_arr);
            let chunks: [[ [[&r uniq gpu.global i32; n/1024]]; 1024]] = 
                group<n/1024, n, &r uniq gpu.global i32>(view_arr);
            // transpose for coalescing
            let chunks_for_threads: [[ [[&r uniq gpu.global i32; 1024]]; n/1024]] =
                transpose<1024, n/1024, &r uniq gpu.global i32>(chunks_for_threads);
            // hoisted runtime check: n/1024 == 64 * 1024
            // reduce chunks in parallel
            sync_threads[gpu, 64 * 1024] for chunck in chunks_for_threads {
                let mut acc: i32 = 0;
                for elem in chunck { // elem: &r uniq gpu.global i32
                    acc = acc + *elem;
                }
                // This works because array views themselves are immutable.
                // Hence, chunk is immutable and we would not be able to write something like
                // chunk[0] = other_borrow: &r uniq gpu.global i32
                *(chunck[0]) = acc;
            }
            
            // drop uniq borrows of gpu_arr before out is constructed
            let out_view: [[&s shrd gpu.global i32; n]] =
                to_view<s, shrd, gpu.global, n, i32>(&s shrd gpu_arr);
            let part_res_only_gpu: [[&s shrd gpu.global i32; 64*1024]] =
                take<64*1024, n, &s shrd gpu.global i32>(out_view);
            let part_res_only_host: [[&h uniq cpu.heap i32; 64*1024]] =
                take<64*1024>(to_view(&h uniq cpu.heap ha_array));
            view_copy_to_host<64*1024, h, s, i32>(part_res_only_host, part_res_only_gpu);
        
            // host-side reduction of the partial results
            let mut acc: i32 = 0;
            for elem in part_res_only_host { // elem: &h uniq cpu.heap i32
                acc = acc + *elem;
            }

            acc // return result from function
        }
    }"#;
    let result = descend::global_item(src);
    // TODO: Do proper check against expected AST
    assert!(result.is_err()); // Currently not parsed properly due to Nat binOp Terms (i.e. 64*1024, n/1024 as Nat values)
    }
    */
}