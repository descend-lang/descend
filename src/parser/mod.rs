mod helpers;

use crate::ast::ty::{Nat, Ty, ScalarData, ExecLoc, Memory, Provenance, Kind, GlobalItem, GlobalFunDef, FrameExpr, IdentKinded, KindedArg};
use crate::ty_check::ty_ctx::IdentTyped;
use crate::ast::{Ownership, Mutability, Ident, Lit, PlaceExpr, Expr, ExprKind, BinOp, UnOp};

use crate::dsl::fun_ty;

peg::parser!{
    pub(crate) grammar descent() for str {

        // TODO: PreDeclaredGlobalFun missing Syntax
        pub(crate) rule global_item() -> GlobalItem
            = "fn" __ name:identifier() _ "<" _ ty_idents:(kind_parameter() ** (_ "," _)) _ ">" _
            "(" _ params:(fun_parameter() ** (_ "," _)) _ ")" _
            "-[" _ exec:execution_location() _ "]->" _ ret_ty:ty() _
            "{" _ "letprov" _ "<" _ identifier() ** (_ "," _) /* TODO: ast structure for letprov? */ _ ">" _
            "{" _ body_expr:expression_seq() _"}" _ "}" {
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
                GlobalItem::Def(Box::new(GlobalFunDef{
                  name,
                  ty_idents,
                  params,
                  ret_ty,
                  exec,
                  prv_rels: vec![], // TODO: What even is this?
                  body_expr,
                  fun_ty: f_ty
                }))
            }

        rule kind_parameter() -> IdentKinded
            = name:identifier() _ ":" _ kind:kind() {
                IdentKinded::new(&Ident::new(&name), kind)
            }

        rule fun_parameter() -> IdentTyped
            = ident:ident() _ ":" _ ty:ty() {
                IdentTyped { ident, ty }
            }

        /// Parse a sequence of expressions (might also just be one)
        pub(crate) rule expression_seq() -> Expr
            = head:expression() _ ";" _ tail:expression_seq()? {
                match tail{
                    None => head,
                    Some(tail) => {
                        let tail_ty = tail.ty.clone();
                        Expr{expr: ExprKind::Seq(Box::new(head), Box::new(tail)), ty: tail_ty}
                    }
                }
            }
            / "let" __ m:(m:mutability() __ {m})? ident:ident() _ ":" _ ty:ty() _ "=" _ expr:expression() _ ";" _
                tail:expression_seq()
            {
                let tail_ty = tail.ty.clone();
                Expr{expr:ExprKind::Let(m.unwrap_or(Mutability::Const), ident, ty, Box::new(expr), Box::new(tail)), ty: tail_ty}
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
            // TODO: Integrate this properly into the precedence parser (irrelevant for now
            // since there are no lambda functions yet)
            func:place_expression() _ kind_args:("<" _ k:kind_argument() ** (_ "," _) _ ">" _ { k })?
                "(" _ args:expression() ** (_ "," _) _ ")" {
                    helpers::make_function_application(
                        Expr{expr: ExprKind::PlaceExpr(func), ty: None}, kind_args, args)
                }
            l:literal() { 
                let ty = Some(helpers::type_from_lit(&l));
                Expr {expr: ExprKind::Lit(l), ty}
            }
            p:place_expression() idx:(_ "[" _ n:nat() _ "]" {n})? expr:(_ "=" _ e:expression() {e})? {
                match expr {
                    None => match idx {
                        None => Expr{expr: ExprKind::PlaceExpr(p), ty: None},
                        Some(idx) => Expr{expr: ExprKind::Index(p,idx), ty: None}
                    },
                    Some(expr) => match idx {
                        None => Expr{expr: ExprKind::Assign(p, Box::new(expr)), ty: None},
                        Some(_) => unimplemented!() // TODO: Implement array assignment
                    }
                }

            }
            "&" _ prov:provenance() __ own:ownership() __ p:place_expression() idx:(_ "[" _ n:nat() _ "]" {n})? {
                match idx {
                    None => Expr{expr: ExprKind::Ref(prov, own, p), ty: None},
                    Some(idx) => Expr{expr: ExprKind::BorrowIndex(prov, own, p,idx), ty: None}
                }
            }
            "[" _ expressions:expression() ** (_ "," _) _ "]" {
                Expr {expr: ExprKind::Array(expressions), ty: None}
            }
            "(" _ expressions:(e:expression() _ "," _ {e})* _ ")" {
                Expr {expr: ExprKind::Tuple(expressions), ty: None}
            }
            "if" _ cond:expression() _ "{" _ iftrue:expression_seq() _ "}" _ "else" _ "{" _ iffalse:expression_seq() _ "}" {
                Expr {
                    expr: ExprKind::IfElse(Box::new(cond), Box::new(iftrue), Box::new(iffalse)),
                    ty: None
                }
            }
            sync_threads:("sync_threads" _ "[" _ gpu_expr:expression() _ ";" _ threads:nat() _ "]" _ {(gpu_expr, threads)})?
                "for" _ ident:ident() _ "in" _ collection:expression() "{" _ body:expression_seq() _ "}"
            {
                match sync_threads {
                    None => Expr {
                            expr: ExprKind::For(ident, Box::new(collection), Box::new(body)),
                            ty: None
                        },
                    Some((gpu_expr, threads)) => Expr {
                        expr: ExprKind::ParForGlobalSync(
                            Box::new(gpu_expr), threads,
                            ident, Box::new(collection), Box::new(body)),
                        ty: None
                    },
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
            / ident:identifier() { KindedArg::Ident(Ident::new(&ident))}

        /// Place expression
        pub(crate) rule place_expression() -> PlaceExpr
            = derefs:("*" _)* name:identifier() _ ns:("." _ n:nat() _ {n})* {
                let root = PlaceExpr::Var(Ident::new(&name));
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
            / name:identifier() {
                Nat::Ident(Ident::new(&name))
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
            / name:identifier() { Ty::Ident(Ident::new(&name)) }
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
            / name:identifier() { Memory::Ident(Ident::new(&name)) }

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
            = i:$(identifier()) {
                Ident{name: i.to_string()}
            }

        rule provenance() -> Provenance
            = prov:prov_value() {
                Provenance::Value(prov)
            }
            / ident:identifier() {
                Provenance::Ident(Ident::new(&ident))
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
                / "let" / "if" / "else" / "for" / "in" / "sync_threads" / "fn" / "letprov")
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
        assert_eq!(descent::nat("0"), Ok(Nat::Lit(0)), "cannot parse 0");
        assert_eq!(descent::nat("42"), Ok(Nat::Lit(42)), "cannot parse 42");
        assert!(descent::nat("100000000000000000000").is_err(), "overflow not handled");
        assert!(descent::nat("-1").is_err(), "negative numbers not handled");
        assert!(descent::nat("3abc").is_err(), "garbage not handled");
        assert!(descent::nat("").is_err(), "matches empty");
    }

    #[test]
    #[ignore = "Unimplemented"]
    fn nat_identifier() {
        assert_eq!(descent::nat("N"), Ok(Nat::Ident(Ident::new("N"))), "cannot parse N");
        assert_eq!(descent::nat("my_long_ident"), Ok(Nat::Ident(Ident::new("my_long_ident"))),
            "cannot parse long identifer");
    }

    #[test]
    #[ignore = "Unimplemented"]
    fn nat_binary_operation() {
        todo!()
    }

    #[test]
    fn ty_scalar() {
        assert_eq!(descent::ty("f32"), Ok(Ty::Scalar(ScalarData::F32)), 
            "does not recognize f32 type");
        assert_eq!(descent::ty("i32"), Ok(Ty::Scalar(ScalarData::I32)), 
            "does not recognize i32 type");
        assert_eq!(descent::ty("()"), Ok(Ty::Scalar(ScalarData::Unit)), 
            "does not recognize unit type");
        assert_eq!(descent::ty("bool"), Ok(Ty::Scalar(ScalarData::Bool)), 
            "does not recognize Boolean type");
    }

    #[test]
    fn ty_gpu() {
        assert_eq!(descent::ty("GPU"), Ok(Ty::GPU), 
            "does not recognize GPU type");
    }

    #[test]
    fn ty_tuple() {
        let ty_f32 = Ty::Scalar(ScalarData::F32);
        let ty_i32 = Ty::Scalar(ScalarData::I32);
        let ty_unit = Ty::Scalar(ScalarData::Unit);
        assert_eq!(descent::ty("(f32)"), Ok(Ty::Tuple(vec![ty_f32])), 
            "does not recognize (f32) tuple type");
        assert_eq!(descent::ty("(i32,i32)"), Ok(Ty::Tuple(vec![ty_i32.clone(), ty_i32])), 
            "does not recognize (i32) tuple type");
        assert_eq!(descent::ty("((),(),())"), Ok(Ty::Tuple(vec![
            ty_unit.clone(), ty_unit.clone(), ty_unit.clone()])), 
            "does not recognize (unit,unit,unit) tuple type");
    }

    #[test]
    fn ty_array_view() {
        assert_eq!(descent::ty("[f32;42]"), Ok(Ty::Array(Box::new(
            Ty::Scalar(ScalarData::F32)),
            Nat::Lit(42)
        )), "does not recognize [f32;42] type");
        // TODO: Implement identifer parsing in nat
        // assert_eq!(descent::ty("[();N]"), Ok(Ty::Array(Box::new(
        //     Ty::Scalar(ScalarData::Unit)),
        //     Nat::Ident(Nat::new_ident("N")))
        // ), "does not recognize [();N] type");
        assert_eq!(descent::ty("[[i32;24]]"), Ok(Ty::ArrayView(Box::new(
            Ty::Scalar(ScalarData::I32)),
            Nat::Lit(24)
        )), "does not recognize [[f32;24]] type");
    }

    #[test]
    fn ty_identifier() {
        assert_eq!(descent::ty("T"), Ok(Ty::Ident(Ident::new("T"))), 
            "does not recognize T type");
    }

    #[test]
    fn ty_reference() {
        assert_eq!(descent::ty("&'a uniq cpu.heap i32"), Ok(Ty::Ref(
                Provenance::Value("'a".into()),
                Ownership::Uniq,
                Memory::CpuHeap,
                Box::new(Ty::Scalar(ScalarData::I32))
            )), "does not recognize type of unique i32 reference in cpu heap with provenance 'a");
        assert_eq!(descent::ty("&b shrd gpu.global [f32;N]"), Ok(Ty::Ref(
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
        assert_eq!(descent::ty("i32 @ cpu.stack"), Ok(Ty::At(
            Box::new(Ty::Scalar(ScalarData::I32)),
            Memory::CpuStack
        )), "does not recognize f32 @ cpu.stack type");
        assert_eq!(descent::ty("[f32;42] @ gpu.global"), Ok(Ty::At(
            Box::new(Ty::Array(Box::new(Ty::Scalar(ScalarData::F32)), Nat::Lit(42))),
            Memory::GpuGlobal
        )), "does not recognize [f32;42] @ gpu.global type");
    }

    #[test]
    fn ownership() {
        assert_eq!(descent::ownership("shrd"), Ok(Ownership::Shrd), 
            "does not recognize shrd ownership qualifier");
        assert_eq!(descent::ownership("uniq"), Ok(Ownership::Uniq), 
            "does not recognize uniq ownership qualifier");
    }

    #[test]
    #[ignore = "Mutability does not implement Eq"]
    fn mutability() {
        // TODO: Missing Eq implementation in AST
        // assert_eq!(descent::mutability("const"), Ok(Mutability::Const), 
        //     "does not recognize const mutability qualifier");
        // assert_eq!(descent::mutability("mut"), Ok(Mutability::Mut), 
        //     "does not recognize mut mutability qualifier");
    }

    #[test]
    fn memory_kind() {
        assert_eq!(descent::memory_kind("cpu.stack"), Ok(Memory::CpuStack), 
            "does not recognize cpu.stack memory kind");
        assert_eq!(descent::memory_kind("cpu.heap"), Ok(Memory::CpuHeap), 
            "does not recognize cpu.heap memory kind");
        assert_eq!(descent::memory_kind("gpu.global"), Ok(Memory::GpuGlobal), 
            "does not recognize gpu.global memory kind");
        assert_eq!(descent::memory_kind("gpu.shared"), Ok(Memory::GpuShared), 
            "does not recognize gpu.shared memory kind");
        assert_eq!(descent::memory_kind("M"), Ok(Memory::Ident(Ident::new("M"))), 
            "does not recognize M memory kind");
    }

    #[test]
    fn execution_location() {
        assert_eq!(descent::execution_location("cpu.thread"), Ok(ExecLoc::CpuThread), 
            "does not recognize cpu.stack memory kind");
        assert_eq!(descent::execution_location("gpu.group"), Ok(ExecLoc::GpuGroup), 
            "does not recognize cpu.heap memory kind");
        assert_eq!(descent::execution_location("gpu.thread"), Ok(ExecLoc::GpuThread), 
            "does not recognize gpu.global memory kind");
    }

    #[test]
    fn literal() {
        assert_eq!(descent::literal("true"), Ok(Lit::Bool(true)), "does not parse boolean correctly");
        assert_eq!(descent::literal("False").is_err(), true, "wrongfully parses misspelled boolean");
        assert_eq!(descent::literal("12345"), Ok(Lit::Int(12345)), "does not parse i32 correctly");
        assert_eq!(descent::literal("789i32"), Ok(Lit::Int(789)), "does not parse i32 correctly");
        assert_eq!(descent::literal("-1i32"), Ok(Lit::Int(-1)), "does not correctly parse 1e05i32 to i32");
        assert_eq!(descent::literal("1f32"), Ok(Lit::Float(1.)), "does not correctly parse 1f32 to f32");
        // TODO: Do proper float comparison (test error against threshold)
        assert_eq!(descent::literal("1.0"), Ok(Lit::Float(1.0)), "does not parse f32 correctly");
        assert_eq!(descent::literal("2.0f32"), Ok(Lit::Float(2.0)), "does not parse f32 correctly");
        assert_eq!(descent::literal("777.7e0f32"), Ok(Lit::Float(777.7)), "does not parse f32 correctly");
        assert_eq!(descent::literal("777.7e01f32"), Ok(Lit::Float(7777.0)), "does not parse f32 correctly");
        assert_eq!(descent::literal("1.0e2"), Ok(Lit::Float(100.0)), "does not parse f32 in scientific notation correctly");
        assert_eq!(descent::literal("1.0e-2"), Ok(Lit::Float(0.01)), "does not parse f32 in scientific notation correctly");
        assert_eq!(descent::literal("3.7f32"), Ok(Lit::Float(3.7)), "does not parse f32 correctly");
        assert_eq!(descent::literal("3.75e3"), Ok(Lit::Float(3750.0)), "does not parse scientific notation f32 correctly");
        assert_eq!(descent::literal("-1234.5e-0005"), Ok(Lit::Float(-0.012345)), "does not parse negative scientific notation f32 correctly");
        assert_eq!(descent::literal("3.14159265358979323846264338327950288"), // std::f64::consts::PI
                                    Ok(Lit::Float(3.1415927)), "not parsing f32 float as expected");
        assert_eq!(descent::literal("12345ad").is_err(), true, "incorrectly parsing invalid literal");
        assert_eq!(descent::literal("e54").is_err(), true, "incorrectly parsing e-notation only to literal");
        assert_eq!(descent::literal("-i32").is_err(), true, "incorrectly parsing 'negative data type' to literal");
    }

    #[test]
    fn kind() {
        assert_eq!(descent::kind("nat"), Ok(Kind::Nat), 
            "does not recognize nat kind");
        assert_eq!(descent::kind("mem"), Ok(Kind::Memory), 
            "does not recognize mem kind");
        assert_eq!(descent::kind("ty"), Ok(Kind::Ty), 
            "does not recognize ty kind");
        assert_eq!(descent::kind("prv"), Ok(Kind::Provenance), 
            "does not recognize prv kind");
        assert_eq!(descent::kind("frm"), Ok(Kind::Frame), 
            "does not recognize frm kind");
    }

    #[test]
    fn place_expression() {
        assert_eq!(descent::place_expression("*x"), Ok(
            PlaceExpr::Deref(Box::new(
                PlaceExpr::Var(Ident::new("x"))
            ))), "does not recognize place expression *x");
        assert_eq!(descent::place_expression("x.0"), Ok(
            PlaceExpr::Proj(
                Box::new(PlaceExpr::Var(Ident::new("x"))),
                Nat::Lit(0)
            )), "does not recognize place expression *x");
        assert_eq!(descent::place_expression("*x.0"), Ok(
            PlaceExpr::Deref(Box::new(
                PlaceExpr::Proj(
                    Box::new(PlaceExpr::Var(Ident::new("x"))),
                    Nat::Lit(0)
            )))), "does not recognize place expression *x.0");
    }

    #[test]
    fn expression() {
        assert_eq!(descent::expression("if 7+8 {let mut x : f32 = 17.123; true} else {15/3}"), Ok(Expr{
            expr: ExprKind::IfElse(
                Box::new(Expr{
                    expr: ExprKind::Binary(BinOp::Add, Box::new(Expr{
                            expr: ExprKind::Lit(Lit::Int(7)),
                            ty: Some(Ty::Scalar(ScalarData::I32))
                        }), Box::new(Expr{
                            expr: ExprKind::Lit(Lit::Int(8)),
                            ty: Some(Ty::Scalar(ScalarData::I32))
                        })),
                    ty: None
                }),
                Box::new(Expr{
                    expr: ExprKind::Let(Mutability::Mut, Ident::new("x"), Ty::Scalar(ScalarData::F32), Box::new(Expr{
                            expr: ExprKind::Lit(Lit::Float(17.123)),
                            ty: Some(Ty::Scalar(ScalarData::F32))
                        }), Box::new(Expr{
                            expr: ExprKind::Lit(Lit::Bool(true)),
                            ty: Some(Ty::Scalar(ScalarData::Bool))
                        })),
                    ty: Some(Ty::Scalar(ScalarData::Bool))
                }),
                Box::new(Expr{
                    expr: ExprKind::Binary(BinOp::Div, Box::new(Expr{
                            expr: ExprKind::Lit(Lit::Int(15)),
                            ty: Some(Ty::Scalar(ScalarData::I32))
                        }), Box::new(Expr{
                            expr: ExprKind::Lit(Lit::Int(3)),
                            ty: Some(Ty::Scalar(ScalarData::I32))
                        })),
                    ty: None
                })),
            ty: None
        }));
    }
    #[test]
    fn expression_if_else() {
        assert_eq!(descent::expression("if 7<8 {7+8} else {7*8}"), Ok(Expr{
            expr: ExprKind::IfElse(
                Box::new(Expr{
                    expr: ExprKind::Binary(BinOp::Lt, Box::new(Expr{
                            expr: ExprKind::Lit(Lit::Int(7)),
                            ty: Some(Ty::Scalar(ScalarData::I32))
                        }), Box::new(Expr{
                            expr: ExprKind::Lit(Lit::Int(8)),
                            ty: Some(Ty::Scalar(ScalarData::I32))
                        })),
                    ty: None
                }),
                Box::new(Expr{
                    expr: ExprKind::Binary(BinOp::Add, Box::new(Expr{
                            expr: ExprKind::Lit(Lit::Int(7)),
                            ty: Some(Ty::Scalar(ScalarData::I32))
                        }), Box::new(Expr{
                            expr: ExprKind::Lit(Lit::Int(8)),
                            ty: Some(Ty::Scalar(ScalarData::I32))
                        })),
                    ty: None
                }),
                Box::new(Expr{
                    expr: ExprKind::Binary(BinOp::Mul, Box::new(Expr{
                            expr: ExprKind::Lit(Lit::Int(7)),
                            ty: Some(Ty::Scalar(ScalarData::I32))
                        }), Box::new(Expr{
                            expr: ExprKind::Lit(Lit::Int(8)),
                            ty: Some(Ty::Scalar(ScalarData::I32))
                        })),
                    ty: None
                })),
            ty: None
        }));
    }
    #[test]
    fn expression_addition() {
        assert_eq!(descent::expression("7+8"), Ok(Expr{
            expr: ExprKind::Binary(BinOp::Add, Box::new(Expr{
                    expr: ExprKind::Lit(Lit::Int(7)),
                    ty: Some(Ty::Scalar(ScalarData::I32))
                }), Box::new(Expr{
                    expr: ExprKind::Lit(Lit::Int(8)),
                    ty: Some(Ty::Scalar(ScalarData::I32))
                })),
            ty: None
        }));
    }
    #[test]
    fn expression_literal() {
        assert_eq!(descent::expression("7"), Ok(Expr{
            expr: ExprKind::Lit(Lit::Int(7)),
            ty: Some(Ty::Scalar(ScalarData::I32))
        }));
    }
}
