use crate::ast::ty::{Nat, Ty, ScalarData, Kinded, ExecLoc, Memory, Provenance};
#[allow(unused_imports)]
use crate::ast::{Ownership, Mutability};
use crate::*;


peg::parser!{
    pub(crate) grammar descent() for str {

        /// Parse nat token
        pub(crate) rule nat() -> Nat 
            = s:$("0" / (['1'..='9']['0'..='9']+)) { ?
                // TODO: Getting the cause of the parse error is unstable for now. Fix this once 
                // int_error_matching becomes stable
                match s.parse::<usize>() {
                    Ok(val) => Ok(Nat::Lit(val)),
                    Err(_) => { Err("Cannot parse natural number") }
                }
            }
            / name:identifier() {
                Nat::Ident(Nat::new_ident(&name))
            }
            // TODO: binary operations are currently disabled
            // TODO: Add 0b, 0o and 0x prefixes for binary, octal and hexadecimal?

        /// Parse a type token
        pub(crate) rule ty() -> Ty
            = first:ty_term() _ mems:("@" _ mem:memory_kind() _ {mem})* {
                if mems.is_empty() {
                    first
                }
                else {
                    mems.into_iter().fold(first, |prev,mem| Ty::At(Box::new(prev), mem))
                }
            }

        /// Helper for "type @ memory" left-recursion
        rule ty_term() -> Ty
            = "f32" { Ty::Scalar(ScalarData::F32) }
            / "i32" { Ty::Scalar(ScalarData::I32) }
            / "bool" { Ty::Scalar(ScalarData::Bool) }
            / "()" { Ty::Scalar(ScalarData::Unit) }
            / "GPU" { Ty::GPU }
            / name:identifier() { Ty::Ident(Ty::new_ident(&name)) }
            / "(" _ types:ty() ** ( _ "," _ ) _ ")" { Ty::Tuple(types) }
            / "[" _ t:ty() _ ";" _ n:nat() _ "]" { Ty::Array(Box::new(t), n) }
            / "[[" _ t:ty() _ ";" _ n:nat() _ "]]" { Ty::ArrayView(Box::new(t), n) }
            / "&" _ prov:prov_identifier() _ own:ownership() _ mem:memory_kind() _ ty:ty() {
                Ty::Ref(
                    Provenance::Ident(Provenance::new_ident(&prov)), // TODO: When should this be Provenance::Value?
                    own, mem, Box::new(ty)
                )
            }

        pub(crate) rule ownership() -> ast::Ownership
        = "shrd" { ast::Ownership::Shrd }
        / "uniq" { ast::Ownership::Uniq }

        pub(crate) rule mutability() -> ast::Mutability
        = "const" { ast::Mutability::Const }
        / "mut" { ast::Mutability::Mut }

        pub(crate) rule memory_kind() -> Memory
            = "cpu.stack" { Memory::CpuStack }
            / "cpu.heap" { Memory::CpuHeap }
            / "gpu.global" { Memory::GpuGlobal }
            / "gpu.shared" { Memory::GpuShared }
            / name:identifier() { Memory::Ident(Memory::new_ident(&name)) }

        pub(crate) rule execution_location() -> ExecLoc
            = "cpu.thread" { ExecLoc::CpuThread }
            / "gpu.group" { ExecLoc::GpuGroup }
            / "gpu.thread" { ExecLoc::GpuThread }

        rule ident() -> ast::Ident
            = i:$(identifier()) {
                ast::Ident{name: i.to_string()}
            }

        /// Identifier, but also allows leading ' for provenance names
        rule prov_identifier() -> String
        = s:$(identifier() / ("'" identifier())) { s.into() }

        /// Parse an identifier
        rule identifier() -> String
        = s:$(!keyword() (['a'..='z'|'A'..='Z'] ['a'..='z'|'A'..='Z'|'0'..='9'|'_']* 
            / ['_']+ ['a'..='z'|'A'..='Z'|'0'..='9'] ['a'..='z'|'A'..='Z'|'0'..='9'|'_']*))
        {
            s.into()
        }

        rule keyword() -> ()
            = "crate" / "super" / "self" / "Self" / "const" / "mut" / "uniq" / "shrd"
            / "f32" / "i32" / "bool" / "GPU"

        
        // Literal may be one of Unit, bool, i32, f32
        pub(crate) rule literal() -> ast::Lit
        = &"()" { ? 
            Ok(ast::Lit::Unit)
        }
        / l:$("true" / "false") {   ? 
            Ok(ast::Lit::Bool(l.parse::<bool>().unwrap()))
        }
        / l:$( ("-"? ((['1'..='9']['0'..='9']*) / "0") "." ['0'..='9']*)  (['e'|'E'] "-"?  ['0'..='9']*)? "f32"? ) { ?
            let mut _l = l.to_string();
            let mut exp:i32 = 0i32;

            if  (_l.len() > 3) && (&_l[_l.len()-3.._l.len()] == "f32") {
                _l = _l[0.._l.len()-3].to_string(); 
            }
            if _l.contains('e') {
                let _l_cp = _l.clone();
                let mut parts = _l_cp.split('e').into_iter();
                _l = parts.next().unwrap().to_string();
                exp = parts.next().unwrap().to_string().parse::<i32>().unwrap();
            } 

            let _f32 = _l.parse::<f32>();
            match _f32 {
                Ok(val) => Ok(ast::Lit::Float(val * 10f32.powi(exp))),
                Err(_) => Err("Parser Error: Value cannot be parsed to f32")
            }
        }
        / l:$((("-"? ['1'..='9']['0'..='9']*) / "0") "i32"?  ) { ? 
            let mut _l = l.to_string();
            
            if (_l.len() > 3) && (&_l[_l.len()-3.._l.len()] == "i32") {
                _l = _l[0.._l.len()-3].to_string();   
            }

            let _i32 = _l.parse::<i32>();

            match _i32 {
                Ok(val) => Ok(ast::Lit::Int(val)),
                Err(_) => Err("Parser Error: Value cannot be parsed to f32")
            }
        }


        /// Potential whitespace
        rule _() -> ()
            = quiet!{(
                [' '|'\n'|'\t'|'\r'] _) // 0 or more whitespaces
                / ("//" (!['\n'][_])* ['\n'] _) // Comment to EOL
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
        assert_eq!(descent::nat("N"), Ok(Nat::Ident(Nat::new_ident("N"))), "cannot parse N");
        assert_eq!(descent::nat("my_long_ident"), Ok(Nat::Ident(Nat::new_ident("my_long_ident"))),
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
        assert_eq!(descent::ty("T"), Ok(Ty::Ident(Ty::new_ident("T"))), 
            "does not recognize T type");
    }

    #[test]
    fn ty_reference() {
        assert_eq!(descent::ty("&'a uniq cpu.heap i32"), Ok(Ty::Ref(
                Provenance::Ident(Provenance::new_ident("'a")),
                Ownership::Uniq,
                Memory::CpuHeap,
                Box::new(Ty::Scalar(ScalarData::I32))
            )), "does not recognize type of unique i32 reference in cpu heap with provenance 'a");
        assert_eq!(descent::ty("&b shrd gpu.global [f32;N]"), Ok(Ty::Ref(
                Provenance::Ident(Provenance::new_ident("b")),
                Ownership::Shrd,
                Memory::GpuGlobal,
                Box::new(Ty::Array(
                    Box::new(Ty::Scalar(ScalarData::F32)),
                    Nat::Ident(Nat::new_ident("N"))
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
        assert_eq!(descent::memory_kind("M"), Ok(Memory::Ident(Memory::new_ident("M"))), 
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
        assert_eq!(descent::literal("true"), Ok(ast::Lit::Bool(true)), "does not parse boolean correctly");
        assert_eq!(descent::literal("False").is_err(), true, "wrongfully parses misspelled boolean");
        assert_eq!(descent::literal("12345"), Ok(ast::Lit::Int(12345)), "does not parse i32 correctly");
        assert_eq!(descent::literal("789i32"), Ok(ast::Lit::Int(789)), "does not parse i32 correctly");
        // TODO: Figure out why this test is failing.
        assert_eq!(descent::literal("-1i32"), Ok(ast::Lit::Int(-1)), "does not correctly parse 1e05i32 to i32");
        assert_eq!(descent::literal("1.0"), Ok(ast::Lit::Float(1.0)), "does not parse f32 correctly");
        assert_eq!(descent::literal("2.0f32"), Ok(ast::Lit::Float(2.0)), "does not parse f32 correctly");
        assert_eq!(descent::literal("777.7e0f32"), Ok(ast::Lit::Float(777.7)), "does not parse f32 correctly");
        assert_eq!(descent::literal("777.7e01f32"), Ok(ast::Lit::Float(7777.0)), "does not parse f32 correctly");
        assert_eq!(descent::literal("1.0e2"), Ok(ast::Lit::Float(100.0)), "does not parse f32 in scientific notation correctly");
        assert_eq!(descent::literal("1.0e-2"), Ok(ast::Lit::Float(0.01)), "does not parse f32 in scientific notation correctly");
        assert_eq!(descent::literal("3.7f32"), Ok(ast::Lit::Float(3.7)), "does not parse f32 correctly");
        assert_eq!(descent::literal("3.75e3"), Ok(ast::Lit::Float(3750.0)), "does not parse scientific notation f32 correctly");
        assert_eq!(descent::literal("-1234.5e-0005"), Ok(ast::Lit::Float(-0.012344999)), "does not parse negative scientific notation f32 correctly");
        assert_eq!(descent::literal("3.14159265358979323846264338327950288"), // std::f64::consts::PI
                                    Ok(ast::Lit::Float(3.1415927)), "not parsing f32 float as expected");
        assert_eq!(descent::literal("12345ad").is_err(), true, "incorrectly parsing invalid literal");
        assert_eq!(descent::literal("e54").is_err(), true, "incorrectly parsing e-notation only to literal");
        assert_eq!(descent::literal("-i32").is_err(), true, "incorrectly parsing 'negative data type' to literal");
    }
}
