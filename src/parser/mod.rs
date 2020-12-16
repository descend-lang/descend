use crate::ast::ty::{Nat, Ty, ScalarData};
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
            // TODO: missing identifier rule
            // TODO: binary operations are currently disabled
            // TODO: Add 0b, 0o and 0x prefixes for binary, octal and hexadecimal?

        /// Parse type token
        pub(crate) rule ty() -> Ty
            =  // TODO: missing identifer rule
            "f32" { Ty::Scalar(ScalarData::F32) }
            / "i32" { Ty::Scalar(ScalarData::I32) }
            / "bool" { Ty::Scalar(ScalarData::Bool) }
            / "()" { Ty::Scalar(ScalarData::Unit) }
            / "GPU" { Ty::GPU }
            / "(" _ types:ty() ** ( _ "," _ ) _ ")" { Ty::Tuple(types) }
            / "[" _ t:ty() _ ";" _ n:nat() _ "]" { Ty::Array(Box::new(t), n) }
            / "[[" _ t:ty() _ ";" _ n:nat() _ "]]" { Ty::ArrayView(Box::new(t), n) }
            // TODO: missing type @ memory_location rule
            // TODO: missing reference rule



        rule identifier() -> String
        = s:$(!keyword()
            /['a'..='z'|'A'..='Z'] ['a'..='z'|'A'..='Z'|'0'..='9'|'_']* 
            / ['_']+ ['a'..='z'|'A'..='Z'|'0'..='9'] ['a'..='z'|'A'..='Z'|'0'..='9'|'_']*
            / "'" identifier()
            )
        {String::from(s)}

        rule keyword() -> ()
        = "crate"/"super"/"self"/"Self"

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
        assert!(descent::nat("abc").is_err(), "garbage not handled");
        assert!(descent::nat("").is_err(), "matches empty");
    }

    #[test]
    #[ignore = "Unimplemented"]
    fn nat_identifier() {
        todo!()
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
}
