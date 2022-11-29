use std::sync::Once;

use ast::CompilUnit;
use parser::SourceCode;

use crate::error::ErrorReported;

#[macro_use]
mod ast;
#[macro_use]
mod codegen;
pub mod error;
mod parser;
mod ty_check;

pub fn compile(file_path: &str) -> Result<String, ErrorReported> {
    let source = parser::SourceCode::from_file(file_path)?;
    compile_source_code(&source)
}

pub fn compile_src(source: &str) -> Result<String, ErrorReported> {
    let source = parser::SourceCode::new(String::from(source));
    compile_source_code(&source)
}

fn compile_source_code(source: &SourceCode) -> Result<String, ErrorReported> {
    let mut compil_unit = parser::parse(source)?;
    let mut std_lib = get_stdlib_compil_unit();
    ty_check::ty_check(&mut compil_unit, &mut std_lib)?;
    Ok(codegen::gen(compil_unit, std_lib, false))
}

/// Return the CompilUnit for the standard library
fn get_stdlib_compil_unit() -> CompilUnit<'static> {
    const STD_LIB_PATH: &'static str = "src/stdlib.desc";
    static mut STD_LIB_SRC: Option<SourceCode> = None;
    static mut STD_LIB_COMPIL: Option<CompilUnit> = None;

    //Use the singleton-pattern
    static ONCE: Once = Once::new();
    unsafe {
        ONCE.call_once(|| {
            STD_LIB_SRC = Some(match SourceCode::from_file(STD_LIB_PATH) {
                Ok(s) => s,
                Err(err) => panic!("Reading stdlib failed\n{:#?}", err),
            });
            STD_LIB_COMPIL = Some(match crate::parser::parse(STD_LIB_SRC.as_ref().unwrap()) {
                Ok(c) => c,
                Err(err) => panic!("Parsing stdlib failed!\n{:#?}", err),
            });
        });

        STD_LIB_COMPIL.clone().unwrap()
    }
}
