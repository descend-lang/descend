#![feature(iter_partition_in_place)]

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
    compile_source(&source)
}

pub fn compile_src(source: &str) -> Result<String, ErrorReported> {
    let source = parser::SourceCode::new(String::from(source));
    compile_source(&source)
}

fn compile_source(source: &SourceCode) -> Result<String, ErrorReported> {
    let mut compil_unit = parser::parse(source)?;
    ty_check::ty_check(&mut compil_unit)?;
    Ok(codegen::gen(&compil_unit, false))
}
