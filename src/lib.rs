use crate::error::ErrorReported;

// TODO remove pub where possible. only public because of basic_syntax tests
#[macro_use]
pub mod ast;
#[macro_use]
pub mod codegen;
pub mod error;
mod nat;
pub mod parser;
pub mod ty_check;
mod utils;

pub fn compile(file_path: &str) -> Result<String, ErrorReported> {
    let source = parser::SourceCode::from_file(file_path)?;
    let mut compil_unit = parser::parse(&source)?;
    ty_check::ty_check(&mut compil_unit)?;
    Ok(codegen::gen(&compil_unit))
}
