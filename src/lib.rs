use crate::error::ErrorReported;

mod ast;
mod codegen;
pub mod error;
mod parser;
mod ty_check;

pub fn compile(file_path: &str) -> Result<String, ErrorReported> {
    let source = parser::SourceCode::from_file(file_path)?;
    let mut compil_unit = parser::parse(&source)?;
    ty_check::ty_check(&mut compil_unit)?;
    Ok(codegen::gen(&compil_unit, false))
}
