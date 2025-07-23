extern crate core;

use crate::error::ErrorReported;
use bumpalo::Bump;
mod arena_ast;
mod ast;
mod codegen;
pub mod error;
pub mod parser;
pub mod ty_check;

pub fn compile(file_path: &str) -> Result<String, ErrorReported> {
    let source = parser::SourceCode::from_file(file_path)?;
    let arena = Bump::new();
    let mut compil_unit = parser::parse(&arena, &source);
    ty_check::ty_check(&mut compil_unit)?;
    Ok(codegen::gen(&compil_unit, false))
}
