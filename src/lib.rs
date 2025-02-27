extern crate core;

use crate::error::ErrorReported;
use std::fs::write;

mod ast;
mod codegen;
pub mod error;
pub mod parser;
pub mod ty_check;


pub fn compile(file_path: &str, output_path: Option<&str>) -> Result<String, ErrorReported> {
    let source = parser::SourceCode::from_file(file_path)?;
    let mut compil_unit = parser::parse(&source)?;
    ty_check::ty_check(&mut compil_unit)?;
    let generated_code = codegen::gen(&compil_unit, false);

    if let Some(out) = output_path {
        write(out, &generated_code).map_err(|e| {
            eprintln!("Error writing output file {}: {}", out, e);
            ErrorReported
        })?;
    }

    Ok(generated_code)
}
