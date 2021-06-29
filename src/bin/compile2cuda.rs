use clap::Clap;
use descend::{parser::SourceFile, ty_check};
use std::{fs, io::Write};

/// Try to parse a source file of Descend code and print the AST
#[derive(Clap)]
#[clap(version = "0.1", author = "The Descend developers")]
struct Opts {
    /// Output file
    #[clap(short, default_value = "out.cu")]
    output: String,
    /// Path to source file
    source_file: String,
}

fn main() {
    // Get commandline arguments
    let opts = Opts::parse();
    // Try to open file
    let source = fs::read_to_string(opts.source_file).expect("Cannot open source file");
    let source_file = SourceFile::new(source);
    // Try to parse a global item
    let mut unit = source_file.parse_unit().expect("Parser error");
    ty_check::ty_check(&mut unit).expect("Typecheck Error");
    let generated_code = descend::codegen::gen(&unit);
    // Write to output
    let mut output = fs::File::create(opts.output).expect("Cannot create output file");
    output.write_all(generated_code.as_bytes()).expect("I/O Error while writing output");
}
