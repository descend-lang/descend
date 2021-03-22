use clap::Clap;
use descend::parser::SourceFile;
use std::fs;

/// Try to parse a source file of Descend code and print the AST
#[derive(Clap)]
#[clap(version = "0.1", author = "The Descend developers")]
struct Opts {
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
    let unit = source_file.parse_unit().expect("Parser error");
    println!("{:?}", unit)
}
