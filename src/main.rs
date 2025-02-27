use clap::{Parser};
use descend::{compile, error::ErrorReported};
use std::process::exit;

/// Descend Compiler CLI
#[derive(Parser, Debug)]
#[command(name = "descendc", version = "1.0", about = "Descend GPU Compiler")]
struct Cli {
    pub input: String,

    #[arg(short, long)]
    pub output: Option<String>,

    #[arg(short, long)]
    pub debug: bool,

    #[arg(short, long)]
    pub verbose: bool,
}

fn main() {
    let args = Cli::parse();

    println!("Compiling: {}", args.input);

    if args.debug {
        println!("Debug mode enabled.");
    }

    if args.verbose {
        println!("Verbose output enabled.");
    }

    match compile(&args.input, args.output.as_deref()) {
        Ok(ptx_code) => {
            if args.output.is_none() {
                println!("{}", ptx_code);
            } else {
                println!("Compilation successful! Output written to {:?}", args.output);
            }
        }
        Err(ErrorReported) => {
            eprintln!("Compilation failed.");
            exit(1);
        }
    }
}
