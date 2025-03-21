use clap::{Parser, Subcommand};
use descend::{compile, error::ErrorReported};
use std::fs::write;
use std::process::{Command, exit};
use anyhow::{Context, Result};

#[derive(Parser, Debug)]
#[command(name = "descendc", version = "1.0", about = "Descend GPU Compiler")]
struct Cli {
    /// Enable debug mode
    #[arg(short, long)]
    debug: bool,
    
    /// Enable verbose output
    #[arg(short, long)]
    verbose: bool,
    
    /// Suppress warning if nvcc (CUDA Toolkit) is not installed (only applicable for build/run)
    #[arg(long)]
    suppress_cuda_warning: bool,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    /// Emit the generated CUDA code without compiling.
    Emit {
        /// Input file (.desc)
        input: String,
        /// Optionally write the CUDA code to a file (if not provided, it is printed)
        #[arg(short, long)]
        output: Option<String>,
    },
    /// Compile the generated CUDA code into a binary.
    Build {
        /// Input file (.desc)
        input: String,
        /// Optionally specify output file for the CUDA code (if not provided, uses the input name with a .cu extension)
        #[arg(short, long)]
        output: Option<String>,
        /// Specify CUDA architecture (e.g., `sm_75`, `sm_80`)
        #[arg(long, default_value = "sm_75")]
        arch: String,
        /// Optimization level for `nvcc` (`0-3`)
        #[arg(long, default_value = "3")]
        optimize: u8,
        /// Additional flags to pass directly to `nvcc`
        #[arg(long, default_value = "")]
        nvcc_flags: String,
    },
    /// Compile the generated CUDA code and run the resulting binary.
    Run {
        /// Input file (.desc)
        input: String,
        /// Optionally specify output file for the CUDA code (if not provided, uses the input name with a .cu extension)
        #[arg(short, long)]
        output: Option<String>,
        /// Specify CUDA architecture (e.g., `sm_75`, `sm_80`)
        #[arg(long, default_value = "sm_75")]
        arch: String,
        /// Optimization level for `nvcc` (`0-3`)
        #[arg(long, default_value = "3")]
        optimize: u8,
        /// Additional flags to pass directly to `nvcc`
        #[arg(long, default_value = "")]
        nvcc_flags: String,
    },
}

/// Helper function to check if a command exists by attempting to run `<cmd> --version`
fn check_command_exists(cmd: &str) -> bool {
    Command::new(cmd).arg("--version").output().is_ok()
}

/// Generates the CUDA code from the .desc file.
fn generate_cuda(input: &str) -> Result<String> {
    compile(input, None)
        .map_err(|_| anyhow::anyhow!("Descend compilation failed for input '{}'", input))
}

/// Writes the generated CUDA code to a file.
fn write_cuda_file(cuda_code: &str, filename: &str) -> Result<()> {
    write(filename, cuda_code).with_context(|| format!("Error writing CUDA file {}", filename))
}

/// Builds the CUDA file using nvcc.
fn build_cuda(cuda_file: &str, executable: &str, optimize: u8, arch: &str, nvcc_flags: &str) -> Result<()> {
    let mut nvcc_cmd = Command::new("nvcc");
    nvcc_cmd.arg(cuda_file)
        .arg(cuda_file) // Retaining the original behavior: passing the same file twice.
        .arg("-o")
        .arg(executable)
        .arg(format!("-O{}", optimize))
        .arg("-I")
        .arg("cuda-examples/")
        .args(nvcc_flags.split_whitespace());
    if arch != "none" {
        nvcc_cmd.arg(format!("-arch={}", arch));
    }
    let output = nvcc_cmd.output().with_context(|| "Failed to run nvcc command")?;
    if !output.status.success() {
        return Err(anyhow::anyhow!("nvcc compilation failed:\n{}", String::from_utf8_lossy(&output.stderr)));
    }
    Ok(())
}

/// Runs the generated executable.
fn run_executable(executable: &str) -> Result<()> {
    let output = Command::new(format!("./{}", executable))
        .output()
        .with_context(|| "Failed to run the executable")?;
    println!("Program output:\n{}", String::from_utf8_lossy(&output.stdout));
    eprintln!("Program errors:\n{}", String::from_utf8_lossy(&output.stderr));
    Ok(())
}

/// Handles the Emit subcommand.
fn handle_emit(input: String, output: Option<String>) -> Result<()> {
    let cuda_code = generate_cuda(&input)?;
    if let Some(file) = output {
        write_cuda_file(&cuda_code, &file)?;
        println!("CUDA code written to {}", file);
    } else {
        println!("Generated CUDA Code:\n{}", cuda_code);
    }
    Ok(())
}

/// Handles the Build and Run subcommands.
fn handle_build_run(
    input: String,
    output: Option<String>,
    arch: String,
    optimize: u8,
    nvcc_flags: String,
    run_after: bool,
    suppress_cuda_warning: bool,
) -> Result<()> {
    if !check_command_exists("nvcc") {
        if suppress_cuda_warning {
            eprintln!("Warning: 'nvcc' not found, but warnings are suppressed. Compilation will likely fail.");
        } else {
            return Err(anyhow::anyhow!("Error: 'nvcc' is not installed. Please install the CUDA Toolkit to compile the code."));
        }
    }
    let cuda_code = generate_cuda(&input)?;
    let cuda_file = output.unwrap_or_else(|| input.replace(".desc", ".cu"));
    let executable = cuda_file.replace(".cu", "");
    write_cuda_file(&cuda_code, &cuda_file)?;
    println!("CUDA code written to {}", cuda_file);
    build_cuda(&cuda_file, &executable, optimize, &arch, &nvcc_flags)?;
    println!("Compilation successful: {}", executable);
    if run_after {
        run_executable(&executable)?;
    }
    Ok(())
}

fn main() {
    let cli = Cli::parse();

    if cli.debug {
        println!("Debug mode enabled.");
    }
    if cli.verbose {
        println!("Verbose output enabled.");
    }

    // Always require clang-format.
    if !check_command_exists("clang-format") {
        eprintln!("Error: 'clang-format' is not installed. Please install clang-format to proceed.");
        exit(1);
    }

    // Process the subcommand.
    let result = match cli.command {
        Commands::Emit { input, output } => handle_emit(input, output),
        Commands::Build { input, output, arch, optimize, nvcc_flags } => {
            handle_build_run(input, output, arch, optimize, nvcc_flags, false, cli.suppress_cuda_warning)
        },
        Commands::Run { input, output, arch, optimize, nvcc_flags } => {
            handle_build_run(input, output, arch, optimize, nvcc_flags, true, cli.suppress_cuda_warning)
        },
    };

    if let Err(e) = result {
        eprintln!("{:#}", e);
        exit(1);
    }
}
