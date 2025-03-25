use clap::{Parser, Subcommand, Args};
use descend::{compile, error::ErrorReported};
use std::fs::write;
use std::process::{Command, exit};
use anyhow::{Context, Result};
use log::{debug, error, info, warn};
use which::which;

#[derive(Parser, Debug)]
#[command(name = "descendc", version = "1.0", about = "Descend Compiler")]
struct Cli {
    /// Enable debug mode.
    #[arg(short, long)]
    debug: bool,

    /// Enable verbose output.
    #[arg(short, long)]
    verbose: bool,

    /// Suppress warning if nvcc (CUDA Toolkit) is not installed.
    #[arg(long)]
    suppress_cuda_warning: bool,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    /// Emit the generated CUDA code without compiling.
    Emit {
        #[clap(flatten)]
        common: CommonArgs,
    },
    /// Compile the generated CUDA code into a binary.
    Build {
        #[clap(flatten)]
        common: CommonArgs,
        #[clap(flatten)]
        build_run: BuildRunArgs,
    },
    /// Compile the generated CUDA code and run the resulting binary.
    Run {
        #[clap(flatten)]
        common: CommonArgs,
        #[clap(flatten)]
        build_run: BuildRunArgs,
    },
}

/// Arguments common to all subcommands.
#[derive(Args, Debug)]
struct CommonArgs {
    /// Input file (.desc)
    input: String,

    /// Optionally write the CUDA code to a file (if not provided, uses default naming)
    #[arg(short, long)]
    output: Option<String>,
}

/// Arguments only applicable to Build and Run.
#[derive(Args, Debug)]
struct BuildRunArgs {
    /// Specify CUDA architecture (e.g., sm_75, sm_80)
    #[arg(long, default_value = "sm_75")]
    arch: String,

    /// Optimization level for nvcc (0-3)
    #[arg(long, default_value = "3")]
    optimize: u8,

    /// Additional flags to pass directly to nvcc
    #[arg(long, default_value = "")]
    nvcc_flags: String,
}

/// Checks if a command exists using the which crate
fn command_exists(cmd: &str) -> bool {
    which(cmd).is_ok()
}

fn generate_cuda(input: &str) -> Result<String> {
    compile(input, None)
        .map_err(|_| anyhow::anyhow!("Descend compilation failed for input '{}'", input))
}

fn write_cuda_file(cuda_code: &str, filename: &str) -> Result<()> {
    write(filename, cuda_code)
        .with_context(|| format!("Error writing CUDA file {}", filename))
}

fn build_cuda(cuda_file: &str, executable: &str, optimize: u8, arch: &str, nvcc_flags: &str) -> Result<()> {
    let mut nvcc_cmd = Command::new("nvcc");
    nvcc_cmd.arg(cuda_file)
        .arg("-o")
        .arg(executable)
        .arg(format!("-O{}", optimize))
        .arg("-I")
        .arg("cuda-examples/")
        .args(nvcc_flags.split_whitespace());
    if arch != "none" {
        nvcc_cmd.arg(format!("-arch={}", arch));
    }
    debug!("Running NVCC command: {:?}", nvcc_cmd);
    let output = nvcc_cmd.output()
        .with_context(|| "Failed to run nvcc command")?;
    if !output.status.success() {
        return Err(anyhow::anyhow!("nvcc compilation failed:\n{}", String::from_utf8_lossy(&output.stderr)));
    }
    Ok(())
}

fn run_executable(executable: &str) -> Result<()> {
    let output = Command::new(format!("./{}", executable))
        .output()
        .with_context(|| "Failed to run the executable")?;
    println!("Program output:\n{}", String::from_utf8_lossy(&output.stdout));
    eprintln!("Program errors:\n{}", String::from_utf8_lossy(&output.stderr));
    Ok(())
}

fn handle_emit(common: CommonArgs) -> Result<()> {
    let cuda_code = generate_cuda(&common.input)?;
    if let Some(file) = common.output {
        write_cuda_file(&cuda_code, &file)?;
        println!("CUDA code written to {}", file);
    } else {
        println!("Generated CUDA Code:\n{}", cuda_code);
    }
    Ok(())
}

fn handle_build_run(
    common: CommonArgs,
    build_run: BuildRunArgs,
    run_after: bool,
    suppress_cuda_warning: bool,
) -> Result<()> {
    if !command_exists("nvcc") {
        if suppress_cuda_warning {
            eprintln!("Warning: 'nvcc' not found, but warnings are suppressed. Compilation will likely fail.");
        } else {
            return Err(anyhow::anyhow!("Error: 'nvcc' is not installed. Please install the CUDA Toolkit to compile the code."));
        }
    }
    let cuda_code = generate_cuda(&common.input)?;
    let cuda_file = common.output.unwrap_or_else(|| common.input.replace(".desc", ".cu"));
    let executable = cuda_file.replace(".cu", "");
    write_cuda_file(&cuda_code, &cuda_file)?;
    println!("CUDA code written to {}", cuda_file);
    build_cuda(&cuda_file, &executable, build_run.optimize, &build_run.arch, &build_run.nvcc_flags)?;
    println!("Compilation successful: {}", executable);
    if run_after {
        run_executable(&executable)?;
    }
    Ok(())
}

fn main() {
    env_logger::init();
    let cli = Cli::parse();

    if cli.debug {
        println!("Debug mode enabled.");
    }
    if cli.verbose {
        println!("Verbose output enabled.");
    }

    if !command_exists("clang-format") {
        eprintln!("Error: 'clang-format' is not installed. Please install clang-format to proceed.");
        exit(1);
    }

    let result = match cli.command {
        Commands::Emit { common } => handle_emit(common),
        Commands::Build { common, build_run } =>
            handle_build_run(common, build_run, false, cli.suppress_cuda_warning),
        Commands::Run { common, build_run } =>
            handle_build_run(common, build_run, true, cli.suppress_cuda_warning),
    };

    if let Err(e) = result {
        eprintln!("{:#}", e);
        exit(1);
    }
}
