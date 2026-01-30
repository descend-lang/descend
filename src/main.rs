use clap::{Args, Parser, Subcommand};
use descend::error::NVCCError;
use descend::{compile, error::ErrorReported, error::ExecutableError, error::FileIOError};
use env_logger::Env;
use log::LevelFilter;
use log::{debug, error, info};
use std::env;
use std::fs;
use std::fs::write;
use std::path::PathBuf;
use std::process;
use std::process::{exit, Command};
use std::time::{SystemTime, UNIX_EPOCH};
use which::which;

#[derive(Parser, Debug)]
#[command(name = "descendc", version = "1.0", about = "Descend Compiler")]
struct Cli {
    /// Enable debug mode.
    #[arg(short, long)]
    debug: bool,

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

    /// Only save the generated CUDA file if explicitly requested.
    #[arg(long)]
    save_cuda: bool,
}

/// RAII wrapper for a temporary file.
struct TempFile {
    path: PathBuf,
}

impl TempFile {
    fn new(path: PathBuf) -> Self {
        TempFile { path }
    }

    /// Returns the file path as a string.
    fn path_string(&self) -> String {
        self.path.to_string_lossy().into_owned()
    }
}

impl Drop for TempFile {
    fn drop(&mut self) {
        // Attempt to delete the file; report error if it fails.
        if let Err(e) = fs::remove_file(&self.path) {
            error!(
                "Warning: failed to remove temporary file {:?}: {}",
                self.path, e
            );
        } else {
            debug!("Temporary file {:?} deleted.", self.path);
        }
    }
}

/// Checks if a command exists using the which crate
fn command_exists(cmd: &str) -> bool {
    which(cmd).is_ok()
}

fn generate_cuda(input: &str) -> Result<String, ErrorReported> {
    compile(input)
}

fn write_cuda_file(cuda_code: &str, filename: &str) -> Result<(), ErrorReported> {
    write(filename, cuda_code).map_err(|e| FileIOError::new(filename, e).emit())
}

fn build_cuda(
    cuda_file: &str,
    executable: &str,
    optimize: u8,
    arch: &str,
    nvcc_flags: &str,
) -> Result<(), ErrorReported> {
    let mut nvcc_cmd = Command::new("nvcc");
    nvcc_cmd
        .arg(cuda_file)
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
    let output = nvcc_cmd
        .output()
        .map_err(|_e| NVCCError::new("Failed to run nvcc command").emit())?;
    if !output.status.success() {
        return Err(NVCCError::new(format!(
            "nvcc compilation failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        ))
        .emit());
    }
    Ok(())
}

fn run_executable(executable: &str) -> Result<(), ErrorReported> {
    let output = Command::new(format!("./{}", executable))
        .output()
        .map_err(|_e| ExecutableError::new("Failed to run the executable").emit())?;

    info!(
        "Program output:\n{}",
        String::from_utf8_lossy(&output.stdout)
    );
    error!(
        "Program errors:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    Ok(())
}

fn handle_emit(common: CommonArgs) -> Result<(), ErrorReported> {
    let cuda_code = generate_cuda(&common.input)?;
    if let Some(file) = common.output {
        write_cuda_file(&cuda_code, &file)?;
        info!("CUDA code written to {}", file);
    } else {
        info!("Generated CUDA Code:\n{}", cuda_code);
    }
    Ok(())
}

fn handle_build_run(
    common: CommonArgs,
    build_run: BuildRunArgs,
    run_after: bool,
    suppress_cuda_warning: bool,
) -> Result<(), ErrorReported> {
    if !command_exists("nvcc") {
        if suppress_cuda_warning {
            info!("Warning: 'nvcc' not found, but warnings are suppressed. Compilation will likely fail.");
        } else {
            return Err(
                NVCCError::new("Error: 'nvcc' is not installed. Please install the CUDA Toolkit to compile the code.")
                    .emit()
            );
        }
    }
    let cuda_code = generate_cuda(&common.input)?;

    // Determine the file name based on the --save-cuda flag. If save_cuda is false, generate a temporary file path.
    let (cuda_file, _temp_guard): (String, Option<TempFile>) = if build_run.save_cuda {
        (
            common
                .output
                .unwrap_or_else(|| common.input.replace(".desc", ".cu")),
            None,
        )
    } else {
        let temp_dir = env::temp_dir();
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_millis();
        let temp_filename = format!("descendc-{}-{}.cu", process::id(), timestamp);
        let temp_path = temp_dir.join(temp_filename);
        let file_str = temp_path.to_string_lossy().into_owned();
        (file_str, Some(TempFile::new(temp_path)))
    };

    write_cuda_file(&cuda_code, &cuda_file)?;
    debug!("CUDA code written to {}", cuda_file);

    let executable = cuda_file.replace(".cu", "");
    build_cuda(
        &cuda_file,
        &executable,
        build_run.optimize,
        &build_run.arch,
        &build_run.nvcc_flags,
    )?;
    debug!("Compilation successful: {}", executable);

    if run_after {
        run_executable(&executable)?;
    }

    Ok(())
}

fn main() {
    let cli = Cli::parse();

    let default_log_level = if cli.debug {
        LevelFilter::Debug
    } else {
        LevelFilter::Info
    };

    env_logger::Builder::from_env(Env::default().default_filter_or(default_log_level.to_string()))
        .init();

    if cli.debug {
        info!("Debug mode enabled.");
    }

    if !command_exists("clang-format") {
        error!("Error: 'clang-format' is not installed. Please install clang-format to proceed.");
        exit(1);
    }

    let result = match cli.command {
        Commands::Emit { common } => handle_emit(common),
        Commands::Build { common, build_run } => {
            handle_build_run(common, build_run, false, cli.suppress_cuda_warning)
        }
        Commands::Run { common, build_run } => {
            handle_build_run(common, build_run, true, cli.suppress_cuda_warning)
        }
    };

    if let Err(e) = result {
        error!("{:#}", e);
        exit(1);
    }
}
