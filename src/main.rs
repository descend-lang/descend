use clap::{Parser};
use descend::{compile, error::ErrorReported};
use std::fs::write;
use std::process::{Command, exit};

/// Descend Compiler CLI
#[derive(Parser, Debug)]
#[command(name = "descendc", version = "1.0", about = "Descend GPU Compiler")]
struct Cli {
    /// Input Descend source file
    pub input: String,

    /// Output CUDA file (optional, default: input_name.cu)
    #[arg(short, long)]
    pub output: Option<String>,

    /// Print CUDA code to stdout instead of saving
    #[arg(long)]
    pub emit_cuda: bool,

    /// Compile CUDA code with `nvcc`
    #[arg(long)]
    pub compile: bool,

    /// Run the compiled executable
    #[arg(long)]
    pub run: bool,

    /// Specify CUDA architecture (e.g., `sm_75`, `sm_80`)
    #[arg(long, default_value = "sm_75")]
    pub arch: String,

    /// Optimization level for `nvcc` (`0-3`)
    #[arg(long, default_value = "3")]
    pub optimize: u8,

    /// Additional flags to pass directly to `nvcc`
    #[arg(long, default_value = "")]
    pub nvcc_flags: String,

    /// Enable debug mode
    #[arg(short, long)]
    pub debug: bool,

    /// Enable verbose output
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

    // Step 1: Compile Descend to CUDA code
    match compile(&args.input, None) {
        Ok(cuda_code) => {
            // Step 2: Print CUDA code instead of saving it if `--emit-cuda` is set
            if args.emit_cuda {
                println!("Generated CUDA Code:\n{}", cuda_code);
                return; // Exit early, no further processing needed
            }

            // Step 3: Compile CUDA code with `nvcc` if `--compile` is set
            if args.compile {
                let cuda_file = args.output.clone().unwrap_or_else(|| args.input.replace(".desc", ".cu"));
                let executable = cuda_file.replace(".cu", ""); // Remove .cu for output binary

                // Save CUDA file before compilation
                if let Err(e) = write(&cuda_file, &cuda_code) {
                    eprintln!("Error writing CUDA file {}: {}", cuda_file, e);
                    exit(1);
                }
                println!("CUDA code saved to: {}", cuda_file);

                println!("Compiling CUDA with nvcc...");

                // Include `descend.cuh` directory in the compilation command
                let mut nvcc_cmd = Command::new("nvcc");
                nvcc_cmd.arg(&cuda_file)
                    .arg(&cuda_file)                   // Input CUDA file
                    .arg("-o").arg(&executable)        // Output executable
                    .arg(format!("-O{}", args.optimize)) // Pass `--optimize`
                    .arg("-I").arg("cuda-examples/")   // Include path for `descend.cuh`
                    .args(args.nvcc_flags.split_whitespace()); // Pass custom `--nvcc-flags`

                if args.arch != "none" {
                    nvcc_cmd.arg(format!("-arch={}", args.arch)); // Only add `-arch` if not "none"
                }
                    
                let nvcc_output = nvcc_cmd.output();

                match nvcc_output {
                    Ok(output) if output.status.success() => {
                        println!("Successfully compiled: {}", executable);

                        // Step 4: Run the executable if `--run` is set
                        if args.run {
                            println!("Running {}...", executable);
                            let run_output = Command::new(format!("./{}", executable)).output();

                            match run_output {
                                Ok(run) => {
                                    println!("Program output:\n{}", String::from_utf8_lossy(&run.stdout));
                                    println!("Program errors:\n{}", String::from_utf8_lossy(&run.stderr));
                                }
                                Err(e) => {
                                    eprintln!("Error running executable: {}", e);
                                    exit(1);
                                }
                            }
                        }
                    }
                    Ok(output) => {
                        eprintln!("nvcc compilation failed:\n{}", String::from_utf8_lossy(&output.stderr));
                        exit(1);
                    }
                    Err(e) => {
                        eprintln!("Failed to run nvcc: {}", e);
                        exit(1);
                    }
                }
            }
        }
        Err(ErrorReported) => {
            eprintln!("Descend compilation failed.");
            exit(1);
        }
    }
}
