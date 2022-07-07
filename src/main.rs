use descend::compile;
use std::{env, fs, process::Command};
use std::io::{self, Write};

fn main() {
   let mut args: Vec<String> = env::args().rev().collect();

   // Popfile path
   args.pop();

   // Get mode 
   let mode = args.pop().expect("[Err] Missing mode!");
   let mut input_file = "".to_owned();
   let build_dir = "build";
   let mut cuda_output_file = build_dir.to_owned() + "/output.cu";
   let mut compile_file = cuda_output_file.to_owned();
   let mut binary_output_file = build_dir.to_owned() + "/a.out"; 
   let mut custom_final_output_file = false;
   let mut final_output_file = "".to_string();
   let mut descend_header = "cuda-examples/descend.cuh".to_string();
   let mut disable_transpile = false;

   while !args.is_empty() {
      let curr_word = args.pop().expect("Error while parsing arguments");
      match curr_word.as_str() {
         "-o" => {
            final_output_file = args.pop().expect("-o is missing file path");
            custom_final_output_file = true;
         }
         "-dh" => {
            descend_header = args.pop().expect("Expected path to descend_header");
         }
         "-cf" => 
            compile_file = args.pop().expect("-cf is missing file path"),
         "-nt" => 
            disable_transpile = true,
         _ => input_file = curr_word.clone()
      }
   }

   fs::create_dir_all(build_dir).expect("Could not create build_dir");
   fs::copy(descend_header.to_owned(), build_dir.to_owned() + "/descend.cuh").expect("Copy of descend header failed");

   match mode.as_str() {
      "transpile" => {
         if custom_final_output_file {
            cuda_output_file = final_output_file.to_owned();
         }
         transpile(input_file.to_owned(), cuda_output_file.to_string()).expect("Compiliation failed");
      }
      "compile" | "run" => {
         if custom_final_output_file {
            binary_output_file = final_output_file.to_owned();
         }

         if !disable_transpile {
            transpile(input_file.to_string(), cuda_output_file.to_string()).expect("Compiliation failed");
         }

         fs::copy(compile_file.to_owned(), build_dir.to_owned() + "/main.cu").expect("Could not copy compile_file");
         compile_to_binary(build_dir.to_owned() + "/main.cu", binary_output_file.to_string()).expect("NVCC Failed");
         if mode == "run" {
            run(binary_output_file.to_string()).expect("Execution failed");
         }
      }
      _ => panic!("Bad mode")
   }
}

fn transpile(input_file: String, output_file: String) -> Result<(), String> {
   let output = compile(input_file.as_str());
   let string_outputt = output.ok();
   if string_outputt.is_some() {
      fs::write(output_file.clone(), string_outputt.unwrap()).expect("Could not write to output_file");
      Ok(())
   } else {
      Err("Transpilation failed".to_string())
   }
}

fn compile_to_binary(compile_file: String, output_file: String) -> Result<(), String> {
   println!("[*] Starting to compile");
   // if compile_file.len() == 0 {
   //    compile_file = cuda_output_file;
   // }
   let output = Command::new("sh")
      .arg("-c")
      .arg(format!("nvcc {compile_file} -o {output_file} --extended-lambda"))
      .output()
      .expect("Failed to compile to binary");
   io::stdout().write_all(&output.stdout).unwrap();
   io::stderr().write_all(&output.stderr).unwrap();

   if output.status.code().expect("Did not get exit code") != 0 {
      Err("[!] Compiliation failed!".to_string())
   } else {
      Ok(())
   }
}

fn run(binary_path: String) -> Result<(), String> {
   println!("[!] Start executing");
   let output = Command::new("sh")
      .arg("-c")
      .arg(format!("./{binary_path}"))
      .output()
      .expect("Program executed with non zero exit code");
   io::stdout().write_all(&output.stdout).unwrap();
   io::stderr().write_all(&output.stderr).unwrap();
   if output.status.code().expect("Did not get exit code") != 0 {
      println!("[!] Running failed!");
      Err("Execution failed".to_string())
   } else {
      println!("[!] Execution finished");
      Ok(())
   }
}
