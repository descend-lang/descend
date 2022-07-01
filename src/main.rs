use descend::compile;
use std::{env, fs, process::Command};
use std::io::{self, Write};

// fn fmain() {
//    let mut args: Vec<String> = env::args().rev().collect();
// 
//    // Popfile path
//    args.pop();
// 
//    // Get mode 
//    let mode = args.pop().expect("[Err] Missing mode!");
// 
//    let transpile = false;
// 
//    match mode {
//       "transpile" => {
//          while !args.is_empty() {
//             let curr_word = args.pop().expect("Unexpected End of arguments");
//             match curr_word.as_str() {
//                "-o" => 
//             }
//          }
//          let output_file = args.pop();
//       }
//    }
// }

fn main() {
   // let output = compile("examples/infer/parral-prefix.desc");
   // Because pop takes the last element, we need to reverse
   let mut args: Vec<String> = env::args().rev().collect();
   println!("{:?}", args);

   let mut output_file = "a.out".to_string();
   let mut cuda_output_file = "cuda-examples/output.cu".to_string();
   let mut input_file = "".to_string();
   let mut compile_flag = false;
   let mut run_flag = false;
   let mut compile_file = "".to_string();
   // Pop filepath
   args.pop();

   while !args.is_empty() {
      let curr_word = args.pop().expect("Error while parsing arguments");
      match curr_word.as_str() {
         "-o" => 
            output_file = args.pop().expect("-o is missing file path"),
         "-co" => 
            cuda_output_file = args.pop().expect("-co is missing file path"),
         "-cf" => 
            compile_file = args.pop().expect("-cf is missing file path"),
         "-c" => compile_flag = true,
         "-r" => run_flag = true,
         _ => input_file = curr_word
      }
   }

   let output = compile(input_file.as_str());
   let string_outputt = output.ok();
   if string_outputt.is_some() {
      fs::write(cuda_output_file.clone(), string_outputt.unwrap()).expect("Could not write to output_file");
   } else {
      println!("[!] Transpilation failed");
      return 
   }
   if compile_flag || run_flag {
      println!("[!] Starting to compile");
      if compile_file.len() == 0 {
         compile_file = cuda_output_file;
      }
      let output = Command::new("sh")
         .arg("-c")
         .arg(format!("nvcc {compile_file} -o {output_file} --extended-lambda"))
         .output()
         .expect("Failed to compile to binary");
      io::stdout().write_all(&output.stdout).unwrap();
      io::stderr().write_all(&output.stderr).unwrap();
   
      if output.status.code().expect("Did not get exit code") != 0 {
         println!("[!] Compiliation failed!");
         return
      } else {
         println!("[!] Compiliation finished")
      }
   }
   
   if run_flag {
      println!("[!] Start executing");
      let output = Command::new("sh")
         .arg("-c")
         .arg(format!("./{output_file}"))
         .output()
         .expect("Program executed with non zero exit code");
      io::stdout().write_all(&output.stdout).unwrap();
      io::stderr().write_all(&output.stderr).unwrap();
      if output.status.code().expect("Did not get exit code") != 0 {
         println!("[!] Running failed!");
      } else {
         println!("[!] Execution finished")
      }
   }
}

