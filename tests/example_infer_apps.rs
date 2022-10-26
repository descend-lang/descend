#![cfg(test)]

extern crate descend;

use std::io::Write;
use std::process::{Command, Stdio};
use std::env;
use std::fs;

type Res = Result<(), descend::error::ErrorReported>;

#[test]
fn scale_vec() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/scale_vec.desc")?
    ))
}

#[ignore]
fn bitonic_sort_split_blocks() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/bitonic_sort/bitonic_sort.desc")?
    ))
}

#[ignore]
fn bitonic_sort_shrd_mem() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/bitonic_sort/bitonic_sort_shrd_mem.desc")?
    ))
}

#[test]
fn scan() -> Res {
    eprintln!(
        "Breaks because there are name clashes between nats and type variables.\n \
    This is not the case for the fully typed version.\n\
    Solution: Keep track of the kinded arguments for dependent function separately depending on their kinds."
    );
    Ok(println!(
        "{}",
        descend::compile("examples/infer/scan.desc")?
    ))
}

#[test]
fn reduce_shared_mem() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/reduce_shared_mem.desc")?
    ))
}

#[test]
fn tree_reduce() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/tree_reduce.desc")?
    ))
}

#[test]
fn vector_add() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/vec_add.desc")?
    ))
}

#[ignore]
#[test]
fn warp_reduce() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/warp_reduce.desc")?
    ))
}

#[ignore]
#[test]
fn bfs() -> Res {
    Ok(println!("{}", descend::compile("examples/infer/bfs.desc")?))
}

#[test]
fn computed_indexing() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/computed_indexing.desc")?
    ))
}

#[test]
fn vec_add_compile_test() -> Res {
    let compiled = descend::compile("examples/infer/vec_add_lion.desc")?;
    let file_path = "cuda-examples/vec_add_cuda.cu";

    fs::write(file_path, descend::compile("examples/infer/vec_add_lion.desc")?)
        .expect("Cant write in the file");



    Ok(println!("{}", compiled))
}

// #[test]
// fn vec_add_test() -> Res {
//     let compiled = descend::compile("examples/infer/vec_add_lion.desc")?;
//     let a = [1, 2, 3, 4, 5, 6];
//     let b = [3, 4, 5, 6, 7, 8];
//     let res = [4, 6, 8, 10, 12, 14];
//
//     let mut compile_unit = Command::new("nvcc ")
//         .stdin(Stdio:piped())
//         .stdin(Stdio:piped())
//         .spawn()
//         .expect("Can't compile the CUDA nvcc Code");
//
//
//     if let Some(mut stdin) = compile_unit.stdin.take() {
//         stdin
//             .write_all()
//             .
//     }
// }
