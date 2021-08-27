#![cfg(test)]

extern crate descend;

use descend::parser::{parse, SourceCode};
use descend::ty_check;

#[test]
fn warp_reduce() -> Result<(), descend::error::ErrorReported> {
    Ok(println!(
        "{}",
        descend::compile("examples/warp_reduce.desc")?
    ))
}

#[test]
fn scan() -> Result<(), descend::error::ErrorReported> {
    Ok(println!("{}", descend::compile("examples/scan.desc")?))
}

#[test]
fn reduce_shared_mem2() -> Result<(), descend::error::ErrorReported> {
    panic!("Generates the wrong code.");
    Ok(println!(
        "{}",
        descend::compile("examples/shared_mem_red2.desc")?
    ))
}

#[test]
fn reduce_shared_mem() -> Result<(), descend::error::ErrorReported> {
    println!("{}", descend::compile("examples/shared_mem_red.desc")?);
    panic!("Wrong code")
}

#[test]
fn tree_reduce() -> Result<(), descend::error::ErrorReported> {
    println!("{}", descend::compile("examples/tree_reduce.desc")?);
    panic!("Wrong code")
}

#[test]
fn vector_add() -> Result<(), descend::error::ErrorReported> {
    Ok(println!("{}", descend::compile("examples/vec_add.desc")?))
}

#[test]
fn bfs() -> Result<(), descend::error::ErrorReported> {
    Ok(println!("{}", descend::compile("examples/bfs.desc")?))
}
