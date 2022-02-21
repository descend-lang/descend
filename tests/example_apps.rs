#![cfg(test)]

extern crate descend;

type Res = Result<(), descend::error::ErrorReported>;
#[test]
fn scalar_mult() -> Res{
   Ok(println!("{}", descend::compile("examples/with_tys/scalar_mult.desc")?))
}

#[test]
fn split_test() -> Result<(), descend::error::ErrorReported> {
    Ok(println!(
        "{}",
        descend::compile("examples/with_tys/split_test.desc")?
    ))
}

#[test]
fn scan() -> Result<(), descend::error::ErrorReported> {
    Ok(println!(
        "{}",
        descend::compile("examples/with_tys/scan.desc")?
    ))
}

#[test]
fn reduce_shared_mem() -> Result<(), descend::error::ErrorReported> {
    Ok(println!(
        "{}",
        descend::compile("examples/with_tys/shared_mem_red.desc")?
    ))
}

#[test]
fn tree_reduce() -> Result<(), descend::error::ErrorReported> {
    Ok(println!(
        "{}",
        descend::compile("examples/with_tys/tree_reduce_working.desc")?
    ))
}

#[test]
fn tree_reduce_sequencing_fail() -> Result<(), descend::error::ErrorReported> {
    Ok(println!(
        "{}",
        descend::compile("examples/with_tys/tree_reduce.desc")?
    ))
}

#[test]
fn vector_add() -> Result<(), descend::error::ErrorReported> {
    Ok(println!(
        "{}",
        descend::compile("examples/with_tys/vec_add.desc")?
    ))
}

#[ignore]
#[test]
fn warp_reduce() -> Result<(), descend::error::ErrorReported> {
    Ok(println!(
        "{}",
        descend::compile("examples/with_tys/warp_reduce.desc")?
    ))
}

#[ignore]
#[test]
fn bfs() -> Result<(), descend::error::ErrorReported> {
    Ok(println!(
        "{}",
        descend::compile("examples/with_tys/bfs.desc")?
    ))
}

#[test]
fn computed_indexing() -> Result<(), descend::error::ErrorReported> {
    Ok(println!(
        "{}",
        descend::compile("examples/with_tys/computed_indexing.desc")?
    ))
}
