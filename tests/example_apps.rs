#![cfg(test)]

extern crate descend;

#[test]
fn scan() -> Result<(), descend::error::ErrorReported> {
    Ok(println!("{}", descend::compile("examples/scan.desc")?))
}

#[test]
fn reduce_shared_mem() -> Result<(), descend::error::ErrorReported> {
    Ok(println!(
        "{}",
        descend::compile("examples/shared_mem_red.desc")?
    ))
}

#[test]
fn tree_reduce() -> Result<(), descend::error::ErrorReported> {
    Ok(println!(
        "{}",
        descend::compile("examples/tree_reduce.desc")?
    ))
}

#[test]
fn vector_add() -> Result<(), descend::error::ErrorReported> {
    Ok(println!("{}", descend::compile("examples/vec_add.desc")?))
}

#[ignore]
#[test]
fn warp_reduce() -> Result<(), descend::error::ErrorReported> {
    Ok(println!(
        "{}",
        descend::compile("examples/warp_reduce.desc")?
    ))
}

#[test]
fn bfs() -> Result<(), descend::error::ErrorReported> {
    Ok(println!("{}", descend::compile("examples/bfs_copy.desc")?))
}

#[test]
fn bfs_working() -> Result<(), descend::error::ErrorReported> {
    Ok(println!(
        "{}",
        descend::compile("examples/bfs_copy_working.desc")?
    ))
}

#[test]
fn computed_indexing() -> Result<(), descend::error::ErrorReported> {
    Ok(println!(
        "{}",
        descend::compile("examples/computed_indexing.desc")?
    ))
}
