#![cfg(test)]

extern crate descend;

type Res = Result<(), descend::error::ErrorReported>;
#[test]
fn scalar_mult() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/with_tys/scalar_mult.desc")?
    ))
}

#[test]
fn scale_vec_test() -> Result<(), descend::error::ErrorReported> {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/vec_scale.desc")?
    ))
}

#[test]
fn bitonic_sort() -> Result<(), descend::error::ErrorReported> {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/bitonic_sort.desc")?
    ))
}


#[test]
fn split_test() -> Result<(), descend::error::ErrorReported> {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/split_test.desc")?
    ))
}

#[test]
fn scan() -> Result<(), descend::error::ErrorReported> {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/scan.desc")?
    ))
}

#[test]
fn reduce_shared_mem() -> Result<(), descend::error::ErrorReported> {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/shared_mem_red.desc")?
    ))
}

#[test]
fn tree_reduce() -> Result<(), descend::error::ErrorReported> {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/tree_reduce_working.desc")?
    ))
}

#[test]
fn tree_reduce_sequencing_fail() -> Result<(), descend::error::ErrorReported> {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/tree_reduce.desc")?
    ))
}

#[test]
fn vector_add() -> Result<(), descend::error::ErrorReported> {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/vec_add.desc")?
    ))
}

#[ignore]
#[test]
fn warp_reduce() -> Result<(), descend::error::ErrorReported> {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/warp_reduce.desc")?
    ))
}

#[ignore]
#[test]
fn bfs() -> Result<(), descend::error::ErrorReported> {
    Ok(println!("{}", descend::compile("examples/infer/bfs.desc")?))
}

#[test]
fn computed_indexing() -> Result<(), descend::error::ErrorReported> {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/computed_indexing.desc")?
    ))
}
