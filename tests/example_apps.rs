#![cfg(test)]

extern crate descend;

type Res = Result<(), descend::error::ErrorReported>;

#[test]
fn split_test() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/with_tys/split_test.desc")?
    ))
}

#[test]
fn scan() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/with_tys/scan.desc")?
    ))
}

#[test]
fn reduce_shared_mem() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/with_tys/shared_mem_red.desc")?
    ))
}

#[test]
fn tree_reduce() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/with_tys/tree_reduce.desc")?
    ))
}

#[test]
fn vector_add() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/with_tys/vec_add.desc")?
    ))
}

#[ignore]
#[test]
fn warp_reduce() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/with_tys/warp_reduce.desc")?
    ))
}

#[ignore]
#[test]
fn bfs() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/with_tys/bfs.desc")?
    ))
}

#[test]
fn computed_indexing() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/with_tys/computed_indexing.desc")?
    ))
}
