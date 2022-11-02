#![cfg(test)]

extern crate descend;

type Res = Result<(), descend::error::ErrorReported>;

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
        descend::compile("examples/with_tys/reduce_shared_mem.desc")?
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
