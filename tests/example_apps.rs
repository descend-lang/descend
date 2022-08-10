#![cfg(test)]

extern crate descend;

type Res = Result<(), descend::error::ErrorReported>;

#[test]
#[ignore]//TODO stack overflow
fn scan() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/with_tys/scan.desc")?
    ))
}

#[test]
#[ignore]//TODO stack overflow
fn reduce_shared_mem() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/with_tys/reduce_shared_mem.desc")?
    ))
}

#[test]
#[ignore]//TODO stack overflow
fn tree_reduce() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/with_tys/tree_reduce.desc")?
    ))
}

#[test]
#[ignore]//TODO error monomorphise
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
#[ignore]//TODO error monomorphise
fn computed_indexing() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/with_tys/computed_indexing.desc")?
    ))
}
