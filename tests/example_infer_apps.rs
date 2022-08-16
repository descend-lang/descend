#![cfg(test)]

extern crate descend;

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
#[ignore] //FIXME: Some codegen error
fn scan() -> Res {
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
