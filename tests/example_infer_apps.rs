#![cfg(test)]

extern crate descend;

type Res = Result<(), descend::error::ErrorReported>;

#[test]
fn transpose() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/transpose.desc")?
    ))
}

#[test]
fn transpose_shrd_mem() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/transpose_shrd_mem.desc")?
    ))
}

#[test]
fn matmul() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/matmul.desc")?
    ))
}

#[test]
fn scale_vec() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/scale_vec.desc")?
    ))
}

#[test]
fn reverse_vec() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/reverse_vec.desc")?
    ))
}

#[ignore]
#[test]
fn bitonic_sort() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/bitonic_sort/bitonic_sort.desc")?
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
fn vlc_encode() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/huffman/vlc_encode.desc")?
    ))
}

#[test]
fn vlc_encode_cg() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/huffman/vlc_encode_cg.desc")?
    ))
}

#[test]
fn vlc_encode_reuse() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/huffman/vlc_encode_reuse.desc")?
    ))
}

#[test]
fn histogram() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/huffman/histogram.desc")?
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
