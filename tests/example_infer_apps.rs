#![cfg(test)]

extern crate descend;

type Res = Result<(), descend::error::ErrorReported>;

#[test]
fn transpose() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/transpose.desc", None)?
    ))
}

#[test]
fn transpose_shrd_mem() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/transpose_shrd_mem.desc", None)?
    ))
}

#[test]
fn matmul() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/matmul.desc", None)?
    ))
}

#[test]
fn scale_vec() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/scale_vec.desc", None)?
    ))
}

#[test]
fn reverse_vec() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/reverse_vec.desc", None)?
    ))
}

#[ignore]
#[test]
fn bitonic_sort() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/bitonic_sort/bitonic_sort.desc", None)?
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
        descend::compile("examples/infer/scan.desc", None)?
    ))
}

#[test]
fn reduce_shared_mem() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/reduce_shared_mem.desc", None)?
    ))
}

#[test]
fn vlc_encode() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/huffman/vlc_encode.desc", None)?
    ))
}

#[test]
fn vlc_encode_cg() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/huffman/vlc_encode_cg.desc", None)?
    ))
}

#[test]
fn vlc_encode_reuse() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/huffman/vlc_encode_reuse.desc", None)?
    ))
}

#[test]
fn histogram() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/huffman/histogram.desc", None)?
    ))
}

#[test]
fn tree_reduce() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/tree_reduce.desc", None)?
    ))
}

#[test]
fn vector_add() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/vec_add.desc", None)?
    ))
}

#[ignore]
#[test]
fn bfs() -> Res {
    Ok(println!("{}", descend::compile("examples/infer/bfs.desc", None)?))
}

#[test]
fn sgemm() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/sgemm.desc", None)?
    ))
}

#[test]
fn shrd_mem_acc_equiv_exec() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/shrd_mem_acc_equiv_exec.desc", None)?
    ))
}

#[test]
fn sssp_ffi_unsafe() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/sssp-ffi.desc", None)?
    ))
}

#[test]
fn jacobisvd() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/jacobisvd.desc", None)?
    ))
}
