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
fn ext_transpose_shrd_mem() -> Res {
    use descend::ast::{ArgKinded, BinOpNat, DataTy, DataTyKind, Nat, Provenance, ScalarTy};
    use descend::ty_check::ext_ty_check_kernel;

    let source = descend::parser::SourceCode::from_file("examples/infer/ext_transpose_shrd_mem.desc")?;
    let mut compil_unit = descend::parser::parse(&source)?;
    let n256 = Nat::Lit(256);
    let n32 = Nat::Lit(32);
    let n8 = Nat::Lit(8);
    let n256x32 = Nat::BinOp(
        BinOpNat::Mul,
        Box::new(Nat::Lit(256)),
        Box::new(Nat::Lit(32)),
    );
    let gen_args = vec![
        ArgKinded::Nat(n256),
        ArgKinded::Nat(n32),
        ArgKinded::Nat(n8),
        ArgKinded::Nat(n256x32.clone()),
        ArgKinded::Provenance(Provenance::Value("dummy0".to_string())),
        ArgKinded::Provenance(Provenance::Value("dummy1".to_string())),
    ];
    descend::ty_check::ext_ty_check_kernel(&mut compil_unit, "par_transpose", &gen_args)
        .map_err(|err| err.emit(&source))?;
    let code = descend::codegen::ext_gen(
        &compil_unit,
        "par_transpose",
        vec![DataTy::new(DataTyKind::Array(
            Box::new(DataTy::new(DataTyKind::Array(
                Box::new(DataTy::new(DataTyKind::Scalar(ScalarTy::F32))),
                n256x32.clone(),
            ))),
            n256x32,
        ))],
    );
    Ok(println!("{}", code))
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

#[ignore]
#[test]
fn sgemm() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/sgemm.desc")?
    ))
}

#[test]
fn shrd_mem_acc_equiv_exec() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/shrd_mem_acc_equiv_exec.desc")?
    ))
}

#[test]
fn sssp_ffi_unsafe() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/sssp-ffi.desc")?
    ))
}

#[test]
fn jacobisvd() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/infer/jacobisvd.desc")?
    ))
}
