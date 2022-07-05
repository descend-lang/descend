#![cfg(test)]

extern crate descend;

type Res = Result<(), descend::error::ErrorReported>;

#[test]
fn gaussian() -> Res {
    Ok(println!(
        "{}",
        descend::compile("examples/rodinia/gaussian.desc")?
    ))
}
