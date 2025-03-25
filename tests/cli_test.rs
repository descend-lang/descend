use assert_cmd::Command;
use predicates::prelude::*;

#[test]
fn test_emit_cuda_on_transpose_desc() {
    let mut cmd = Command::cargo_bin("descendc").expect("Failed to find descendc binary");

    cmd.arg("emit").arg("examples/infer/transpose.desc");

    cmd.assert()
       .success()
       .stdout(predicate::str::contains("Generated CUDA Code"));
}
