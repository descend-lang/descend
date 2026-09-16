use std::{env, hint::black_box};

fn main() {
    let input = env::args().nth(1).expect("missing input file");
    let iterations: usize = env::args()
        .nth(2)
        .unwrap_or_else(|| "20".to_owned())
        .parse()
        .expect("iteration count must be positive");
    let warmups: usize = env::args()
        .nth(3)
        .unwrap_or_else(|| "2".to_owned())
        .parse()
        .expect("warmup count must be non-negative");
    assert!(iterations > 0, "iteration count must be positive");

    for _ in 0..warmups {
        black_box(descend::compile_measured(&input).expect("warmup compilation failed"));
    }

    let mut source_load_ns = 0_u128;
    let mut parse_prepare_ns = 0_u128;
    let mut type_check_ns = 0_u128;
    let mut codegen_ns = 0_u128;
    let mut teardown_ns = 0_u128;
    let mut total_ns = 0_u128;
    let mut arena_allocated_bytes = None;
    let mut cuda_len = 0;

    for _ in 0..iterations {
        let sample =
            descend::compile_measured(black_box(&input)).expect("measured compilation failed");
        source_load_ns += sample.source_load.as_nanos();
        parse_prepare_ns += sample.ast_preparation.as_nanos();
        type_check_ns += sample.type_check.as_nanos();
        codegen_ns += sample.codegen.as_nanos();
        teardown_ns += sample.teardown.as_nanos();
        total_ns += sample.total.as_nanos();
        arena_allocated_bytes = sample.arena_allocated_bytes;
        cuda_len = sample.cuda.len();
        black_box(sample.cuda);
    }

    let arena_bytes = arena_allocated_bytes
        .map(|bytes| bytes.to_string())
        .unwrap_or_else(|| "null".to_owned());

    println!(
        concat!(
            "{{\"iterations\":{},\"warmups\":{},",
            "\"source_load_ns\":{},\"parse_prepare_ns\":{},",
            "\"type_check_ns\":{},\"codegen_ns\":{},",
            "\"teardown_ns\":{},\"total_ns\":{},",
            "\"arena_allocated_bytes\":{},\"cuda_len\":{}}}"
        ),
        iterations,
        warmups,
        source_load_ns,
        parse_prepare_ns,
        type_check_ns,
        codegen_ns,
        teardown_ns,
        total_ns,
        arena_bytes,
        cuda_len,
    );
}
