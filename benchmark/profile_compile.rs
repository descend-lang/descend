use std::{env, hint::black_box};

fn main() {
    let input = env::args().nth(1).expect("missing input file");
    let iterations: usize = env::args()
        .nth(2)
        .unwrap_or_else(|| "100".to_owned())
        .parse()
        .expect("iteration count must be a non-negative integer");

    if iterations == 0 {
        print!("{}", descend::compile(&input).expect("compilation failed"));
        return;
    }

    for _ in 0..iterations {
        let cuda = descend::compile(black_box(&input)).expect("compilation failed");
        black_box(cuda);
    }
}
