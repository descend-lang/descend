#!/bin/bash
INPUT="examples/infer/matmul.desc"

cargo build --profile samply

samply record -- ./target/samply/descendc emit "$INPUT"