#!/usr/bin/env bash

set -euo pipefail

usage() {
    cat <<'EOF'
Usage: ./compare_performance.sh [INPUT] [ITERATIONS] [PROCESSES] [OUTPUT_DIR]

Compare coarse compiler phases and exact System-allocator requests for main and
the current HEAD. Each revision is measured in a temporary detached worktree.

Defaults:
  INPUT       examples/infer/matmul.desc
  ITERATIONS  20 per process
  PROCESSES   6 per revision (must be at least 5)
  OUTPUT_DIR  performance-results

Set BENCH_CPU to pin measurements to a particular CPU. Otherwise the first CPU
allowed for this process is used when taskset is available.
EOF
}

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
    usage
    exit 0
fi

input="${1:-examples/infer/matmul.desc}"
iterations="${2:-20}"
processes="${3:-6}"
output_arg="${4:-performance-results}"

if [[ ! "$iterations" =~ ^[1-9][0-9]*$ ]]; then
    echo "ITERATIONS must be a positive integer, got: $iterations" >&2
    exit 2
fi
if [[ ! "$processes" =~ ^[0-9]+$ ]] || ((processes < 5)); then
    echo "PROCESSES must be an integer of at least 5, got: $processes" >&2
    exit 2
fi

for command in cargo git rustc clang-format python3; do
    if ! command -v "$command" >/dev/null 2>&1; then
        echo "Required command not found: $command" >&2
        exit 1
    fi
done

repo_root="$(git rev-parse --show-toplevel)"
main_commit="$(git -C "$repo_root" rev-parse main^{commit})"
arena_commit="$(git -C "$repo_root" rev-parse HEAD^{commit})"

if [[ "$output_arg" = /* ]]; then
    output_dir="$output_arg"
else
    output_dir="$repo_root/$output_arg"
fi
mkdir -p "$output_dir"
output_dir="$(cd "$output_dir" && pwd)"

if ! git -C "$repo_root" diff --quiet || ! git -C "$repo_root" diff --cached --quiet; then
    echo "Warning: tracked working-tree changes are excluded; comparing committed revisions." >&2
fi

tmp_root="$(mktemp -d -t descend-performance.XXXXXX)"
main_worktree="$tmp_root/main"
arena_worktree="$tmp_root/arena"

cleanup() {
    git -C "$repo_root" worktree remove --force "$main_worktree" >/dev/null 2>&1 || true
    git -C "$repo_root" worktree remove --force "$arena_worktree" >/dev/null 2>&1 || true
    rm -rf "$tmp_root"
}
trap cleanup EXIT

git -C "$repo_root" worktree add --quiet --detach "$main_worktree" "$main_commit"
git -C "$repo_root" worktree add --quiet --detach "$arena_worktree" "$arena_commit"

prepare_worktree() {
    local label="$1"
    local worktree="$2"

    if [[ ! -f "$worktree/$input" ]]; then
        echo "Input does not exist in $label revision: $input" >&2
        exit 1
    fi
    for driver in benchmark/profile_compile.rs benchmark/profile_metrics.rs benchmark/profile_timings.rs; do
        if [[ ! -f "$repo_root/$driver" ]]; then
            echo "Current benchmark branch does not contain $driver." >&2
            exit 1
        fi
    done

    if [[ "$label" == "main" ]]; then
        if [[ ! -f "$repo_root/benchmark/main_compile_measured.rs" ]]; then
            echo "Missing benchmark/main_compile_measured.rs baseline adapter." >&2
            exit 1
        fi
        mkdir -p "$worktree/examples"
        cp "$repo_root/benchmark/profile_compile.rs" "$worktree/examples/profile_compile.rs"
        cp "$repo_root/benchmark/profile_metrics.rs" "$worktree/examples/profile_metrics.rs"
        cp "$repo_root/benchmark/profile_timings.rs" "$worktree/examples/profile_timings.rs"
        cp "$repo_root/benchmark/main_compile_measured.rs" "$worktree/src/lib.rs"
    else
        if ! grep -q '^bench-internals[[:space:]]*=' "$worktree/Cargo.toml"; then
            echo "$label revision does not provide the bench-internals feature." >&2
            exit 1
        fi
        for driver in benchmark/profile_compile.rs benchmark/profile_metrics.rs benchmark/profile_timings.rs; do
            if [[ ! -f "$worktree/$driver" ]]; then
                echo "$label revision does not contain $driver." >&2
                exit 1
            fi
        done
    fi
}

prepare_worktree main "$main_worktree"
prepare_worktree arena "$arena_worktree"

build_revision() {
    local label="$1"
    local worktree="$2"
    local target_dir="$3"
    (
        cd "$worktree"
        if [[ "$label" == "main" ]]; then
            CARGO_TARGET_DIR="$target_dir" \
                CARGO_PROFILE_RELEASE_DEBUG=true \
                cargo build --quiet --offline --release \
                    --example profile_compile --example profile_metrics --example profile_timings
        else
            CARGO_TARGET_DIR="$target_dir" \
                CARGO_PROFILE_RELEASE_DEBUG=true \
                cargo build --quiet --offline --release \
                    --features bench-internals \
                    --example profile_compile --example profile_metrics --example profile_timings
        fi
    )
}

echo "Building instrumented revisions..."
build_revision main "$main_worktree" "$tmp_root/target-main"
build_revision arena "$arena_worktree" "$tmp_root/target-arena"

(
    cd "$main_worktree"
    "$tmp_root/target-main/release/examples/profile_compile" "$input" 0
) >"$output_dir/main.cu"
(
    cd "$arena_worktree"
    "$tmp_root/target-arena/release/examples/profile_compile" "$input" 0
) >"$output_dir/arena.cu"

if ! cmp --silent "$output_dir/main.cu" "$output_dir/arena.cu"; then
    diff -u "$output_dir/main.cu" "$output_dir/arena.cu" >"$output_dir/generated-cuda.diff" || true
    echo "Generated CUDA differs; refusing to measure unequal work." >&2
    echo "Inspect: $output_dir/generated-cuda.diff" >&2
    exit 1
fi
rm -f "$output_dir/generated-cuda.diff"

bench_cpu="${BENCH_CPU:-}"
if [[ -z "$bench_cpu" && -r /proc/self/status ]] && command -v taskset >/dev/null 2>&1; then
    allowed_cpus="$(awk '/Cpus_allowed_list/ { print $2 }' /proc/self/status)"
    bench_cpu="${allowed_cpus%%[-,]*}"
fi

run_one() {
    local label="$1"
    local worktree="$2"
    local target_dir="$3"
    local driver="$4"
    local output="$5"
    local binary="$target_dir/release/examples/$driver"

    echo "Measuring $label with $driver..."
    if [[ -n "$bench_cpu" ]] && command -v taskset >/dev/null 2>&1; then
        (cd "$worktree" && taskset -c "$bench_cpu" "$binary" "$input" "$iterations" 2) >>"$output"
    else
        (cd "$worktree" && "$binary" "$input" "$iterations" 2) >>"$output"
    fi
}

main_timing_raw="$output_dir/main-timings.jsonl"
arena_timing_raw="$output_dir/arena-timings.jsonl"
main_alloc_raw="$output_dir/main-allocations.jsonl"
arena_alloc_raw="$output_dir/arena-allocations.jsonl"
: >"$main_timing_raw"
: >"$arena_timing_raw"
: >"$main_alloc_raw"
: >"$arena_alloc_raw"

for ((process = 1; process <= processes; process++)); do
    if ((process % 2 == 1)); then
        run_one main "$main_worktree" "$tmp_root/target-main" profile_timings "$main_timing_raw"
        run_one arena "$arena_worktree" "$tmp_root/target-arena" profile_timings "$arena_timing_raw"
        run_one main "$main_worktree" "$tmp_root/target-main" profile_metrics "$main_alloc_raw"
        run_one arena "$arena_worktree" "$tmp_root/target-arena" profile_metrics "$arena_alloc_raw"
    else
        run_one arena "$arena_worktree" "$tmp_root/target-arena" profile_timings "$arena_timing_raw"
        run_one main "$main_worktree" "$tmp_root/target-main" profile_timings "$main_timing_raw"
        run_one arena "$arena_worktree" "$tmp_root/target-arena" profile_metrics "$arena_alloc_raw"
        run_one main "$main_worktree" "$tmp_root/target-main" profile_metrics "$main_alloc_raw"
    fi
done

{
    echo "main_commit=$main_commit"
    echo "arena_commit=$arena_commit"
    echo "input=$input"
    echo "iterations_per_process=$iterations"
    echo "processes_per_revision=$processes"
    echo "warmups_per_process=2"
    echo "bench_cpu=${bench_cpu:-unpinned}"
    echo "rustc=$(rustc --version)"
    echo "cargo=$(cargo --version)"
    echo "clang_format=$(clang-format --version)"
    echo "kernel=$(uname -srmo)"
    echo "codegen_includes_external_clang_format=true"
    echo "counting_allocator_includes_clang_format_child=false"
    echo "timings_use_counting_allocator=false"
    echo "main_instrumentation=temporary benchmark/main_compile_measured.rs adapter"
} >"$output_dir/metadata.txt"

python3 "$repo_root/benchmark/summarize_metrics.py" \
    "$main_timing_raw" "$arena_timing_raw" \
    "$main_alloc_raw" "$arena_alloc_raw" "$output_dir/summary.md"

echo "Raw timing measurements: $main_timing_raw and $arena_timing_raw"
echo "Raw allocation measurements: $main_alloc_raw and $arena_alloc_raw"
echo "Summary: $output_dir/summary.md"
echo "Metadata: $output_dir/metadata.txt"
