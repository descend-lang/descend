#!/usr/bin/env bash

set -euo pipefail

usage() {
    cat <<'EOF'
Usage: PROFILE_TOOL=samply ./compare_flamegraphs.sh [INPUT] [ITERATIONS] [OUTPUT_DIR]

Compare end-to-end Descend compiler flamegraphs for main and the current HEAD.

Defaults:
  PROFILE_TOOL samply (also supports flamegraph)
  INPUT       examples/infer/matmul.desc
  ITERATIONS  100
  OUTPUT_DIR  flamegraph-results

Requirements:
  cargo install --locked samply
  perf
  clang-format

On Linux, if perf access is denied, temporarily enable it with:
  sudo sysctl -w kernel.perf_event_paranoid=-1

Set ALLOW_OUTPUT_MISMATCH=1 to profile even when generated CUDA differs.
EOF
}

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
    usage
    exit 0
fi

input="${1:-examples/infer/matmul.desc}"
iterations="${2:-100}"
output_arg="${3:-flamegraph-results}"
profile_tool="${PROFILE_TOOL:-samply}"

if [[ "$profile_tool" != "samply" && "$profile_tool" != "flamegraph" ]]; then
    echo "PROFILE_TOOL must be 'samply' or 'flamegraph', got: $profile_tool" >&2
    exit 2
fi

if [[ ! "$iterations" =~ ^[1-9][0-9]*$ ]]; then
    echo "ITERATIONS must be a positive integer, got: $iterations" >&2
    exit 2
fi

for command in cargo git rustc perf clang-format; do
    if ! command -v "$command" >/dev/null 2>&1; then
        echo "Required command not found: $command" >&2
        exit 1
    fi
done

if [[ "$profile_tool" == "samply" ]]; then
    if ! command -v samply >/dev/null 2>&1; then
        echo "samply is not installed. Run: cargo install --locked samply" >&2
        exit 1
    fi
elif ! cargo flamegraph --version >/dev/null 2>&1; then
    echo "cargo-flamegraph is not installed. Run: cargo install --locked flamegraph" >&2
    exit 1
fi

repo_root="$(git rev-parse --show-toplevel)"

if ! git -C "$repo_root" diff --quiet || ! git -C "$repo_root" diff --cached --quiet; then
    echo "Warning: tracked working-tree changes are excluded; comparing committed revisions." >&2
fi

main_commit="$(git -C "$repo_root" rev-parse main^{commit})"
arena_commit="$(git -C "$repo_root" rev-parse HEAD^{commit})"

if [[ "$output_arg" = /* ]]; then
    output_dir="$output_arg"
else
    output_dir="$repo_root/$output_arg"
fi
mkdir -p "$output_dir"
output_dir="$(cd "$output_dir" && pwd)"

tmp_root="$(mktemp -d -t descend-flamegraphs.XXXXXX)"
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

for worktree in "$main_worktree" "$arena_worktree"; do
    if [[ ! -f "$worktree/$input" ]]; then
        echo "Input does not exist at commit $(git -C "$worktree" rev-parse --short HEAD): $input" >&2
        exit 1
    fi

    cp "$repo_root/benchmark/profile_compile.rs" "$worktree/examples/profile_compile.rs"
done

metadata="$output_dir/metadata.txt"
{
    echo "main_commit=$main_commit"
    echo "arena_commit=$arena_commit"
    echo "input=$input"
    echo "iterations=$iterations"
    echo "rustc=$(rustc --version)"
    echo "cargo=$(cargo --version)"
    echo "perf=$(perf version)"
    echo "clang_format=$(clang-format --version)"
    echo "kernel=$(uname -srmo)"
    if [[ -r /proc/sys/kernel/perf_event_paranoid ]]; then
        echo "perf_event_paranoid=$(</proc/sys/kernel/perf_event_paranoid)"
    fi
} >"$metadata"

build_and_emit() {
    local worktree="$1"
    local target_dir="$2"
    local cuda_output="$3"

    (
        cd "$worktree"
        CARGO_TARGET_DIR="$target_dir" \
            CARGO_PROFILE_RELEASE_DEBUG=true \
            cargo build --quiet --offline --release --example profile_compile
        "$target_dir/release/examples/profile_compile" "$input" 0 >"$cuda_output"
    )
}

echo "Building both revisions and checking generated CUDA..."
build_and_emit "$main_worktree" "$tmp_root/target-main" "$output_dir/main.cu"
build_and_emit "$arena_worktree" "$tmp_root/target-arena" "$output_dir/arena.cu"

if ! cmp --silent "$output_dir/main.cu" "$output_dir/arena.cu"; then
    diff -u "$output_dir/main.cu" "$output_dir/arena.cu" >"$output_dir/generated-cuda.diff" || true
    if [[ "${ALLOW_OUTPUT_MISMATCH:-0}" != "1" ]]; then
        echo "Generated CUDA differs; refusing to compare unequal work." >&2
        echo "Inspect: $output_dir/generated-cuda.diff" >&2
        echo "Set ALLOW_OUTPUT_MISMATCH=1 only if the difference is understood." >&2
        exit 1
    fi
    echo "Warning: profiling despite generated CUDA differences." >&2
else
    rm -f "$output_dir/generated-cuda.diff"
fi

record_flamegraph() {
    local label="$1"
    local worktree="$2"
    local target_dir="$3"

    echo "Recording $label $profile_tool profile..."
    if [[ "$profile_tool" == "samply" ]]; then
        (
            cd "$worktree"
            samply record \
                --save-only \
                --output "$output_dir/$label.json.gz" \
                -- "$target_dir/release/examples/profile_compile" "$input" "$iterations"
        )
    else
        (
            cd "$worktree"
            CARGO_TARGET_DIR="$target_dir" \
                CARGO_PROFILE_RELEASE_DEBUG=true \
                cargo flamegraph \
                    --deterministic \
                    --example profile_compile \
                    --output "$output_dir/$label.svg" \
                    -- "$input" "$iterations"
        )
    fi
}

record_flamegraph main "$main_worktree" "$tmp_root/target-main"
record_flamegraph arena "$arena_worktree" "$tmp_root/target-arena"

echo
if [[ "$profile_tool" == "samply" ]]; then
    echo "Samply profiles created:"
    echo "  $output_dir/main.json.gz"
    echo "  $output_dir/arena.json.gz"
    echo "Open them with:"
    echo "  samply load $output_dir/main.json.gz"
    echo "  samply load $output_dir/arena.json.gz"
else
    echo "Flamegraphs created:"
    echo "  $output_dir/main.svg"
    echo "  $output_dir/arena.svg"
fi
echo "Metadata:"
echo "  $metadata"
