#!/usr/bin/env bash

set -euo pipefail

usage() {
    cat <<'EOF'
Usage: ./compare_heaptrack.sh [INPUT] [ITERATIONS] [OUTPUT_DIR]

Run Heaptrack symmetrically against main and the current HEAD using the same
repeated profile_compile driver. Generated CUDA must be identical.

Defaults:
  INPUT       examples/infer/matmul.desc
  ITERATIONS  2
  OUTPUT_DIR  heaptrack-results
EOF
}

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
    usage
    exit 0
fi

input="${1:-examples/infer/matmul.desc}"
iterations="${2:-2}"
output_arg="${3:-heaptrack-results}"

if [[ ! "$iterations" =~ ^[1-9][0-9]*$ ]]; then
    echo "ITERATIONS must be a positive integer, got: $iterations" >&2
    exit 2
fi

for command in cargo git rustc clang-format heaptrack heaptrack_print; do
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

tmp_root="$(mktemp -d -t descend-heaptrack.XXXXXX)"
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

prepare_and_build() {
    local worktree="$1"
    local target_dir="$2"
    local cuda_output="$3"

    if [[ ! -f "$worktree/$input" ]]; then
        echo "Input does not exist at $(git -C "$worktree" rev-parse --short HEAD): $input" >&2
        exit 1
    fi
    cp "$repo_root/benchmark/profile_compile.rs" "$worktree/examples/profile_compile.rs"
    (
        cd "$worktree"
        CARGO_TARGET_DIR="$target_dir" \
            CARGO_PROFILE_RELEASE_DEBUG=true \
            cargo build --quiet --offline --release --example profile_compile
        "$target_dir/release/examples/profile_compile" "$input" 0
    ) >"$cuda_output"
}

echo "Building both revisions and checking generated CUDA..."
prepare_and_build "$main_worktree" "$tmp_root/target-main" "$output_dir/main.cu"
prepare_and_build "$arena_worktree" "$tmp_root/target-arena" "$output_dir/arena.cu"

if ! cmp --silent "$output_dir/main.cu" "$output_dir/arena.cu"; then
    diff -u "$output_dir/main.cu" "$output_dir/arena.cu" >"$output_dir/generated-cuda.diff" || true
    echo "Generated CUDA differs; refusing to profile unequal work." >&2
    echo "Inspect: $output_dir/generated-cuda.diff" >&2
    exit 1
fi
rm -f "$output_dir/generated-cuda.diff"

record_heaptrack() {
    local label="$1"
    local worktree="$2"
    local target_dir="$3"
    local output_template="$output_dir/$label.%p.heaptrack"
    local marker="$tmp_root/$label.heaptrack-started"
    local profile_list="$output_dir/$label.profiles.txt"

    echo "Recording $label Heaptrack profile..."
    touch "$marker"
    (
        cd "$worktree"
        heaptrack -o "$output_template" \
            "$target_dir/release/examples/profile_compile" "$input" "$iterations"
    ) >"$output_dir/$label.heaptrack.log" 2>&1

    : >"$profile_list"
    while IFS= read -r profile; do
        echo "$profile" >>"$profile_list"
        heaptrack_print -l -f "$profile" >"${profile%.*}.txt"
    done < <(
        find "$output_dir" -maxdepth 1 -type f \
            \( -name "$label.*.heaptrack.gz" -o -name "$label.*.heaptrack.zst" \) \
            -newer "$marker" | sort
    )

    if [[ ! -s "$profile_list" ]]; then
        echo "Heaptrack did not produce a recognized .gz or .zst profile for $label." >&2
        exit 1
    fi
}

record_heaptrack main "$main_worktree" "$tmp_root/target-main"
record_heaptrack arena "$arena_worktree" "$tmp_root/target-arena"

main_profiles="$(wc -l <"$output_dir/main.profiles.txt")"
arena_profiles="$(wc -l <"$output_dir/arena.profiles.txt")"

{
    echo "main_commit=$main_commit"
    echo "arena_commit=$arena_commit"
    echo "input=$input"
    echo "iterations=$iterations"
    echo "main_profile_files=$main_profiles"
    echo "arena_profile_files=$arena_profiles"
    echo "rustc=$(rustc --version)"
    echo "cargo=$(cargo --version)"
    echo "heaptrack=$(heaptrack --version 2>&1 | head -n 1)"
    echo "heaptrack_print=$(heaptrack_print --version 2>&1 | head -n 1)"
    echo "clang_format=$(clang-format --version)"
    echo "kernel=$(uname -srmo)"
    echo "child_process_note=Inspect profile lists and summaries for clang-format; LD_PRELOAD inheritance may profile children separately."
} >"$output_dir/metadata.txt"

echo "Heaptrack profiles and text summaries: $output_dir"
echo "Metadata: $output_dir/metadata.txt"
