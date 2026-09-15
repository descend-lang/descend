# Compiler performance comparisons

All comparison scripts build `main` and the current committed `HEAD` in
temporary detached worktrees with separate target directories, compare
generated CUDA byte-for-byte, and leave the real branches untouched. Tracked
working-tree changes are reported and excluded from commit-to-commit
measurements. The Samply and Heaptrack workflows inject the same minimal repeat
driver so they can also profile older revisions.

Phase measurement uses the feature-gated `descend::compile_measured` API on the
arena branch. Benchmark code stays on this branch: `compare_performance.sh`
copies the drivers and `benchmark/main_compile_measured.rs` into its temporary
detached `main` worktree. The adapter is the unmodified main compiler pipeline
with phase observation around it and reports no arena byte count. Neither the
real `main` worktree nor the real feature worktree is changed. If main's
compiler pipeline changes, update the adapter before accepting new results.

## Runtime and exact allocator counts

```console
./compare_performance.sh examples/infer/matmul.desc 20 6 performance-results
```

This runs six independent processes per revision in alternating order, with
two warmups and 20 measured compilations in each process. Timing and allocation
counting use separate executables so the allocator's atomic counters do not
distort the runtime measurements. It pins both revisions to the first allowed
CPU by default; set `BENCH_CPU` to override it. The output contains raw JSONL,
environment metadata, generated CUDA, and a Markdown table of medians with
bootstrap intervals.

`profile_metrics` deliberately reports no timings: its atomic operations add
substantial overhead when a revision makes many allocator calls. Runtime data
comes only from the uninstrumented `profile_timings` executable.

The temporary benchmark API measures source loading, parsing plus AST
preparation, type checking, code generation including the external
`clang-format` process, and destruction. On the arena revision it also records
`Bump::allocated_bytes()`. Parsing and AST preparation are still combined, so
the current harness does not isolate PEG parsing, heap-to-arena conversion, and
arena normalization from one another.

The counting global allocator wraps `std::alloc::System` and counts allocation,
zeroed-allocation, reallocation, and deallocation requests without allocating
inside those methods. Requested and live bytes use Rust `Layout` sizes; they
are not RSS or allocator-resident sizes. Allocations made inside the external
`clang-format` child are not included.

## Heaptrack

```console
./compare_heaptrack.sh examples/infer/matmul.desc 2 heaptrack-results
```

Heaptrack is intentionally repeated only twice by default because allocation-
heavy revisions can generate multi-million-event traces per compilation. The
script supports both `.zst` and `.gz` Heaptrack output, saves the raw profiles,
runs `heaptrack_print -l`, and records the profile list and environment.

## Samply

```console
./compare_flamegraphs.sh examples/infer/matmul.desc 500 flamegraph-results
```

Samply explains sampled CPU attribution but does not provide exact allocator
counts. Compare absolute Call Tree values where available; do not treat missing
allocator samples as proof that no allocator call occurred.
