#!/usr/bin/env python3

import json
import random
import statistics
import sys
from pathlib import Path


TIME_FIELDS = [
    ("Source loading", "source_load_ns"),
    ("Parse + AST preparation", "parse_prepare_ns"),
    ("Type checking", "type_check_ns"),
    ("Code generation + clang-format", "codegen_ns"),
    ("Teardown", "teardown_ns"),
    ("Compiler core (in-memory source onward)", "compiler_core_ns"),
    ("File-to-formatted-CUDA", "total_ns"),
]


def load(path):
    with Path(path).open(encoding="utf-8") as stream:
        return [json.loads(line) for line in stream if line.strip()]


def per_iteration(rows, field):
    if field == "compiler_core_ns":
        return [
            (row["total_ns"] - row["source_load_ns"]) / row["iterations"]
            for row in rows
        ]
    return [row[field] / row["iterations"] for row in rows]


def median_change(main, arena):
    main_median = statistics.median(main)
    arena_median = statistics.median(arena)
    if main_median == 0:
        change = 0.0 if arena_median == 0 else None
    else:
        change = (arena_median / main_median - 1.0) * 100.0
    return main_median, arena_median, change


def bootstrap_change(main, arena, samples=5000):
    rng = random.Random(0xD35CE7D)
    changes = []
    for _ in range(samples):
        main_sample = [rng.choice(main) for _ in main]
        arena_sample = [rng.choice(arena) for _ in arena]
        change = median_change(main_sample, arena_sample)[2]
        if change is not None:
            changes.append(change)
    if not changes:
        return None, None
    changes.sort()
    count = len(changes)
    return changes[int(count * 0.025)], changes[min(count - 1, int(count * 0.975))]


def fmt_change(value):
    if value is None:
        return "N/A"
    return f"{value:+.2f}%"


def main():
    if len(sys.argv) != 6:
        raise SystemExit(
            "usage: summarize_metrics.py MAIN_TIMINGS.jsonl ARENA_TIMINGS.jsonl "
            "MAIN_ALLOCATIONS.jsonl ARENA_ALLOCATIONS.jsonl OUTPUT.md"
        )

    main_rows = load(sys.argv[1])
    arena_rows = load(sys.argv[2])
    main_alloc_rows = load(sys.argv[3])
    arena_alloc_rows = load(sys.argv[4])
    if min(map(len, (main_rows, arena_rows, main_alloc_rows, arena_alloc_rows))) < 5:
        raise SystemExit("at least five independent processes per revision are required")

    lines = [
        "# Descend benchmark summary",
        "",
        "Medians are across independent processes. Time and allocation-call values are per compilation.",
        "Change is `(arena / main - 1)`. The interval is a deterministic percentile bootstrap",
        "of the median change across processes; it describes run-to-run measurement uncertainty,",
        "not a proof of population-level performance.",
        "",
        "| Phase | Main median (ms) | Arena median (ms) | Change | 95% bootstrap interval |",
        "|---|---:|---:|---:|---:|",
    ]

    for label, field in TIME_FIELDS:
        main_values = per_iteration(main_rows, field)
        arena_values = per_iteration(arena_rows, field)
        main_median, arena_median, change = median_change(main_values, arena_values)
        low, high = bootstrap_change(main_values, arena_values)
        lines.append(
            f"| {label} | {main_median / 1e6:.3f} | {arena_median / 1e6:.3f} | "
            f"{fmt_change(change)} | {fmt_change(low)} to {fmt_change(high)} |"
        )

    lines.extend(
        [
            "",
            "| Allocation metric | Main median | Arena median | Change | 95% bootstrap interval |",
            "|---|---:|---:|---:|---:|",
        ]
    )

    alloc_fields = [
        ("alloc calls", "alloc_calls", True),
        ("alloc_zeroed calls", "alloc_zeroed_calls", True),
        ("realloc calls", "realloc_calls", True),
        ("dealloc calls", "dealloc_calls", True),
        ("requested bytes", "requested_bytes", True),
        ("peak live-byte growth", "peak_growth_bytes", False),
    ]
    for label, field, divide in alloc_fields:
        if divide:
            main_values = per_iteration(main_alloc_rows, field)
            arena_values = per_iteration(arena_alloc_rows, field)
        else:
            main_values = [row[field] for row in main_alloc_rows]
            arena_values = [row[field] for row in arena_alloc_rows]
        main_median, arena_median, change = median_change(main_values, arena_values)
        low, high = bootstrap_change(main_values, arena_values)
        lines.append(
            f"| {label} | {main_median:.0f} | {arena_median:.0f} | {fmt_change(change)} | "
            f"{fmt_change(low)} to {fmt_change(high)} |"
        )

    arena_bytes = [row["arena_allocated_bytes"] for row in arena_alloc_rows]
    arena_bytes = [value for value in arena_bytes if value is not None]
    if arena_bytes:
        lines.extend(
            [
                "",
                f"Arena `Bump::allocated_bytes()` median: {statistics.median(arena_bytes):.0f} bytes.",
            ]
        )

    Path(sys.argv[5]).write_text("\n".join(lines) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
