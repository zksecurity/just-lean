# Session report — 2026-09-09 (10:00–15:00 CET grind on "bullet 2")

## Deliverables (all in `~/code/lean-just-lean/`)
- `verified/` — Lean 4.33.1 project, 3.2k lines, 20 verified results (18 sort theorems + `mergeKernelS_spec` + `findRun_spec`) on standard axioms, no `sorry`, zero linter
  warnings; `check.sh` builds, cross-checks all sorts on 37 sizes × 3 seeds × 4 input shapes, prints axioms,
  benchmarks. Also builds unchanged on 4.33.0 (`verified-4330/`).
- Verified sorts: `Fast.sort` (top-down, `sort_toList` = exactly Part 1's `mergeSort`), `BottomUp.sort`,
  `sort16` (insertion runs), `sort2` (bidirectional merge), `sortBlocked` (cache-blocked passes),
  `sortAdaptive2` (sorted/reversed inputs), `sortAdaptive3` (same, one fused scan: `scanFrom_spec`).
- `ffi/` C demo: C fills a `lean_sarray`, calls the exported sort, gets the same buffer sorted in place.
- `rust/` comparison programs (plain, same-trick, same-algorithm, driftsort).
- `../site-smoke/` Verso skeleton (3 parts, docstring roles, an inline definition with `termination_by`,
  checked `#eval` output, tactic proof states rendered, plain command blocks; Part 3 now also renders the
  `findRun` / `mergeKernelS` docstrings). Builds in ~1.5 min incl. Verso.
- `NaturalRuns.lean` (`lake exe naturalruns N`): total natural-run merge sort prototype over the verified
  kernels, with the input-shape benchmark (random / 8 runs / 1% swaps / sawtooth / reversed).
- `README.md` (numbers, 10 lessons, TCB), `PLAN.md` (tutorial chapters).

## Numbers (ms, 1M / 10M random u64)
sortAdaptive2/sortBlocked 30 / 364 · Rust same algorithm 29 / 366 · driftsort 19 / 271 ·
sort2 30–34 / 410–500 · sort16 46 / 568 · BottomUp.sort 48 / 600 · Fast.sort 68 / 780 ·
Rust plain merge sort 82 / 965 · do-notation version 1010 / 13072.
Presorted 1M: 0.5 ms (Rust 0.4); reversed 1M: 1.4 ms with the single fused scan (2.4 ms with two scans). 1k elements: 0.021 ms (driftsort 0.017).
Peak RSS 10M: 167 MB (Rust 119 MB). Clean build of all proofs: 52 s.

## Answers
- Bullet 2 target ("as fast as plain idiomatic Rust merge sort"): exceeded 2.7× with the same-trick
  parity confirmed (Lean = Rust at every level of tricks).
- Remaining gap to driftsort (1.5×) is algorithmic: a Rust port of our exact algorithm is identical.
- Std.Do/mvcgen: available and works; the `do` loops it verifies allocate per iteration when they carry
  more than one mutable value (6–14× slower), so the fast code is tail-recursive with equational specs.

## Scaling (ms, random u64, same machine, one run each; 10M Lean varies 330–430 across runs)
| n | Lean `sortBlocked` (verified) | Rust same algorithm | Rust plain merge sort | Rust driftsort |
|---|---|---|---|---|
| 1k | 0.017 | 0.019 | 0.043 | 0.018 |
| 10k | 0.21 | 0.20 | 0.98 | 0.14 |
| 100k | 2.4 | 2.4 | 6.9 | 1.6 |
| 1M | 29.8 | 28.3 | 82.9 | 18.8 |
| 10M | 330–430 | 367 | 943 | 270 |

## Negative results (measured, not kept)
- Insertion-sorted runs of 16 feeding the blocked bidirectional passes (`lab/scratch/Blocked16-experiment.lean`):
  31 vs 30 ms at 1M, 2.44 vs 2.37 at 100k; 10M inside the run-to-run noise (330–440). The merge passes below
  width 16 are already cache-resident inside a block, so the insertion sort only trades passes for branches.
- Sorting networks (sort8) for run creation: +5% at 10M, nothing at 1M (Experiments.lean).
- `perf stat` is unavailable on this machine (`perf_event_paranoid = 4`), so the driftsort gap was attributed
  by porting the exact Lean algorithm to Rust (identical timings) rather than by hardware counters.

## Input-shape study (1M, ms): where driftsort's remaining advantage comes from
random: Lean 30 / Rust same 28 / driftsort 19 · 8 sorted runs: 30 / 28 / 7.3 · sorted + 1% swaps: 30 / 28 / 14 ·
sawtooth of 1000: 30 / 28 / 23. The bottom-up sort is oblivious to input shape; driftsort's run detection
is its biggest lever on realistic data. Part 3 design in `PLAN.md` builds run detection first.
(`msbench N random|runs8|swaps1|sawtooth`, `lab/rust`: `msort N <shape>`.)

## Natural-run prototype (Part 3 steps 1–3; `NaturalRuns.lean`: total, no `partial`, no `sorry`; run detection and every merge are the verified `findRun` / `mergeKernelS`, only the run-collection and level loops lack specs)
1M ms, hybrid vs driftsort: random 30 vs 19 · 8 runs 5.5 vs 7.3 · sawtooth 16 vs 23 · reversed 2.1 vs 0.6 ·
1% swaps 30–37 vs 14. All outputs exact. Details and lessons in `PLAN.md` (Part 3 design).

## Verified Part 3 building block: `MergeSort/SkipMerge.lean`
`mergeKernelS` = `mergeKernel` with the driftsort-style fast path (runs already in order ⇒ verified
`copyRange`), proved with `merge_eq_append` + `runs_in_order`; its spec is literally `mergeKernel_spec`'s,
so it is a drop-in for the natural-run merge of Part 3 (Rust measurements in `PLAN.md` show where it pays).

## Verified Part 3 building block 2: `MergeSort/FindRun.lean`
`findRun lo n a` = maximal ascending / strictly descending run from `lo` (descending reversed in place),
`findRun_spec`: the run is sorted, a permutation of the original slice, frame outside. With `mergeKernelS`
this is steps 1 and the merge of step 3 of the Part 3 design; what remains is the run stack.
