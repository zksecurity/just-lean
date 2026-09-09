# Session report — 2026-09-09 (10:00–15:00 CET grind on "bullet 2")

## Deliverables (all in `~/code/lean-just-lean/`)
- `verified/` — Lean 4.33.1 project, 2.8k lines, 16 theorems on standard axioms, no `sorry`, zero linter
  warnings; `check.sh` builds, cross-checks all sorts on 37 sizes × 3 seeds × 4 input shapes, prints axioms,
  benchmarks. Also builds unchanged on 4.33.0 (`verified-4330/`).
- Verified sorts: `Fast.sort` (top-down, `sort_toList` = exactly Part 1's `mergeSort`), `BottomUp.sort`,
  `sort16` (insertion runs), `sort2` (bidirectional merge), `sortBlocked` (cache-blocked passes),
  `sortAdaptive2` (sorted/reversed inputs in one pass).
- `ffi/` C demo: C fills a `lean_sarray`, calls the exported sort, gets the same buffer sorted in place.
- `rust/` comparison programs (plain, same-trick, same-algorithm, driftsort).
- `../site-smoke/` Verso skeleton (3 parts, docstring roles, checked `#eval`, rendered proof states).
- `README.md` (numbers, 10 lessons, TCB), `PLAN.md` (tutorial chapters).

## Numbers (ms, 1M / 10M random u64)
sortAdaptive2/sortBlocked 30 / 364 · Rust same algorithm 29 / 366 · driftsort 19 / 271 ·
sort2 30–34 / 410–500 · sort16 46 / 568 · BottomUp.sort 48 / 600 · Fast.sort 68 / 780 ·
Rust plain merge sort 82 / 965 · do-notation version 1010 / 13072.
Presorted 1M: 0.5 ms (Rust 0.4). Peak RSS 10M: 167 MB (Rust 119 MB).

## Answers
- Bullet 2 target ("as fast as plain idiomatic Rust merge sort"): exceeded 2.7× with the same-trick
  parity confirmed (Lean = Rust at every level of tricks).
- Remaining gap to driftsort (1.5×) is algorithmic: a Rust port of our exact algorithm is identical.
- Std.Do/mvcgen: available and works; the `do` loops it verifies allocate per iteration when they carry
  more than one mutable value (6–14× slower), so the fast code is tail-recursive with equational specs.
