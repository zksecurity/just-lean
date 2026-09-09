# Session report — 2026-09-09 (10:00–15:00 CET grind on "bullet 2")

## Deliverables (all in `~/code/lean-just-lean/`)
- `verified/` — Lean 4.33.1 project, 3.4k lines of library, 25 verified results (18 sort theorems + `mergeKernelS_spec` + `findRun_spec` + `net4_sorted`/`net4_perm` + `sort4_spec` + `sort8_spec`/`sort8P_spec`) on standard axioms, no `sorry`, zero linter
  warnings; `check.sh` builds, cross-checks all sorts on 37 sizes × 3 seeds × 4 input shapes, prints axioms,
  benchmarks. Also builds unchanged on 4.33.0 (`verified-4330/`).
- Verified sorts: `Fast.sort` (top-down, `sort_toList` = exactly Part 1's `mergeSort`), `BottomUp.sort`,
  `sort16` (insertion runs), `sort2` (bidirectional merge), `sortBlocked` (cache-blocked passes),
  `sortAdaptive2` (sorted/reversed inputs), `sortAdaptive3` (same, one fused scan: `scanFrom_spec`).
- `ffi/` C demo: C fills a `lean_sarray`, calls the exported sort, gets the same buffer sorted in place.
- `rust/` comparison programs (plain, same-trick, same-algorithm, driftsort).
- `../site-smoke/` Verso skeleton (3 parts, docstring roles, an inline definition with `termination_by`,
  checked `#eval` output, tactic proof states rendered, plain command blocks; Part 3 now also renders the
  natural-runs paragraph with `findRun` / `mergeKernelS` and a sorting-network page with `net4` / `sort8`).
  Builds in ~1.5 min incl. Verso.
- `NaturalRuns.lean` (`lake exe naturalruns N`): total natural-run merge sort prototype over the verified
  kernels, with the input-shape benchmark (random / 8 runs / 1% swaps / sawtooth / reversed).
- `README.md` (numbers, 10 lessons, TCB), `PLAN.md` (tutorial chapters).

## Numbers (ms, 1M / 10M random u64)
Medians of 5 idle-machine runs at 1M: Lean `sortBlocked` 30.1 (29.8–30.2) · Rust same algorithm 29.0 (28.7–29.2) ·
Lean `BottomUp.sort` 49.0 · `Fast.sort` 69.8 · Rust plain 81.1 · driftsort 18.4. Lean/Rust same-algorithm ratio 1.04.
sortAdaptive2/sortBlocked 30 / 364 · Rust same algorithm 29 / 366 · driftsort 19 / 271 ·
sort2 30–34 / 410–500 · sort16 46 / 568 · BottomUp.sort 48 / 600 · Fast.sort 68 / 780 ·
Rust plain merge sort 82 / 965 · do-notation version 1010 / 13072.
Presorted 1M: 0.5 ms (Rust 0.4); reversed 1M: 1.4 ms with the single fused scan (2.4 ms with two scans). 1k elements: 0.021 ms (driftsort 0.017).
Peak RSS 10M: 167 MB (Rust 119 MB). Clean build of all proofs: 49 s (measured after the last change; 1.4 GB peak).

## Answers
- Bullet 2 target ("as fast as plain idiomatic Rust merge sort"): exceeded 2.7× with the same-trick
  parity confirmed (Lean = Rust at every level of tricks).
- Remaining gap to driftsort (1.5×) is algorithmic: a Rust port of our exact algorithm is identical.
- Std.Do/mvcgen: available and works; the `do` loops it verifies allocate per iteration when they carry
  more than one mutable value (6–14× slower), so the fast code is tail-recursive with equational specs.

## Scaling (ms, random u64, same machine, one run each; the 10M spread of 330–430 seen earlier came from concurrent builds, idle machine: Lean 370–376, Rust same algorithm 373–378, driftsort 270–273)
| n | Lean `sortBlocked` (verified) | Rust same algorithm | Rust plain merge sort | Rust driftsort |
|---|---|---|---|---|
| 1k | 0.017 | 0.019 | 0.043 | 0.018 |
| 10k | 0.21 | 0.20 | 0.98 | 0.14 |
| 100k | 2.4 | 2.4 | 6.9 | 1.6 |
| 1M | 29.8 | 28.3 | 82.9 | 18.8 |
| 10M | 370–376 (idle) | 373–378 (idle) | 943 | 270 |

## Negative results (measured, not kept)
- Insertion-sorted runs of 16 feeding the blocked bidirectional passes (`lab/scratch/Blocked16-experiment.lean`):
  31 vs 30 ms at 1M, 2.44 vs 2.37 at 100k; 10M inside the run-to-run noise (330–440). The merge passes below
  width 16 are already cache-resident inside a block, so the insertion sort only trades passes for branches.
- Sorting networks (sort8) for run creation: +5% at 10M, nothing at 1M (Experiments.lean).
- Stable quicksort prototype (`Experiments.lean`, branchless out-of-place partition, `experiments N swaps1`) on the
  1%-swaps input: 36.7 ms vs 37 for the blocked merge sort (driftsort 14), random 39 vs 32. So a quicksort
  engine alone does not explain driftsort's win on nearly sorted data; it is the combination with its
  small-sort networks and pivot selection (`PLAN.md`, step 4/5).
- `perf stat` is unavailable on this machine (`perf_event_paranoid = 4`), so the driftsort gap was attributed
  by porting the exact Lean algorithm to Rust (identical timings) rather than by hardware counters.

## Input-shape study (1M, ms): where driftsort's remaining advantage comes from
random: Lean 30 / Rust same 28 / driftsort 19 · 8 sorted runs: 30 / 28 / 7.3 · sorted + 1% swaps: 30 / 28 / 14 ·
sawtooth of 1000: 30 / 28 / 23. The bottom-up sort is oblivious to input shape; driftsort's run detection
is its biggest lever on realistic data. Part 3 design in `PLAN.md` builds run detection first.
(`msbench N random|runs8|swaps1|sawtooth`, `lab/rust`: `msort N <shape>`.)

## Natural-run prototype (Part 3 steps 1–3; `NaturalRuns.lean`: total, no `partial`, no `sorry`; run detection and every merge are the verified `findRun` / `mergeKernelS`, only the run-collection and level loops lack specs)
1M ms, hybrid vs driftsort: random 30 vs 19 · 8 runs 5.5 vs 7.3 · sawtooth 16 vs 23 · reversed 2.1 vs 0.6 ·
1% swaps 30–37 vs 14. `naturalruns verify`: 3990 sorts over 38 sizes × 3 seeds × 5 shapes, 0 mismatches (part of `check.sh`). Details and lessons in `PLAN.md` (Part 3 design).

## Verified Part 3 building block: `MergeSort/SkipMerge.lean`
`mergeKernelS` = `mergeKernel` with the driftsort-style fast path (runs already in order ⇒ verified
`copyRange`), proved with `merge_eq_append` + `runs_in_order`; its spec is literally `mergeKernel_spec`'s,
so it is a drop-in for the natural-run merge of Part 3 (Rust measurements in `PLAN.md` show where it pays).

## Verified Part 3 building block 2: `MergeSort/FindRun.lean`
`findRun lo n a` = maximal ascending / strictly descending run from `lo` (descending reversed in place),
`findRun_spec`: the run is sorted, a permutation of the original slice, frame outside. With `mergeKernelS`
this is steps 1 and the merge of step 3 of the Part 3 design; what remains is the run stack.

## Verified Part 3 building block 3: `MergeSort/Net4.lean`
A 5-comparator sorting network on four values built from branchless `mn`/`mx` selects; `net4_sorted` and
`net4_perm` are proved by exhaustive case analysis (`repeat' split`, then `omega` on every leaf; 1.7 s).
`sort4` applies it in place to `a[lo..lo+4)` (`sort4_spec`: slice = `net4`, frame outside). This is the shape of driftsort's `sort4_stable`; `sort8` = two of these + the verified (bidirectional) `mergeKernel`,
exactly driftsort's `sort8_stable`, with `sort8_spec` (sorted, permutation, frame) composed from `sort4_spec`,
`net4_sorted`/`net4_perm` and `mergeKernel_spec` in 40 lines. Part 3 step 5 (small sorts) is therefore verified.
Measured as a run former over 1M elements (`msbench`, "run former" lines): verified `sort8P` on all blocks of 8 = 4.7 ms
vs verified insertion sort on blocks of 8 = 6.9 ms. As a full pipeline (`sort8P` runs, then the verified bidirectional width loop from width 8, glue unverified,
output exact): 33.6–38 ms at 1M vs `sort2` 31–35 (a wash: the 4.7 ms network pass buys three merge levels),
481 vs 498 ms at 10M (3%). So the networks only pay inside an in-cache small sort, as driftsort uses them,
not as a run former for the cache-oblivious bottom-up passes.
Pitfall found on the way (worth a tutorial paragraph): a loop
that keeps its own reference to `src` while `sort8` sorts `src` in place makes every block copy the whole array
(24 000 ms instead of 4.7 ms); returning both buffers as a pair (`sort8P`) fixes it, exactly like `Blocked.lean`.

## Generic over the comparison: no loss, with one layout rule (`GenericBench.lean`, `lake exe genericbench`)
Same three loops with the comparison abstracted (`MergeSort/Generic.lean`), 1M `u64`, ms:
monomorphic `BottomUp.sort` 49.6 · `le` as a function argument with `@[specialize]` 78 · `le` from a type class
instance with `@[specialize]` 78 · `le` as an opaque closure 390 · closure chosen at runtime 350 ·
**generic loops with the specialised merge kernel instantiated in its own module (`GenericU64.lean`) 50.3**.
The generated C of the specialised merge loop is identical to the monomorphic one; the 78 ms comes from clang
inlining the merge loop into the pass loop when both specialised copies land in the same C file (Lean's
`@[noinline]` does not reach C). Rule: `@[specialize]` the kernel on the comparison, instantiate it in its own
module, and pass the kernel to the (also specialised) pass loop. Type-class or function argument makes no
difference; an unspecialised closure costs 7×.

## Part 3: the unverified 1:1 driftsort port (`MergeSort/Drift.lean`, 16:xx CEST)
A function-by-function port of `core::slice::sort::stable` for `u64` (run detection, powersort run stack with
lazy logical runs, stable quicksort with pseudo-median pivots and equal-element partitions, the 32-element
small sort with `sort8_stable` networks, the shorter-run-to-scratch physical merge, driftsort's scratch sizing).
Total (no `partial`), no `sorry`; bounds are runtime-checked in the model but the hot accessors are unchecked
externs for this lab measurement (`getU`/`setU`, `memcpy`/vectorised reverse copy, batched `set2`/`set4`).
`driftbench verify`: 2472 sorts over 103 sizes × 3 seeds × 8 shapes, 0 mismatches (in `check.sh`).

| 1M `u64`, ms | Lean port | Rust `Vec::sort` | ratio |
|---|---|---|---|
| random | 27.7 | 18.7 | 1.48 |
| 8 sorted runs | 8.0 | 7.3 | 1.10 |
| sorted + 1% swaps | 21.4 | 14.5 | 1.48 |
| sawtooth (runs of 1000) | 24.0 | 22.7 | 1.06 |
| reversed | 1.3 | 0.52 | 2.5 |
| sorted | 0.99 | 0.38 | 2.6 |
| 16 distinct values | 5.7 | 3.6 | 1.6 |
| 1000 distinct values | 11.4 | 7.5 | 1.5 |
| 10M random | 341 | 270 | 1.26 |

How it got from 85 ms to 27.7 (random, 1M): unchecked accessors 85 → 53 (the bounds checks cost 32 ms; a
verified version recovers them with proofs); the bidirectional merge returned a 6-tuple per call (five boxed
`UInt64`s) → 40; `memcpy`/vectorised copy-back, the partition scan split at the pivot, scans returning one
pair, `stablePartition` inlined → 31; batched stores `set2`/`set4` (one exclusivity check per 2–4 stores)
brought the network and merge stages of the small sort to Rust parity → 30; the physical merge made
branchless in the style of the verified merge loop (runs8 17.7 → 8.0, sawtooth 40 → 24).
What is left (from warm per-phase measurements against a Rust copy of the same phases, `lab/rust-drift`):
partition per level at parity (1.10 vs 1.03 ms), small sort 7.4 vs 6.7, insertion 1.3×; the remaining
random-input gap is per-store exclusivity checks in the element loops and ~4 ms of control-path allocations
(a pair per quicksort call and per small sort). Sorted/reversed inputs pay the 8 MB `zeros` scratch
(Rust's scratch is allocated lazily and never touched on those inputs).

Two harness lessons that also correct earlier numbers: (1) a `let` whose only use is inside the timed
closure is floated into the closure by the compiler, so `ofArray` (7 ms) was being timed as part of the sort
on some shapes; obtain inputs with `← IO.lazyPure` before the clock; (2) an input array still referenced by
the harness is copied inside the timing by the first in-place write (2.5 ms at 1M, ~25 at 10M): Rust's
harness clones before the clock, ours must hand the array over uniquely. Under the corrected protocol the
verified `sortBlocked` is 27.8 ms (not 30) at 1M.

## Night of Sept 9/10: the driftsort is verified
`MergeSort/DriftSort.lean` (bounds-safe port, 535 lines), `DriftCorrect.lean` (kernels: small sort, physical
merge, stable partition; 620 lines) and `DriftCorrectLoop.lean` (run creation, logical merge, run stack, the
quicksort with its ancestor-pivot precondition, entry point; 780 lines). Headline theorems:
`DriftSort.sort_sorted` and `DriftSort.sort_perm`, on `propext`, `Classical.choice`, `Quot.sound` only, no
`sorry`, no `partial`. Every loop has a slice-level spec with a frame clause; the run stack is proved with a
tiling invariant `RunsOK` over the list of runs (top first) and a generic `QuickSpec` for the range sorter,
so the eager fallback (insertion sort, never executed) and the stable quicksort share one loop proof.
Deviations from Rust, all invisible for `u64`: the 4-element network is wired differently (same output),
the small sort's odd-length final merge is one-sided, the physical merge goes through the scratch buffer
and back, the scratch has the size of the input, the run stack is a list, the pivot position is not
special-cased in the partition, and the final "is the collapsed run the whole range" check is a runtime test
instead of a stack invariant. Speed of the bounds-safe version at 1M (input handed over uniquely):
random 41 ms (lab port 28, Rust 19), 8 runs 5.6, sorted 1.0, 16 distinct values 9.3; the difference to the
lab port is the absence of batched stores and of the `memcpy`/vectorised copies (next step: the same C as
proof-carrying primitives with the loop as model).
Proof-engineering lessons of the night: (1) a `have h : … := h` that shadows the guard with its `Nat` form
breaks `simp` on the unfolded definition (auxiliary proof lemmas expect the other type); derive it under a
new name. (2) A `let`-bound length inside `omega` goals is a separate atom; state facts after the `let`
and in terms of it. (3) `generalize … at *` over a large goal times out; generalize the goal only and derive
each stage's facts by rewriting the small equation into a freshly stated fact. (4) Nested tuple patterns
`let ⟨(a, b), h⟩ := …` leave an unreduced `match` in the goal; generalize the scrutinee and `rcases` it to
make the match reduce. (5) `simp` cannot rewrite the index of `set` (the bounds proof depends on it); apply
the induction hypothesis to the goal's own terms and evaluate conditionals only in proof-free side goals.
(6) Bookkeeping proofs after a well-founded recursive call must not let the kernel look into the call
(`simpa` did, causing "deep recursion"); use explicit lemma applications.
