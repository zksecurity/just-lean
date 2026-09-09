# Tutorial plan v2 (after the 2026-09-09 grind)

Site: Verso `Manual` genre, Lean `v4.33.0` (skeleton with the three parts exists in `../site-smoke`; smoke-tested: `../site-smoke` builds and renders docstrings and checked `#eval` output from this project), every Lean snippet elaborated at build time (hovers, proof
states). No WASM. Bash snippets for the commands. One public repo = this project.

## Part 1 — Merge sort in Lean, and a proof that it sorts  (`MergeSort/Simple.lean`)
1. The spec: `Sorted` (pairwise) and `List.Perm`.
2. `merge`, `mergeSort` with a halves split; `termination_by`; the induction principles Lean generates.
3. The proof, incrementally: `merge_perm`, `mergeSort_perm`, `merge_sorted`, `mergeSort_correct`;
   `#print axioms`.
4. Compile and run: `lake build`, `lean --c`, the generated C, a `main`.

## Part 2 — Make it fast (simple tricks), keep the proof  (`UInt64Array.lean`, `BottomUpMerge.lean`, `BottomUp.lean`, `Slice.lean`, `Runs.lean`, `BottomUpCorrect.lean`)
1. Why `Array UInt64` is slow (boxing) and how core builds `FloatArray`; `UInt64Array` in 60 lines.
2. `UInt64` indices; bounds proofs as auto-params (`by u64`); `omega` after `simp` with `toNat` lemmas.
3. The two-buffer bottom-up sort: `mergeLoop`, `passLoop`, `widthLoop`, `sort` (in place + scratch).
4. Three runtime lessons with measurements: borrow inference and the "consume every path" rule,
   `let mut` tuples in loops, the exclusivity check.
5. The branchless merge step (40%), and why the merge loop lives in its own module.
6. The proof: slices as lists (`Slice.lean`), `mergeLoop_spec`, `mergeRuns`/`ChunkSorted`, `passLoop_spec`,
   `widthLoop_spec`, `sort_sorted`/`sort_perm`. Show the proof-engineering discipline
   (`have h : k.toNat < hi.toNat := h`, goal-only rewriting, macro-name pitfall).
7. Optional: insertion-sorted runs of 16 (`SmallRuns*.lean`), reusing the parametric width-loop spec.
8. Benchmarks vs Rust (same algorithm, same tricks; plain; driftsort). `rust/`.
9. Calling it from C with zero copies (`Export.lean`, `ffi/`), static binary.
10. Side note: `Std.Do`/`mvcgen` and when `do`-loops are fine (one mutable value) vs not.

Also worth a short chapter: the top-down ping-pong version (`Fast.lean`, `Correct.lean`) whose theorem
`sort_toList` says it computes *exactly* Part 1's `mergeSort` — the cleanest refinement story, 30% slower.

## Part 3 — Advanced: toward `Vec::sort`  (`MergeBack.lean`, `Bidi.lean`, `BidiSort.lean`)
1. How driftsort works (run detection, small-sort networks, lazy powersort merges, bidirectional merge).
2. The bidirectional branchless merge in Lean, verified: the reverse-merge lemma `drop_merge_eq`,
   `mergeBidi_spec`, `mergeKernel`, `sort2` = 30–34 ms vs driftsort 19 (1M).
3. Cache-blocked pass order, verified (`Blocked.lean`, `sortBlocked`): 368 ms vs driftsort 271 at 10M.
   Pure reuse of the pass/width specs; the only new idea is running passes in pairs so the data always
   returns to the same buffer.
4. Adaptivity: the verified `isSortedFrom` / `isDescFrom` pre-checks and in-place reverse (`Adaptive.lean`,
   `sortAdaptive2`) make sorted and reversed inputs linear, like driftsort's run detection; `scanFrom` /
   `sortAdaptive3` fuse both checks into one verified scan (reversed 1M: 1.4 ms).
5. What is left on the table: small-sort networks (`sort4_stable`/`sort8_stable` style, branchless
   `swap_if_less`; measured +5% at 10M), natural-run detection for *partially* sorted inputs, the run
   stack / powersort policy, and driftsort's stable-quicksort engine for unsorted runs (the real source of
   its remaining 1.5× on random data). Each is a self-contained verification target.

### Part 3 design: a verified "driftsort-lite" (proposed build order for the next session)
Where the remaining time goes on inputs that are not uniformly random (1M `u64`, ms):

| input | Lean `sortBlocked` | Rust same algorithm | driftsort |
|---|---|---|---|
| random | 30 | 28 | 19 |
| 8 sorted runs concatenated | 30 | 28 | 7.3 |
| sorted + 1% random swaps | 30 | 28 | 14 |
| sawtooth (sorted runs of 1000) | 30 | 28 | 23 |

The bottom-up sort is oblivious: it costs the same on every shape. driftsort's biggest lever on realistic data
is not the merge kernel but *finding existing runs* and merging them in a good order. So Part 3 should be
built in this order, each step verified before the next:

1. **Run detection** — DONE, verified: `FindRun.lean` (`ascEnd`, `descEnd`, `findRun`, `findRun_spec`: the
   slice `[lo, hi)` is sorted afterwards, a permutation of the original, frame outside).
2. **Minimum run length**: runs shorter than 32 are extended with `insertionSortRange` (spec exists:
   `insertionSortRange_spec`). This alone makes "8 sorted runs" and "sawtooth" linear-ish.
3. **Run stack + merge policy**: keep a stack of `(start, len)` of sorted runs (`Array (UInt64 × UInt64)`,
   boxed pairs are fine here: one entry per run, not per element). Invariant: the runs tile `[0, k)`,
   each run's slice is `Sorted`. Merge policy: powersort's node power, or the simpler "merge while the top
   two runs have lengths within 2× of each other" (Timsort-style, but proved only for correctness, not
   for the stack-height bound). Correctness spec is the same shape as `passLoop_spec`: after each merge
   the tiling and `Sorted` invariants hold; termination by the number of runs.
   The merge itself is `mergeKernelS` (`SkipMerge.lean`, verified: bidirectional when the runs are equal,
   one-sided otherwise, a plain copy when the runs are already in order) into the scratch buffer, with a
   ping-pong that alternates buffers per merge level (as in the prototype).
4. **Unsorted runs**: driftsort sorts them with a stable quicksort; a verified in-place stable quicksort is
   the largest single proof (partition permutes and preserves order among equals). The bottom-up
   `sortBlocked` on the run is a correct stand-in first (spec exists) and keeps random inputs at 30 ms.
5. **Small sorts**: `sort4_stable`/`sort8_stable` networks with branchless selects, then `insertionSortRange`
   from 8/4 upward; +5% at 10M measured. Proof: 5 comparators, `decide`-able on the abstract permutation.

**Prototype (this session, `NaturalRuns.lean`, `lake exe naturalruns N`)**: steps 1–3 as a total (no `partial`)
prototype whose run detection (`findRun`) and merges (`mergeKernelS`) are the verified kernels; only the
run-collection loop and the level loop still lack specifications (the run stack of step 3). Runs are merged level by level (adjacent pairs, bidirectional
when equal length), with a read-only run count first that bails out to `sortBlocked` when the average run
is shorter than 32 (the scan costs 0.2–0.7 ms at 1M). Every output was checked against the reference.

| input (1M) | `sortBlocked` | hybrid natural runs | driftsort |
|---|---|---|---|
| random | 29–30 | 30–31 | 19 |
| 8 sorted runs | 30 | 5.5–6.3 | 7.3 |
| sawtooth (runs of 1000) | 29 | 16 | 23 |
| reversed | 29 | 2.1 | 0.6 |
| sorted + 1% swaps | 30 | 37 (insertion to 32) / 30 (blockPasses to 4096) | 14 |

Lessons for the verified version: (a) run detection + level merging beats driftsort on inputs with long
runs; (b) extending short runs must not overwrite the following natural run (extending to 1024 destroyed the
sawtooth case: 16 → 31 ms), so extend only the tail `[hi, lo+minRun)` and merge; (c) the 1%-swaps case is
not about runs at all (read `lab/driftsort-src/drift.rs`): driftsort only accepts natural runs of length
≥ sqrt(n) (1000 at 1M) and otherwise emits *unsorted* logical runs that are concatenated lazily and
sorted by its stable quicksort once they no longer fit the scratch buffer; on nearly sorted data that
quicksort's small-sort (insertion sort below 32) is close to linear. A merge-only design cannot copy this;
the merge-side answer is the small-sort networks (step 5) plus skipping merges whose runs are already in
order (`src[mid-1] ≤ src[mid]`, implemented in the prototype, no effect on natural runs since they are cut
exactly at the defects); (d) never compute
`a.size < 2^64` at runtime in a loop, thread it as an erased hypothesis (the Nat comparison against a bignum
made the scan 10× slower: 2.3 ms → 0.2 ms).

**Skip-in-order merges, measured in Rust on the fixed-width blocked sort** (`lab/rust`, "skip in-order
merges"; 1M ms, plain → with skip): random 28.8 → 31.5 (the extra branch mispredicts at small widths),
1% swaps 29.3 → 24.9, sawtooth 28.8 → 21.0, 8 runs 29.2 → 13.6. Restricting the skip to widths ≥ 64 removes
the random-input cost (29.0) but also most of the gain (8 runs 19.2, swaps 28.8, sawtooth 26.9). So the
skip belongs in the natural-run merge (where merges are between long runs) rather than in the bottom-up
levels, which is exactly what driftsort does.

Expected outcome: random stays at ~30 ms (28 with the small-sort networks), the run-based shapes drop to
driftsort territory (8 runs: ~8 ms; 1% swaps: needs the stable quicksort or a Galloping merge to reach 14).
Proof budget estimate from Part 2's rates (~100 lines of spec per 40 lines of loop): run detection 150,
run stack 300, stable quicksort 500+.

## Numbers to quote (1M / 10M `u64`, ms)
`sortBlocked` 30–35 / 364–440 · `sort2` 30–34 / 450–500 · `sort16` 46 / 568 · `BottomUp.sort` 48 / 600 · `Fast.sort` 68 / 780 ·
Rust same-trick 47 / 555 · Rust plain 82 / 965 · driftsort 19 / 269 · `do`-notation loop 1010 / 13072.

## Files (lines / clean-build seconds)
Simple 105 · UInt64Array 88 · Slice 92 · FastMerge 43 · Fast 70 · Correct 434 (10 s) · BottomUpMerge 39 ·
BottomUp 54 · Runs 109 · BottomUpCorrect 252 (6.6 s) · InsertionList 44 · SmallRuns 65 ·
SmallRunsCorrect 300 (2.5 s) · MergeBack 106 · Bidi 183 (17 s) · BidiSort 277 (7.3 s) · Blocked 246 (6.4 s) ·
Adaptive 420 (4 s) · Export 10. Total 2939 lines, ~55 s clean build.

## Scaling (ms, random u64, same machine, one run each; 10M Lean varies 330–430 across runs)
| n | Lean `sortBlocked` (verified) | Rust same algorithm | Rust plain merge sort | Rust driftsort |
|---|---|---|---|---|
| 1k | 0.017 | 0.019 | 0.043 | 0.018 |
| 10k | 0.21 | 0.20 | 0.98 | 0.14 |
| 100k | 2.4 | 2.4 | 6.9 | 1.6 |
| 1M | 29.8 | 28.3 | 82.9 | 18.8 |
| 10M | 330–430 | 367 | 943 | 270 |
