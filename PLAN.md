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

## Part 3 — Advanced: toward `Vec::sort`  (`MergeBack.lean`, `Bidi.lean`, `BidiSort.lean`, `Blocked.lean`, `Adaptive.lean`, `SkipMerge.lean`, `FindRun.lean`, prototype `NaturalRuns.lean`)
1. How driftsort works (run detection, small-sort networks, lazy powersort merges, bidirectional merge).
2. The bidirectional branchless merge in Lean, verified: the reverse-merge lemma `drop_merge_eq`,
   `mergeBidi_spec`, `mergeKernel`, `sort2` = 30–34 ms vs driftsort 19 (1M).
3. Cache-blocked pass order, verified (`Blocked.lean`, `sortBlocked`): 368 ms vs driftsort 271 at 10M.
   Pure reuse of the pass/width specs; the only new idea is running passes in pairs so the data always
   returns to the same buffer.
4. Adaptivity: the verified `isSortedFrom` / `isDescFrom` pre-checks and in-place reverse (`Adaptive.lean`,
   `sortAdaptive2`) make sorted and reversed inputs linear, like driftsort's run detection; `scanFrom` /
   `sortAdaptive3` fuse both checks into one verified scan (reversed 1M: 1.4 ms).
5. Natural runs: verified run detection (`FindRun.lean`) and the in-order merge fast path (`SkipMerge.lean`),
   and the total prototype `NaturalRuns.lean` that beats driftsort on inputs with long runs (design below).
6. What is left on the table: small-sort networks (`sort4_stable`/`sort8_stable` style, branchless
   `swap_if_less`; measured +5% at 10M), the verified run stack / powersort policy, and driftsort's
   stable-quicksort engine for unsorted runs (the real source of its remaining 1.5× on random data and of
   its win on nearly sorted data). Each is a self-contained verification target.

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
   `insertionSortRange_spec`); extend only the tail `[hi, lo+minRun)` so the next natural run survives
   (lesson (b) below). The prototype does this with insertion sort to 32.
3. **Run stack + merge policy**: keep a stack of `(start, len)` of sorted runs (`Array (UInt64 × UInt64)`,
   boxed pairs are fine here: one entry per run, not per element). Invariant: the runs tile `[0, k)`,
   each run's slice is `Sorted`. Merge policy: powersort's node power, or the simpler "merge while the top
   two runs have lengths within 2× of each other" (Timsort-style, but proved only for correctness, not
   for the stack-height bound). Correctness spec is the same shape as `passLoop_spec`: after each merge
   the tiling and `Sorted` invariants hold; termination by the number of runs.
   The merge itself is `mergeKernelS` (`SkipMerge.lean`, verified: bidirectional when the runs are equal,
   one-sided otherwise, a plain copy when the runs are already in order) into the scratch buffer, with a
   ping-pong that alternates buffers per merge level (as in the prototype).
4. **Unsorted runs**: driftsort sorts them with a stable quicksort (`lab/driftsort-src/quicksort.rs`): the
   partition is *out of place* into the scratch buffer (left part written forward from the scratch start,
   right part written backward from the scratch end, 4× unrolled and branchless via `partition_one`), then
   copied back (left part forward, right part reversed); recursion depth limited to `2·log2(n)`, after
   which it falls back to the merge path; below `small_sort_threshold` (32 for `u64`) it calls the small
   sort. A verified version is therefore "partition into scratch + copy back", the same shape as our
   `mergeLoop`/`copyRange` specs (out-of-place, no in-place swaps): the spec is
   `dst.slice = filter (< p) ++ [p] ++ filter (≥ p)` of the source slice (stability = filter keeps order),
   which is a list lemma, plus the same frame clauses. Estimated 400–500 lines. The bottom-up `sortBlocked`
   on the run is a correct stand-in first (spec exists) and keeps random inputs at 30 ms. Measured: our
   unverified stable-quicksort prototype does *not* win on the 1%-swaps input (36.7 vs 37 ms; driftsort
   14), so step 4 only pays together with step 5 and driftsort's pivot selection.
5. **Small sorts** (`lab/driftsort-src/smallsort.rs`, the stable variant used by driftsort for `u64`,
   `small_sort_general_with_scratch`, threshold 32): sort both halves of a ≤32-element slice with
   `sort8_stable` (a 19-comparator network built from two `sort4_stable` + a bidirectional 4+4 merge,
   all `swap_if_less` selects) into scratch, extend each half with insertion (`insert_tail`), then one
   `bidirectional_merge` of the two halves back into place. The unstable variant (`ipnsort`) uses
   `sort9_optimal`/`sort13_optimal` networks. Verified version: `sort4_stable` and `sort8_stable` as
   straight-line code over `get`/`set` with a `decide`d correctness lemma on the 8-element list (the merge
   step is `mergeBidi_spec` on runs of length 4). Measured +5% at 10M with an unverified `net8`.

Also from `merge.rs`: driftsort's physical merge copies the *shorter* run to scratch and merges it
forward (if it is the left run) or backward (if it is the right run) directly into `v`, so it needs only
`min(left, right)` scratch and its scratch buffer is `n/2` overall, versus our two full buffers (`n` scratch);
this is where Rust's 119 MB vs our 167 MB at 10M comes from.

**Prototype (this session, `NaturalRuns.lean`, `lake exe naturalruns N`)**: steps 1–3 as a total (no `partial`)
prototype whose run detection (`findRun`) and merges (`mergeKernelS`) are the verified kernels; only the
run-collection loop and the level loop still lack specifications (the run stack of step 3). Runs are merged level by level (adjacent pairs, bidirectional
when equal length), with a read-only run count first that bails out to `sortBlocked` when the average run
is shorter than 32 (the scan costs 0.2–0.7 ms at 1M). Every output was checked against the reference (`naturalruns verify`: 3990 sorts, 38 sizes × 3 seeds × 5 shapes, 0 mismatches).

| input (1M) | `sortBlocked` | hybrid natural runs | driftsort |
|---|---|---|---|
| random | 29–30 | 30–31 | 19 |
| 8 sorted runs | 30 | 5.5–6.3 | 7.3 |
| sawtooth (runs of 1000) | 29 | 16 | 23 |
| reversed | 29 | 2.1 | 0.6 |
| sorted + 1% swaps | 30 | 37 (insertion to 32) / 30 (blockPasses to 4096) | 14 |

At 100k (ms, hybrid vs driftsort): random 2.4 vs 1.6 · 8 runs 0.43 vs 0.71 · sawtooth 1.10 vs 1.54 · reversed 0.10 vs 0.05 ·
1% swaps 2.7 vs 1.5.
At 10M (ms): 8 runs 57 vs driftsort 97 · sawtooth 273 vs 268 · reversed 23 vs 9 · random 390 vs 270 ·
1% swaps 444 vs (driftsort n/a, `sortBlocked` 367).

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

**Next proof, stated precisely** (the run stack of step 3, matching the prototype's `mergeLevel`/`mergeAll`):

```lean
/-- `runs = #[r₀, …, rₖ]` with `r₀ = lo`, `rₖ = n`, strictly increasing; every `a[rⱼ, rⱼ₊₁)` is sorted. -/
def RunsOK (runs : Array UInt64) (a : UInt64Array) : Prop :=
  1 < runs.size ∧
  ∀ j, j + 1 < runs.size → runs[j]!.toNat < runs[j + 1]!.toNat ∧
    Sorted le64 (a.slice runs[j]!.toNat (runs[j + 1]!.toNat - runs[j]!.toNat))

theorem mergeLevel_spec (runs : Array UInt64) (src dst : UInt64Array) (h : RunsOK runs src) … :
    let r := mergeLevel runs 0 src dst #[]
    RunsOK (r.1.push runs[runs.size - 1]!) r.2.2 ∧
    (r.2.2.slice runs[0]!.toNat (runs[runs.size - 1]!.toNat - runs[0]!.toNat)).Perm
      (src.slice runs[0]!.toNat (runs[runs.size - 1]!.toNat - runs[0]!.toNat)) ∧
    r.1.size + 1 ≤ (runs.size + 2) / 2          -- the level halves the number of runs

theorem collectRuns_spec … : RunsOK (collectRuns minRun n 0 a #[] …).1 (collectRuns …).2 ∧ perm ∧ frame
```

Induction for `mergeLevel_spec` is on `runs.size - i` (two runs per step), each step is
`mergeKernelS_spec` (sorted-run premises come from `RunsOK`) plus `slice_add` to glue the merged slice
onto the already-produced prefix, exactly like `passLoop2_spec`; the odd last run is `copyRange_spec`.
`collectRuns_spec` is `findRun_spec` + `insertionSortRange_spec` per step. With both, `sortNatural_sorted`
/ `sortNatural_perm` follow by induction on the number of levels (`mergeAll`), and the hybrid's policy
choice needs no proof at all (both branches are verified sorts).

Expected outcome: random stays at ~30 ms (28 with the small-sort networks), the run-based shapes drop to
driftsort territory (8 runs: ~8 ms; 1% swaps: needs the stable quicksort or a Galloping merge to reach 14).
Proof budget estimate from Part 2's rates (~100 lines of spec per 40 lines of loop): run detection 150,
run stack 300, stable quicksort 500+.

## Numbers to quote (1M / 10M `u64`, ms)
`sortBlocked` 30–35 / 364–440 · `sort2` 30–34 / 450–500 · `sort16` 46 / 568 · `BottomUp.sort` 48 / 600 · `Fast.sort` 68 / 780 ·
Rust same-trick 47 / 555 · Rust plain 82 / 965 · driftsort 19 / 269 · `do`-notation loop 1010 / 13072.

## Files (lines / clean-build seconds)
Simple 105 · UInt64Array 91 · Slice 92 · FastMerge 43 · Fast 70 · Correct 434 (10 s) · BottomUpMerge 39 · BottomUp 54 · Runs 109 · BottomUpCorrect 252 (6.6 s) · InsertionList 44 · SmallRuns 65 · SmallRunsCorrect 300 (2.5 s) · MergeBack 106 · Bidi 183 (17 s) · BidiSort 277 (7.3 s) · Blocked 253 (6.4 s) · Adaptive 412 (4 s) · SkipMerge 128 · FindRun 157 · Export 10. Total 3224 lines, ~60 s clean build.

## Scaling (ms, random u64, same machine, one run each; the 10M spread of 330–430 seen earlier came from concurrent builds, idle machine: Lean 370–376, Rust same algorithm 373–378, driftsort 270–273)
| n | Lean `sortBlocked` (verified) | Rust same algorithm | Rust plain merge sort | Rust driftsort |
|---|---|---|---|---|
| 1k | 0.017 | 0.019 | 0.043 | 0.018 |
| 10k | 0.21 | 0.20 | 0.98 | 0.14 |
| 100k | 2.4 | 2.4 | 6.9 | 1.6 |
| 1M | 29.8 | 28.3 | 82.9 | 18.8 |
| 10M | 370–376 (idle) | 373–378 (idle) | 943 | 270 |
