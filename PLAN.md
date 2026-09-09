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
   `sortAdaptive2`) make sorted and reversed inputs linear, like driftsort's run detection.
5. What is left on the table: small-sort networks (`sort4_stable`/`sort8_stable` style, branchless
   `swap_if_less`), natural-run detection for presorted inputs, the run stack / powersort policy.
   Each is a self-contained verification target.

## Numbers to quote (1M / 10M `u64`, ms)
`sortBlocked` 30–35 / 368 · `sort2` 30–34 / 450–500 · `sort16` 46 / 568 · `BottomUp.sort` 48 / 600 · `Fast.sort` 68 / 780 ·
Rust same-trick 47 / 555 · Rust plain 82 / 965 · driftsort 19 / 269 · `do`-notation loop 1010 / 13072.

## Files (lines / clean-build seconds)
Simple 105 · UInt64Array 88 · Slice 92 · FastMerge 43 · Fast 70 · Correct 434 (10 s) · BottomUpMerge 39 ·
BottomUp 54 · Runs 109 · BottomUpCorrect 252 (6.6 s) · InsertionList 44 · SmallRuns 65 ·
SmallRunsCorrect 300 (2.5 s) · MergeBack 106 · Bidi 183 (17 s) · BidiSort 277 (7.3 s) · Blocked 246 (6.4 s) ·
Adaptive 274 (2.8 s) · Export 10. Total 2791 lines, ~52 s clean build.
