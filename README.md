# Verified, fast merge sort in Lean 4 (lab notes, 2026-09-09)

Everything here is total (no `partial`), has no `sorry`, and the correctness theorems depend only on
`propext`, `Classical.choice`, `Quot.sound`. Lean `v4.33.1`.

## What is trusted

The theorems are about the *model* (`UInt64Array.data : Array UInt64`). The runtime representation is a
`lean_sarray` of 8-byte elements, and the five `@[extern c inline]` snippets in `UInt64Array.lean`
(`size`, `get`, `set`, `zeros`, plus the constructor/projection externs) are trusted to implement the
model, exactly as core trusts its own `ByteArray`/`FloatArray` externs. Beyond that: Lean's kernel,
compiler and runtime, and clang. `Sorted` is with respect to unsigned `≤` on `UInt64`.

## Files

| file | what |
|---|---|
| `MergeSort/Simple.lean` | Part 1: readable list merge sort (`mergeSort`, halves split) and readable proof: `mergeSort_correct` (sorted ∧ permutation). |
| `MergeSort/UInt64Array.lean` | An unboxed `UInt64` array on Lean's scalar-array runtime (`lean_sarray`), the same recipe core uses for `FloatArray`. Model = `Array UInt64`; runtime ops are `@[extern c inline]`. Bounds proofs are auto-params (`by u64`). |
| `MergeSort/Fast.lean` | Part 2a: top-down ping-pong merge sort in one `2n` buffer, `UInt64` indices, branchless merge step. |
| `MergeSort/Correct.lean` | `Fast.sort_toList : (sort xs h).data.toList = mergeSort le64 xs.data.toList` (refinement of Part 1), plus `sort_sorted`, `sort_perm`. |
| `MergeSort/BottomUpMerge.lean`, `BottomUp.lean` | Part 2b: bottom-up merge sort with two buffers (in place + one scratch), no recursion, branchless merge. The fastest version. |
| `MergeSort/Runs.lean`, `BottomUpCorrect.lean` | List theory of one pass (`mergeRuns`, `ChunkSorted`) and `BottomUp.sort_sorted`, `BottomUp.sort_perm`. |
| `MergeSort/SmallRuns.lean`, `InsertionList.lean`, `SmallRunsCorrect.lean` | Simple trick: insertion-sort 16-element blocks first, start the width loop at 16 (`sort16`); list-level insertion sort; `sort16_sorted`, `sort16_perm`. |
| `MergeSort/MergeBack.lean`, `Bidi.lean`, `BidiSort.lean` | Advanced trick, verified: bidirectional branchless merge for equal-length runs (`mergeBidi`, `mergeKernel`, `sort2`; `sort2_sorted`, `sort2_perm`). Core lemma: merging from the back is the reversed merge of the reversed runs (`drop_merge_eq`). |
| `MergeSort/Blocked.lean` | Advanced trick, verified: cache-blocked pass order (`twoPasses`, `blockPasses`, `blocksLoop`, `sortBlockedB`/`sortBlocked`; `sortBlocked_sorted`, `sortBlocked_perm`). Both buffers are threaded through as a pair (otherwise the reused scratch is shared and every pass copies it). |
| `MergeSort/Adaptive.lean` | Verified `isSortedFrom` / `isDescFrom` pre-checks and an in-place `reverseRange`; `sortAdaptive2` returns sorted input as is, reverses strictly descending input, and sorts otherwise (presorted 1M: 0.6 ms; reversed: ~1 ms). |
| `MergeSort/Export.lean`, `ffi/` | `@[export mergesort_sort_u64]` and a C program that sorts a raw buffer through the verified sort. |
| `Bench.lean`, `VerifyAll.lean`, `Experiments.lean`, `DoBench.lean` | benchmark, exact cross-check (37 sizes × 3 seeds × 4 input shapes), unverified experiments, `do`-notation comparison. |

## How the proofs are organised

- **Specs are lists.** `Slice.lean` turns a range of a `UInt64Array` into a list (`slice a off len`), with
  lemmas for splitting (`slice_add`, `slice_cons`, `slice_succ`), for writes (`slice_set_of_not_mem`,
  `at'_set`), and `slice_eq_toList`. Every loop gets a theorem of the shape *result slice = some list
  function of input slices* plus a *frame* clause (positions outside the written range are unchanged).
- **Loops are proved by strong induction on their measure**, unfolding one step (`rw [loop]`, `split`),
  applying the induction hypothesis to the updated array, and rewriting slices. The `if` hypotheses are
  restated in `Nat` form; `omega` closes all index arithmetic after `simp only` with the `UInt64.toNat_*`
  lemmas (`u64`/`u64g`).
- **Reuse.** `mergeLoop_spec` (front merge) is shared by the top-down and bottom-up sorts; the pass spec
  is parametric in the run length, so `sort16` (insertion runs), `sort2` (bidirectional kernel) and
  `sortBlocked` (blocked pass order) only add what is new; `widthLoop_spec` is shared by all of them.
- **Two routes to the final theorem.** Top-down: `sort_toList` shows the array sort computes *exactly*
  the list `mergeSort` of Part 1, so Part 1's theorems transfer. Bottom-up: a small list theory of a pass
  (`mergeRuns`, `ChunkSorted`) gives sortedness and permutation directly.
- **Bidirectional merge.** `MergeBack.lean` proves that merging from the back is the reversed merge of the
  reversed runs (`merge_reverse_eq_reverse_mergeBack`, `drop_merge_eq`); `Bidi.lean` proves the
  interleaved loop writes `take w` of the merge at the front and `drop w` at the back.

## Numbers (this machine, 1M / 10M random `u64`, ms)

| implementation | 1M | 10M |
|---|---|---|
| Lean `BottomUp.sortBlocked` (verified, bidirectional + cache-blocked passes, B = 2^14) | 30–35 | 370–440 |
| Lean `BottomUp.sort2` (verified, bidirectional branchless merge) | 30–34 (5 runs: 30.1–34.2) | 410–500 |
| Lean `BottomUp.sort16` (verified, branchless, insertion runs of 16) | 46 | 568 |
| Lean `BottomUp.sort` (verified, branchless) | 48 | 589 |
| Rust bidirectional + cache-blocked (same algorithm as `sortBlocked`) | 29 | 366 |
| Rust bottom-up, branchless merge (same trick) | 48 | 555 |
| Lean `Fast.sort` (verified top-down, branchless) | 67 | 768 |
| Rust plain bottom-up merge sort | 84 | 972 |
| Rust plain top-down merge sort | 85 | 937 |
| Rust ping-pong top-down (same algorithm as `Fast.sort`) | 97 | 1078 |
| Rust `Vec::sort` (driftsort) | 19 | 269 |
| Rust `Vec::sort_unstable` (ipnsort) | 16 | 183 |
| Lean `BottomUp.sortAdaptive` on already sorted input | 0.6 | 5 |
| Rust `Vec::sort` on already sorted input | 0.4 | 5 |
| Lean, same bottom-up loop written in `do` notation | 1010 | 13072 |

Scaling (`sortdemo`, verified `sortAdaptive2`, vs `Vec::sort`), ms:

| n | Lean | driftsort |
|---|---|---|
| 1 k | 0.021 | 0.017 |
| 10 k | 0.20 | 0.14 |
| 100 k | 2.4 | 1.7 |
| 1 M | 30 | 19 |
| 10 M | 364 | 271 |

## What made the difference (in order of discovery)

1. `Array UInt64` boxes every element (`lean_box_uint64` allocates): sort `Nat`/`UInt32` (tagged) or use an
   unboxed scalar array. We built `UInt64Array` on `lean_sarray` with inline C accessors.
2. `Nat` indices cost ~35%; `UInt64` indices are free (and `omega` handles them after `simp` with
   `UInt64.toNat_add` etc.).
3. `Float.toBits` is an out-of-line runtime call: don't smuggle `u64` through `FloatArray`.
4. Borrow inference: a recursive function whose base case returns its array parameter unchanged gets a
   *borrowed* parameter, so every later write copies the buffer (quadratic). Make every path consume the array.
5. `for`/`while` loops with several `let mut` variables allocate a tuple per iteration (2–14× slower).
   Write hot loops as tail-recursive functions.
6. Two separate buffers beat one `2n` buffer with offsets by ~10% (the compiler can keep the read pointer
   loop-invariant).
7. The per-write exclusivity check is the whole remaining gap to an unchecked C loop (~20%); it cannot be
   removed in pure Lean, but a branch-hinted `if` form is a few percent faster than the `?:` form.
8. Insertion-sorted initial runs of 16 (replacing the first four passes): another ~7%; the width-loop
   spec is parametric in the initial run length, so only the block sort needed a proof.
9. Branchless merge step (`decide (x ≤ y)`, select, add 0/1 to the indices): ~40% faster; same semantics,
   so the proof changes are local. Keep the merge loop in its own module, otherwise clang inlines it into
   the pass loop and loses the benefit.
10. Proof engineering: keep hypotheses in `Nat` form (`have h : k.toNat < n.toNat := h` right after `if h : k < n`),
   rewrite only the goal with a small simp set + `omega`; `simp at *` cannot touch an `if`-hypothesis that
   later proof terms depend on.

## Executable and memory

`lake exe sortdemo 10000000` sorts ten million pseudo-random numbers with `sortAdaptive2`
(`Main.lean`, no `sorry`): 377 ms, peak RSS 167 MB = the 80 MB input + the 80 MB scratch buffer + the
runtime. The binary is 4.5 MB. For comparison, a minimal Rust program sorting the same data with `Vec::sort` peaks at
119 MB (driftsort allocates an n/2 scratch buffer).

## Calling it from C (zero copy)

`MergeSort/Export.lean` exports `mergesort_sort_u64`. A `UInt64Array` *is* a Lean scalar array
(`lean_sarray`, 8-byte elements), so C can allocate one, fill the buffer directly, call the sort and read
the result from the same buffer (the sort runs in place when the refcount is 1). `ffi/build.sh` builds a
4.3 MB static binary (`leanc`, links `libmergesort_MergeSort.a` + `Init`/`Std`/`leanrt`/`uv`/`gmp`):

    sorted 1000000 u64 from C via verified Lean merge sort: 29.0 ms, sorted, in place: yes (same buffer)
    sorted 10000000 u64 from C via verified Lean merge sort: 378.7 ms, sorted, in place: yes (same buffer)

(The export currently points at `sortBlocked`.)

## Verso smoke test

`../site-smoke` is a minimal Verso (`v4.33.0`) manual that requires this project (the `verified-4330` copy)
and renders `{docstring MergeSort.mergeSort}`, `{name}` roles and a `#eval` block whose output is checked at
build time (`leanOutput`). Building Verso from source plus the document took 1 min 38 s; `lake exe site-smoke`
writes the HTML to `_out/`.

## Toolchains

Developed on `v4.33.1`; the whole project also builds unchanged on `v4.33.0` (the Verso `v4.33.0` pairing),
with the same axioms.

## Std.Do / mvcgen

`Std.Do` and `mvcgen` exist in this toolchain (experimental). They target `do`-notation programs; the same
bottom-up loop written with `let mut`/`while` in `Id.run do` compiles to a loop that allocates the state
tuple on every iteration (`DoBench.lean`: 1010 ms vs 48 ms). So for the *fast* code the natural proof style
is the one used here: tail-recursive functions, equational specs about slices, `omega` for indices.
`mvcgen` would be a good fit for the simple copy loops if they were written in `do` notation.

## Bullet 3 research: what `Vec::sort` (driftsort) does

- Scans for natural runs (`find_existing_run`, sorted or strictly reversed; min run length ~`sqrt(len)`,
  `MIN_SQRT_RUN_LEN = 64`), otherwise `create_run` makes a run by small-sorting.
- Small-sort: for ≤ 32 elements (`SMALL_SORT_GENERAL_THRESHOLD`), sorting networks `sort4_stable` /
  `sort8_stable` built from the branchless `swap_if_less` (cmov), then insertion sort to length, then a
  branchless `bidirectional_merge` (`merge_up` / `merge_down` advance pointers arithmetically).
- Merge policy: a run stack (≤ 66 entries) with powersort's `merge_tree_depth` heuristic; runs are merged
  lazily ("logical merge": two unsorted runs that fit in scratch stay one unsorted run and get
  quicksorted later, `stable_quicksort`), physical merges use a standard merge into a scratch buffer of
  `max(len - len/2, 48)` elements.
- Achieves exactly `n - 1` comparisons on sorted or reversed inputs.
The pieces closest to what we have: the branchless merge (done), small-sort networks for runs of ≤ 32
(insertion start gave only ~7% here; networks should do better), and natural-run detection.

Now verified as `sort2` (see the file table). Originally measured as a prototype (`Experiments.lean`): the **bidirectional branchless merge** (front and
back halves merged in one interleaved loop, used for equal-length runs, i.e. every pair except the last
in a pass) gives 31.8 ms at 1M and 448 ms at 10M, versus 52 / 616 for the verified branchless bottom-up
and 19 / 269 for driftsort. Exact on all tested sizes. Its correctness argument (each direction consumes
exactly `w` elements of two `w`-runs, so no run is ever overrun, and consistent tie-breaking keeps the two
halves disjoint) is formalised in `Bidi.lean`/`BidiSort.lean` on top of the list-level lemma
`drop_merge_eq` in `MergeBack.lean`.

Five-run spread at 1M (ms): `sort16` 45.6–46.1, `BottomUp.sort` 47.2–49.5, `Fast.sort` 67–69,
Rust branchless 45.8–47.1, Rust plain 80–83, driftsort 18.2–18.7. Unchecked-write floor for the branchless
Lean merge: 45–46 (so the refcount check now costs ~8%).

## Reproduce

A clean `lake build` of the whole library (all proofs) takes about 52 s on this machine; the heaviest
modules are `Bidi` (17 s, the bidirectional loop spec), `Correct` (10 s) and `BidiSort` (7 s). The code-only
modules build in 1–3 s each.

```
./check.sh            # build, exact cross-check, axioms of every theorem, benchmark
cd rust && cargo run --release -- 1000000
./ffi/build.sh        # the C demo (needs leanc)
```
