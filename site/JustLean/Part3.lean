import VersoManual
import JustLean.Blocks
import MergeSort.DriftSort
import MergeSort.DriftCorrectLoop

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open JustLean
open Verso.Code.External

set_option pp.rawOnError true
set_option verso.code.warnLineLength 0
set_option verso.exampleProject ".."

#doc (Manual) "Part 3: Vec::sort territory" =>

%%%
file := "part-3"
tag := "part-3"
%%%

Part 2's sort does the same work on every input and takes about 2.5 times as long as Rust's
`Vec::sort` on random data. This part closes most of that gap by porting the algorithm behind
`Vec::sort`, driftsort, to Lean and verifying it. The details are in the repository; this page says
what the algorithm is, what was proved, and what came out.

# What Vec::sort does
%%%
tag := "what-vec-sort-does"
%%%

Rust's stable sort (`core::slice::sort::stable`, "driftsort") is a merge sort that adapts to the
input. Where the time goes on one million `u64`, in milliseconds:

:::table +header
*
  * input
  * Part 2 sort
  * driftsort
*
  * random
  * 50
  * 19
*
  * 8 sorted runs concatenated
  * 50
  * 7
*
  * sorted, then 1% random swaps
  * 50
  * 14
*
  * sorted runs of 1000 (sawtooth)
  * 50
  * 23
*
  * sorted, or reversed
  * 50
  * 0.5
:::

Four ideas account for the difference.

* *Natural runs.* The input is scanned for stretches that are already sorted (or strictly
  descending, which are reversed in place). A sorted input is one run, and the sort is finished after
  one pass over it.

* *A good merge order.* Runs go on a stack and are merged lazily, in the order a balanced merge tree
  would (the "powersort" policy), so that short runs are merged with short runs.

* *A stable quicksort for the rest.* Stretches with no run are sorted by a quicksort that partitions
  into the scratch buffer, so it stays stable, with pivots from a median of medians. It beats a merge
  sort on random data because its inner loop is a scan with no data-dependent branch.

* *Sorting networks at the bottom.* Blocks of up to 32 elements are sorted by fixed comparator
  networks and insertion, then merged bidirectionally.

The Rust source is about 1900 lines across four files. The Lean version, {name}`DriftSort.sort`, is a
line-by-line translation of it for `u64` in which every array access carries its bounds proof:

```anchor sort (module := MergeSort.DriftSort)
/-- driftsort for `u64`, bounds-safe. An input that is one natural run (sorted, or descending and
    reversed in place) needs no scratch buffer; everything else gets one of the same size. -/
def sort (xs : A) (hsz : xs.size < 2 ^ 62) : A :=
  let n : UInt64 := xs.size.toUInt64
  have hn : n.toNat = xs.size := by simp [n]; omega
  if h2 : n < 2 then xs
  else if n ≤ maxLenAlwaysInsertion then (insertionSortRange 0 n 0 xs (by omega) (by omega) (by simp)).1
  else
    have h2 : 2 ≤ n.toNat := by have := UInt64.not_lt.mp h2; have := UInt64.le_iff_toNat_le.mp this; simpa using this
    let ⟨(e, xs1), _, _, hxs1⟩ := findRun 0 n xs (by omega) (by omega) (by simp; omega)
    have hxs1' : xs1.size = xs.size := hxs1
    if e = n then xs1
    else
      let s := zeros xs.size
      have hs : s.size = xs.size := by simp [s]
      let eager := n ≤ smallSortThreshold * 2
      if eager then (driftSortEager xs1 s 0 n n (by omega) (by rw [hs]; omega) (by omega) (by rw [hs]; omega) (by simp)).1.1
      else (driftSortFull xs1 s 0 n n (by omega) (by rw [hs]; omega) (by omega) (by rw [hs]; omega) (by simp)).1.1
```

# The proof
%%%
tag := "part-3-proof"
%%%

The verified sort is 540 lines; its proofs are 1400. The statements follow Part 2's pattern. Every
kernel gets a theorem that says what slice it wrote, as a list function of the slices it read, and
what it left alone, in both buffers. The frame clause for the scratch buffer is the one addition over
Part 2, and it turned out to matter (below).

Three invariants carry the proof.

* The stable partition writes the elements below the pivot, in their order, followed by the others.
  As a list: `filter p xs ++ filter (not ∘ p) xs`, up to reversal of the second part, which is
  invisible for `u64`.

* The run stack tiles the array from the scan position downward, and every run marked sorted is
  sorted:

```anchor RunsOK (module := MergeSort.DriftCorrectLoop)
/-- `RunsOK rs e a`: the runs `rs` (top first) tile `a` downward from position `e`; the sorted ones are sorted. -/
def RunsOK : List Run → Nat → A → Prop
  | [], _, _ => True
  | r :: rs, e, a => r.len.toNat ≤ e ∧ (r.sorted = true → Sorted (a.slice (e - r.len.toNat) r.len.toNat)) ∧ RunsOK rs (e - r.len.toNat) a
```

* The quicksort is proved generic in the range sorter it falls back to (`QuickSpec`), and its
  precondition is the pivot of the left ancestor: every element of the range is at least that value,
  which is what makes an equal-element partition a constant run.

The two theorems about the entry point are the same as Part 2's:

```anchor sort_sorted (module := MergeSort.DriftCorrectLoop)
/-- The bounds-safe driftsort returns a sorted array. -/
theorem sort_sorted (xs : A) (hsz : xs.size < 2 ^ 62) : Sorted (sort xs hsz).data.toList
```

```anchor sort_perm (module := MergeSort.DriftCorrectLoop)
/-- The bounds-safe driftsort returns a permutation of its input. -/
theorem sort_perm (xs : A) (hsz : xs.size < 2 ^ 62) : (sort xs hsz).data.toList.Perm xs.data.toList
```

Both depend on `propext`, `Classical.choice` and `Quot.sound` only; `check.sh` prints the axioms of
every theorem in the repository.

# Making it fast
%%%
tag := "making-it-fast"
%%%

The first verified version ran at 41 ms on a million random `u64`, against 19 for Rust. Four changes
brought it to 28, all of them measured one at a time with interleaved runs on the same input, and none
of them touched the specifications.

1. *A ping-pong quicksort.* Rust's partition writes into the scratch buffer and copies the result
   back. The Lean version does not copy back: it recurses with the two buffers swapped, and a flag
   records which buffer the result must end up in. That saves one pass over the data per level. Rust
   cannot do this in general, since its element type may have a destructor; for `u64` it is free.
   It is also only correct because every kernel is proved not to touch the scratch buffer outside its
   range: a finished sibling's output lives in what the next call uses as scratch. The frame clause
   was already in the theorems, so the change to the proofs was mechanical.

2. *One partition loop per mode.* The partition predicate was passed as a function of a `Bool`
   flag. The compiler had merged the literal `false` at the call site with another variable and
   specialised the loop on a variable, so the mode was tested per element. Two named predicates gave
   two loops.

3. *Store before counting.* In the partition scan, writing the element before computing the 0/1
   increment lets clang fold the increment into the compare (an `adc` instruction).

4. *A fast path for one run.* If the initial scan finds that the whole input is one run, return it
   without allocating the scratch buffer.

Three of the four came from reading the generated C and its assembly rather than the Lean. The
compiled code is in `.lake/build/ir`, and it is readable.

# Results
%%%
tag := "results"
%%%

Interleaved rounds on the same inputs, medians, milliseconds. Rust is `Vec::sort` compiled with
`-O3`.

:::table +header
*
  * input
  * verified `DriftSort.sort`
  * Part 2 sort
  * Rust `Vec::sort`
*
  * 1M random
  * 28
  * 50
  * 19
*
  * 10M random
  * 301
  * 590
  * 270
*
  * 1M, 8 sorted runs
  * 4.9
  * 50
  * 7.3
*
  * 1M sawtooth
  * 17
  * 50
  * 23
*
  * 1M sorted
  * 0.5
  * 50
  * 0.4
*
  * 1M reversed
  * 0.8
  * 50
  * 0.6
*
  * 1M, 1% swaps
  * 22
  * 50
  * 14
:::

The gap to Rust on random data is about 1.4×. Most of it is the exclusivity check on every store,
which Rust does not need, and the partition scan being bound by instruction count rather than by
that check; unrolling it did not help. On inputs with structure the two are close, and the verified
sort is ahead on some of them.

# What is not verified
%%%
tag := "not-verified"
%%%

The same things as in Part 2: the C behind the array primitives, and the Lean toolchain. What is
verified is the sort you get from `lake exe sortdemo` and from the C program in `ffi/`.
