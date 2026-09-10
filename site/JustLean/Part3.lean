import VersoManual
import JustLean.Blocks
import MergeSort.DriftSort
import MergeSort.DriftCorrectLoop

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open JustLean

set_option pp.rawOnError true
set_option verso.code.warnLineLength 0

#doc (Manual) "Part 3: Vec::sort territory" =>

Part 2's sort does the same work on every input and takes about 2.5 times as long as Rust's
`Vec::sort` on random data. This part closes most of that gap by porting the algorithm behind
`Vec::sort`, driftsort, to Lean and verifying it. The details are in the repository; this page says
what the algorithm is, what was proved, and what came out.

# What Vec::sort does

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
line-by-line translation of it for `u64` in which every array access carries its bounds proof.

# The proof

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

{src DriftSort.RunsOK}

* The quicksort is proved generic in the range sorter it falls back to (`QuickSpec`), and its
  precondition is the pivot of the left ancestor: every element of the range is at least that value,
  which is what makes an equal-element partition a constant run.

The two theorems about the entry point are the same as Part 2's:

{docstring DriftSort.sort_sorted}

{docstring DriftSort.sort_perm}

Both depend on `propext`, `Classical.choice` and `Quot.sound` only; `check.sh` prints the axioms of
every theorem in the repository.

# Making it fast

The first verified version ran at 41 ms on a million random `u64`, against 19 for Rust. Five changes
brought it to 27, all of them measured one at a time with interleaved runs on the same input, and none
of them touched the specifications.

1. *Batched stores.* The four-element sorting network writes its result with one exclusivity check. Logically it is
   four `set`s, and that is what the proof sees.

2. *A ping-pong quicksort.* Rust's partition writes into the scratch buffer and copies the result
   back. The Lean version does not copy back: it recurses with the two buffers swapped, and a flag
   records which buffer the result must end up in. That saves one pass over the data per level. Rust
   cannot do this in general, since its element type may have a destructor; for `u64` it is free.
   It is also only correct because every kernel is proved not to touch the scratch buffer outside its
   range: a finished sibling's output lives in what the next call uses as scratch. The frame clause
   was already in the theorems, so the change to the proofs was mechanical.

3. *One partition loop per mode.* The partition predicate was passed as a function of a `Bool`
   flag. The compiler had merged the literal `false` at the call site with another variable and
   specialised the loop on a variable, so the mode was tested per element. Two named predicates gave
   two loops.

4. *Store before counting.* In the partition scan, writing the element before computing the 0/1
   increment lets clang fold the increment into the compare (an `adc` instruction).

5. *A fast path for one run.* If the initial scan finds that the whole input is one run, return it
   without allocating the scratch buffer.

Three of the five came from reading the generated C and its assembly rather than the Lean. The
compiled code is in `.lake/build/ir`, and it is readable.

# Results

Interleaved rounds on the same inputs, medians, milliseconds. Rust is `Vec::sort` compiled with
`-O3`.

:::table +header
*
  * input
  * verified `DriftSort.sort`
  * Lean port, unverified
  * Part 2 sort
  * Rust `Vec::sort`
*
  * 1M random
  * 27
  * 28
  * 50
  * 19
*
  * 10M random
  * 301
  * 344
  * 590
  * 270
*
  * 1M, 8 sorted runs
  * 4.9
  * 7.8
  * 50
  * 7.3
*
  * 1M sawtooth
  * 17
  * 24
  * 50
  * 23
*
  * 1M sorted
  * 0.5
  * 0.6
  * 50
  * 0.4
*
  * 1M reversed
  * 0.8
  * 0.9
  * 50
  * 0.6
*
  * 1M, 1% swaps
  * 22
  * 22
  * 50
  * 14
:::

The verified sort is faster than the unverified port on every input, mostly because of the
ping-pong quicksort. The remaining gap to Rust on random data is about 1.4×. Most of it is the
exclusivity check on every store, which Rust does not need, and the partition scan being bound by
instruction count rather than by that check; unrolling it did not help.

# What is not verified

The same things as in Part 2: the C behind the array primitives, and the Lean toolchain. The
unverified port in `lab/` is only a benchmark reference; nothing on this page depends on it. What is
verified is the sort you get from `lake exe sortdemo` and from the C program in `ffi/`.
