# Just Lean: a verified, fast sort

A tutorial on writing a program in Lean, proving it correct, and compiling and running it, on one
example: sorting. The tutorial is at **https://zksecurity.github.io/just-lean/**; this repository is
the code it is built from.

1. **Part 1** (`MergeSort/Simple.lean`): a merge sort on lists that is short enough to read, and a
   proof that it sorts (`mergeSort_correct`).
2. **Part 2** (`MergeSort/UInt64Array.lean`, `BottomUpMerge.lean`, `BottomUp.lean`, `Slice.lean`,
   `Runs.lean`, `BottomUpCorrect.lean`): the same idea on an unboxed `UInt64` array, in place, with
   `UInt64` indices whose bounds proofs are auto-parameters; `BottomUp.sort_sorted`, `sort_perm`.
   Matches the same algorithm in Rust (50 ms per million random `u64`).
3. **Part 3** (`MergeSort/DriftSort.lean`, `DriftCorrect.lean`, `DriftCorrectLoop.lean`, plus the
   building blocks `Net4`, `Bidi`, `SkipMerge`, `FindRun`, `Adaptive`, ...): a verified port of the
   algorithm behind Rust's `Vec::sort` (driftsort); `DriftSort.sort_sorted`, `sort_perm`. 27 ms per
   million random `u64`, against 19 for Rust and 28 for the unverified Lean port in `lab/Drift.lean`.

Everything is total (no `partial`), there is no `sorry`, and every theorem depends only on
`propext`, `Classical.choice`, `Quot.sound`. The trusted part is the five `@[extern c inline]`
snippets in `UInt64Array.lean` (the runtime representation of the array), plus Lean itself.

## Reproduce

```
./check.sh                                  # build, cross-check, axioms, no-sorry grep, benchmark
lake exe sortdemo 1000000                   # the verified driftsort on a million numbers
lake exe listbench 1000000                  # Part 1's list sort
lake exe msbench 1000000 [shape]            # Part 2 sorts; shape = random | runs8 | swaps1 | sawtooth
lake exe driftbench 1000000 duel 10 [shape] # Part 3, interleaved rounds against the unverified port
./ffi/build.sh 1000000                      # a C program linked against the static library
cd lab/rust && cargo run --release -- 1000000 [shape]   # the Rust comparison programs
```

## The site

`site/` is a [Verso](https://github.com/leanprover/verso) manual that depends on this package. Every
Lean block is elaborated against the library when the site is built, the Part 1 program is compiled
and run, and source excerpts are read from the files in this repository.

```
cd site
lake build subverso-extract-mod && lake build && lake exe just-lean-site   # HTML in _out/html-multi
```

## Layout

| path | what |
|---|---|
| `MergeSort/` | the library: sorts and proofs (see the tutorial for a map) |
| `MergeSort/Export.lean`, `ffi/` | `@[export mergesort_sort_u64]` and a C program that calls it, zero copies |
| `Main.lean`, `Bench.lean`, `DriftBench.lean`, `ListBench.lean`, `VerifyAll.lean` | demo, benchmarks, cross-checks |
| `lab/Drift.lean` | the unverified line-by-line port of driftsort, for comparison |
| `lab/rust/` | the Rust programs used for the numbers |
| `site/` | the tutorial |
