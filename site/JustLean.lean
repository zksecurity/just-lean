import VersoManual
import JustLean.Blocks
import JustLean.Part1
import JustLean.Part2
import JustLean.Part3
import JustLean.Appendix

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open JustLean

#doc (Manual) "Just Lean: a verified, fast sort" =>

%%%
authors := ["Gregor Mitschabaude"]
%%%

Lean is mostly known as a proof assistant. It is also a programming language with a native compiler,
and one file can hold a specification, an implementation, a machine-checked proof that the
implementation meets the specification, and a `main`. There is no second language to bridge to and
no second toolchain to keep in sync.

This tutorial goes through that pipeline on one example, sorting, three times over:

1. A merge sort on lists that is short enough to read, with a proof that is short enough to read.
2. The same idea on an unboxed array of `UInt64`, fifteen times faster, with the proof kept.
3. A port of the algorithm behind Rust's `Vec::sort`, verified, and a little faster than our port of it in unverified Lean.

All three compile to native binaries. Everything is total (no `partial`), nothing is `sorry`, and every
theorem depends only on Lean's standard axioms. The prompt was this exchange:

{tweet}

*One repository.* The whole thing is one repository, [zksecurity/just-lean](https://github.com/zksecurity/just-lean).
Every Lean snippet on these pages is elaborated when the site is built, against the code in that
repository, so what you read is what was checked. The numbers below are for one million and ten
million pseudo-random 64-bit integers, in milliseconds, on one machine (see the appendix for how they
were measured).

:::table +header
*
  * implementation
  * 1M
  * 10M
*
  * Part 1: merge sort on lists
  * 770
  * 12300
*
  * Part 2: bottom-up merge sort on an unboxed array
  * 50
  * 590
*
  * Part 3: verified driftsort
  * 27
  * 300
*
  * Rust `Vec::sort` (driftsort)
  * 19
  * 270
*
  * Rust, a plain merge sort on `Vec<u64>`
  * 84
  * 970
:::

*What is trusted.* The theorems are about the _model_ of the array, an ordinary `Array UInt64`. At runtime the array is a
flat buffer of 8-byte elements, and five short C snippets in one file
(`MergeSort/UInt64Array.lean`: size, read, write, allocate, plus the batched writes) are trusted to
implement the model. That is the same arrangement Lean's own `ByteArray` and `FloatArray` use. Beyond
it: Lean's kernel, compiler and runtime, and clang.

*Following along.* You need [elan](https://github.com/leanprover/elan) (which installs Lean and Lake from the
`lean-toolchain` file) and a C toolchain. Rust is only needed for the comparison programs.

```
git clone https://github.com/zksecurity/just-lean
cd just-lean
lake build                      # the library and its proofs
lake exe sortdemo 1000000       # sort a million numbers with the verified driftsort
./check.sh                      # build, cross-check, print axioms, benchmark
```

Part 1 assumes no Lean beyond what a curious reader can pick up as it goes. Parts 2 and 3 assume
you have seen a `termination_by` and a `simp` before.

{include 0 JustLean.Part1}

{include 0 JustLean.Part2}

{include 0 JustLean.Part3}

{include 0 JustLean.Appendix}
