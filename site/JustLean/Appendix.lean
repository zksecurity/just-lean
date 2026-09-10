import VersoManual
import JustLean.Blocks

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open JustLean

set_option pp.rawOnError true

#doc (Manual) "Appendix: reproducing and pitfalls" =>

# Reproducing everything

The repository is [zksecurity/just-lean](https://github.com/zksecurity/just-lean). `check.sh` builds
the library, cross-checks every sort against a reference on 37 sizes, 3 seeds and 8 input shapes,
prints the axioms of every theorem, greps for `sorry`, and runs the benchmark:

```
./check.sh
```

The individual commands:

```
lake build                              # library, proofs, static and shared library
lake exe sortdemo 1000000               # the verified driftsort on a million numbers
lake exe listbench 1000000              # Part 1's list sort
lake exe msbench 1000000 [shape]        # Part 2 sorts; shape = random | runs8 | swaps1 | sawtooth
lake exe driftbench 1000000 duel 10 [shape]   # Part 3: interleaved rounds against the port
lake exe driftbench verify              # cross-check of the driftsort on all shapes
lake exe verifyall                      # cross-check of the Part 2 sorts
./ffi/build.sh 1000000                  # the C program linked against the static library
cd lab/rust && cargo run --release -- 1000000 [shape]   # the Rust comparison
```

The numbers on these pages were measured on one Linux machine in September 2026, with Lean
`v4.33.0`, and they move by about a millisecond between runs. Only the interleaved `duel` mode
compares implementations reliably: it alternates them on the same input and reports the median.

This site is built from `site/` with `lake build && lake exe just-lean-site`, which elaborates every
Lean block against the library, compiles and runs the Part 1 program, and writes HTML to `_out/`.

# Pitfalls, in the order we met them

These are the things that cost the most time. None of them is documented in one place, and each of
them is easy to check for.

1. `Array UInt64` boxes every element. Use `Nat`/`UInt32` (which are tagged) or an unboxed scalar
   array.

2. `Nat` indices cost about a third in a hot loop. `UInt64` indices cost nothing, and `omega` handles
   them after `simp` with the `UInt64.toNat_*` lemmas.

3. `Float.toBits` is an out-of-line call. Do not smuggle `u64` through `FloatArray`.

4. A recursive function whose base case returns its array parameter unchanged gets a borrowed
   parameter, and every write in the loop then copies the buffer. Make every path consume the array.

5. `for` and `while` loops with several `let mut` variables allocate a tuple per iteration. Write hot
   loops as tail-recursive functions.

6. Two separate buffers beat one buffer of twice the size with offsets, by about 10%.

7. The per-write exclusivity check is the gap to an unchecked C loop, about 20%. A branch-hinted `if`
   form is a few percent faster than the `?:` form.

8. A branchless merge step (compare, select, add 0 or 1 to the index) is 40% faster than an `if`.
   Keep the merge loop in its own module, or the C compiler inlines it and undoes the effect.

9. In proofs, restate an `if` hypothesis in `Nat` form immediately and rewrite only the goal.
   `simp at *` cannot touch a hypothesis that later proof terms depend on.

10. Look at what the compiler was given. A predicate passed as a function of a `Bool` was
    specialised on a variable, not on the literal at the call site, after common-subexpression
    elimination had merged the two. Named functions per mode fixed it.

11. The order of independent operations in a loop body changes the generated assembly. Storing the
    element before computing the increment gave an `adc`.

12. Measure with interleaved rounds. Sequential runs of a benchmark suite drift by a millisecond,
    which is the size of most of the effects above.

# About

The code, the proofs and this text were produced with Claude (Anthropic) over two days in September
2026, directed by the author. Everything that matters is checked by Lean; the prose is the part to
be skeptical of.
