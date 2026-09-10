import VersoManual
import JustLean.Blocks
import MergeSort.BottomUp
import MergeSort.BottomUpCorrect
import MergeSort.Export

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open JustLean

set_option pp.rawOnError true
set_option verso.code.warnLineLength 0

#doc (Manual) "Part 2: make it fast, keep the proof" =>

Part 1's sort spends its time on memory: every number is a heap object, every list cell is another,
and each merge pass allocates a new list. Two changes fix that, and neither makes the program harder
to read: sort an array of unboxed 64-bit integers, in place, and index it with `UInt64` instead of
`Nat`. What changes is the proof, which is no longer short. This part shows the code in full and the
proof by its statements; the tactic scripts are in the repository.

# An unboxed array

`Array UInt64` is not what it sounds like: each element is a separate heap object, because the
`Array` type is generic and stores pointers. Lean's runtime does have flat arrays of fixed-size
elements (`lean_sarray`); the standard library exposes `ByteArray` and `FloatArray` on top of it,
and nothing for `UInt64`. So we make one, in the same way the standard library makes `FloatArray`.

The type has a _model_, an ordinary `Array UInt64`, and the proofs are about the model. At runtime,
each operation is a line of C on the flat buffer, attached with `@[extern c inline]`:

{src UInt64Array}

{src UInt64Array.get}

{src UInt64Array.set}

{src UInt64Array.zeros}

Two things to notice. `get` takes the bounds proof as an argument, and the argument has a default:
`by u64`, a small tactic defined in the same file that unfolds `UInt64` arithmetic to `Nat` and calls
`omega`. Call sites therefore look like `a.get i`, and a call that cannot be proved in bounds does not
compile. There is no bounds check at runtime.

`set` writes in place when the array is not shared. That is the usual Lean rule: values are immutable,
but the runtime reuses a buffer whose reference count is one. The hot loops below are written so that
this is always the case.

The file is 110 lines, of which the five `extern` snippets are the trusted part.

# The sort

A bottom-up merge sort needs no recursion: pass one merges runs of length 1 into runs of length 2, the
next pass runs of length 2 into 4, and so on. Each pass reads one buffer and writes the other, then the
two swap roles. The input array is one of the buffers, so the sort works in place with one scratch
buffer of the same size.

The merge loop is where the time goes. It reads both candidates, selects the smaller one, and
advances the index of the side it came from by adding 0 or 1. There is no branch on the comparison,
and the C compiler turns the selects into conditional moves. This one change is worth about 40%
compared to an `if`, because a branch on random data is mispredicted half the time.

{src MergeSort.BottomUp.mergeLoop}

The proofs in the signature are the loop invariants: both runs lie inside the buffers, `i` is inside
the left run, `j` inside the right one, and the output position `k` is where it should be. All of
them are auto-parameters, so the recursive call writes none of them. The result type
`{ b // b.size = dst.size }` carries the one fact every caller needs.

The merge loop sits in its own module. Otherwise clang inlines it into the pass loop and loses the
branchless code.

A pass merges adjacent pairs of runs and stops at the end; the width loop doubles the run length
until it covers the array:

{src MergeSort.BottomUp.passLoop}

{src MergeSort.BottomUp.widthLoop}

{src MergeSort.BottomUp.sort}

The `2 ^ 62` bound on the size is there so that `2 * w` and `lo + 2 * w` cannot overflow a `UInt64`.

# Three things the runtime cares about

Writing the loops as tail-recursive functions rather than `for` loops is deliberate. These three
points cost between 20% and a factor of twenty when we got them wrong, and none of them is visible in
the types.

* *Consume the array on every path.* If a recursive function returns its array parameter unchanged in
  the base case, Lean's borrow inference marks the parameter as borrowed, and every write in the loop
  copies the buffer. The sort becomes quadratic. Returning `⟨dst, rfl⟩` counts as consuming.

* *No tuples in loops.* A `for` loop with several `let mut` variables allocates a tuple on every
  iteration. The same bottom-up sort written that way in `Id.run do` takes 1010 ms instead of 50.
  Tail recursion with the state as arguments keeps everything in registers.

* *The exclusivity check.* Every `set` tests whether the buffer is shared before writing. On these
  loops that is the whole remaining gap to a plain C loop, about 20%. It cannot be removed in Lean as it
  is, but it is a well-predicted branch and it is the price of not having a borrow checker.

`Nat` indices, for comparison, cost about a third. `UInt64` indices cost nothing, and `omega` handles
them once `simp` has rewritten `(i + 1).toNat` to `i.toNat + 1`. That is all `u64` does.

# The proof

The specification is the one from Part 1, and Part 1's `merge` is used as the reference: what the
loop computes is described as a list. To connect the two, a range of the array is turned into a list:

{src UInt64Array.slice}

Every loop gets a theorem of the same shape: the slice it wrote equals some list function of the
slices it read, and every position outside that range is unchanged. The second half, the _frame_
clause, is what lets the theorem of one loop be used inside the proof of the next. For the merge loop:

{docstring MergeSort.BottomUp.mergeLoop_spec}

The proof is by strong induction on `hi - k`: unfold one step of the loop, apply the induction
hypothesis to the array after the write, and rewrite slices. One lemma from `Slice.lean` does most of
the work, namely that a write outside a range does not change the slice of that range:

{docstring UInt64Array.slice_set_of_not_mem}

A pass merges adjacent runs; the list function that describes it, {name}`MergeSort.BottomUp.mergeRuns`, is
defined by recursion on the list, and a short theory says that a pass turns sorted runs of length
`w` into sorted runs of length `2w` ({name}`MergeSort.BottomUp.chunkSorted_mergeRuns`) and is a permutation
({name}`MergeSort.BottomUp.mergeRuns_perm`). The pass and width loops then have the expected statements:

{docstring MergeSort.BottomUp.passLoop_spec}

{docstring MergeSort.BottomUp.widthLoop_spec}

And the sort itself:

{docstring MergeSort.BottomUp.sort_sorted}

{docstring MergeSort.BottomUp.sort_perm}

The proofs are about 250 lines for the loops plus 110 lines of list theory. Two habits made them
go smoothly. Right after `if h : k < n`, restate the hypothesis in `Nat` form
(`have h : k.toNat < n.toNat := h`) and never touch it again, because the proof terms of the auto-parameters depend on
the original. And rewrite only the goal, with a small `simp only` set followed by `omega`, rather than
`simp at *`.

# Numbers

The same algorithm in Rust, with the same tricks (branchless merge, two buffers, in place), is the
fair comparison. One million and ten million random `u64`, milliseconds:

:::table +header
*
  * implementation
  * 1M
  * 10M
*
  * Lean `BottomUp.sort` (verified)
  * 50
  * 590
*
  * Rust, same algorithm
  * 48
  * 555
*
  * Rust, plain bottom-up merge sort (branching merge)
  * 84
  * 970
*
  * Part 1's list sort
  * 770
  * 12300
:::

The verified Lean sort and the Rust translation are within measurement noise of each other. The
remaining gap to `Vec::sort` is algorithmic, and it is what Part 3 is about.

# Calling it from C

A `UInt64Array` is a Lean scalar array, so a C program can allocate one, fill the buffer, hand it to
the sort and read the result from the same buffer. There is no marshalling. The Lean side is an
exported function:

{src MergeSort.sortExport}

The C side (`ffi/main.c`) initialises the Lean runtime and the module, then does exactly that:

```
lean_initialize_runtime_module();
lean_object *res = initialize_mergesort_MergeSort_Export(1, lean_io_mk_world());
lean_io_mark_end_initialization();

lean_object *arr = lean_alloc_sarray(8, n, n);            /* 8-byte elements */
uint64_t *data = (uint64_t *)lean_sarray_cptr(arr);
for (size_t i = 0; i < n; i++) data[i] = next(&s);

lean_object *sorted = mergesort_sort_u64(arr);            /* consumes arr; sorts in place */
uint64_t *out = (uint64_t *)lean_sarray_cptr(sorted);     /* out == data */
```

`ffi/build.sh` builds the library as a static archive and links it with Lean's `leanc`:

```
lake build MergeSort:static
leanc -O2 -o ffi/main ffi/main.c -I "$(lean --print-prefix)/include" \
  .lake/build/lib/libmergesort_MergeSort.a \
  -L "$(lean --print-prefix)/lib/lean" -lInit -lStd -lleanrt -luv -lgmp
./ffi/main 1000000
```

```
sorted 1000000 u64 from C via verified Lean merge sort: 26.4 ms, sorted, in place: yes (same buffer)
```

The binary is static, 4.3 MB, and the exported function in it is the Part 3 sort by now.
