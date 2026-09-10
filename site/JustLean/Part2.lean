import VersoManual
import JustLean.Blocks
import MergeSort.BottomUp
import MergeSort.BottomUpCorrect
import MergeSort.Export

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open JustLean
open Verso.Code.External

set_option pp.rawOnError true
set_option verso.code.warnLineLength 0
set_option verso.exampleProject ".."

#doc (Manual) "Part 2: make it fast, keep the proof" =>

%%%
file := "part-2"
tag := "part-2"
%%%

Part 1's sort spends its time on memory: every number is a heap object, every list cell is another,
and each merge pass allocates a new list. Two changes fix that, and neither makes the program harder
to read: sort an array of unboxed 64-bit integers, in place, and index it with `UInt64` instead of
`Nat`. What changes is the proof, which is no longer short. This part shows the code in full and the
proof by its statements; the tactic scripts are in the repository.

# An unboxed array
%%%
tag := "unboxed-array"
%%%

`Array UInt64` is not what it sounds like: each element is a separate heap object, because the
`Array` type is generic and stores pointers. Lean's runtime does have flat arrays of fixed-size
elements (`lean_sarray`); the standard library exposes `ByteArray` and `FloatArray` on top of it,
and nothing for `UInt64`. So we make one, in the same way the standard library makes `FloatArray`.

The type has a _model_, an ordinary `Array UInt64`, and the proofs are about the model. At runtime,
each operation is a line of C on the flat buffer, attached with `@[extern c inline]`:

```anchor UInt64Array (module := MergeSort.UInt64Array)
/-- An unboxed array of `UInt64`. The field is the *model* used by proofs; at runtime the value is a
    flat `lean_sarray` of 8-byte elements, and every operation below is implemented by inline C. -/
structure UInt64Array where
  /-- The model: the elements as an ordinary `Array`. Never used at runtime. -/
  data : Array UInt64
```

```anchor get (module := MergeSort.UInt64Array)
/-- Read element `i`. No bounds check at runtime: the proof `h` is the bounds check. -/
@[extern c inline "((uint64_t*)lean_sarray_cptr(#1))[#2]"]
def get (a : @& UInt64Array) (i : UInt64) (h : i.toNat < a.size := by u64) : UInt64 := a.data[i.toNat]

/-- `a[i]` is `a.get i`; the bounds proof is found by the same tactic (see the end of this file). -/
instance : GetElem UInt64Array UInt64 UInt64 (fun a i => i.toNat < a.size) where
  getElem a i h := a.get i h
```

```anchor set (module := MergeSort.UInt64Array)
/-- Write element `i`. In place if `a` is unshared, otherwise copy-on-write. -/
@[extern c inline "({ lean_object* _a = #1; if (__builtin_expect(!lean_is_exclusive(_a), 0)) _a = lean_copy_float_array(_a); ((uint64_t*)lean_sarray_cptr(_a))[#2] = #3; _a; })"]
def set (a : UInt64Array) (i : UInt64) (v : UInt64) (h : i.toNat < a.size := by u64) : UInt64Array :=
  ⟨a.data.set i.toNat v h⟩
```

```anchor zeros (module := MergeSort.UInt64Array)
/-- A zero-filled array of length `n`. -/
@[extern c inline "({ size_t _n = lean_unbox(#1); lean_object* _a = lean_alloc_sarray(8, _n, _n); __builtin_memset(lean_sarray_cptr(_a), 0, 8 * _n); _a; })"]
def zeros (n : @& Nat) : UInt64Array := ⟨Array.replicate n 0⟩
```

This is the point where something is trusted rather than proved, so it deserves to be spelled out.
The theorems on this page are about the model. The claim that the C above implements the model is
not proved; it is read. That is the same arrangement the standard library uses for every array type.
`FloatArray.uget` is declared `@[extern "lean_float_array_uget"]`, and its C in `lean.h` is:

```
static inline double lean_float_array_uget(b_lean_obj_arg a, size_t i) {
    return lean_float_array_cptr(a)[i];
}

static inline lean_obj_res lean_float_array_uset(lean_obj_arg a, size_t i, double d) {
    lean_obj_res r;
    if (lean_is_exclusive(a)) r = a;
    else r = lean_copy_float_array(a);
    double * it = lean_float_array_cptr(r) + i;
    *it = d;
    return r;
}
```

Ours is the same code with `uint64_t` in place of `double`. `Array.uget` and `Array.uset`, which
Part 1's `List` code does not use but every array program does, are `extern` in the same way. So the
trusted base of this part is Lean's trusted base plus four lines that a reader can compare with the
lines above, and the cross-checks in `check.sh` exercise them against core's `Array.qsort` on
thousands of inputs. It is a small thing to trust, but it is ours and not the standard library's, and
a `UInt64Array` in the standard library would remove it. If you want zero lines of your own C today,
sort `Array Nat` with `USize` indices instead: a `Nat` below 2^63 is a tagged machine word, and the
same loop costs about 13% more from the scalar checks on each access.

Two things to notice about the accessors. `get` takes the bounds proof as an argument, and the
argument has a default: `by u64`, a small tactic defined in the same file that unfolds `UInt64`
arithmetic to `Nat` and calls `omega`. The `GetElem` instance next to it routes `a[i]` to `get` with
the same tactic discharging the bound, so the code reads like any other Lean array code, and an index
that cannot be proved in bounds does not compile. There is no bounds check at runtime.

`set` writes in place when the array is not shared. That is the usual Lean rule: values are immutable,
but the runtime reuses a buffer whose reference count is one. The hot loops below are written so that
this is always the case.

# The sort
%%%
tag := "bottom-up-sort"
%%%

A bottom-up merge sort needs no recursion: pass one merges runs of length 1 into runs of length 2, the
next pass runs of length 2 into 4, and so on. Each pass reads one buffer and writes the other, then the
two swap roles. The input array is one of the buffers, so the sort works in place with one scratch
buffer of the same size.

The merge loop is where the time goes. It reads both candidates, selects the smaller one, and
advances the index of the side it came from by adding 0 or 1. There is no branch on the comparison,
and the C compiler turns the selects into conditional moves. This one change is worth about 40%
compared to an `if`, because a branch on random data is mispredicted half the time.

```anchor mergeLoop (module := MergeSort.BottomUpMerge)
/-- Merge `src[i, mid)` and `src[j, hi)` (both sorted) into `dst[k, hi)`. -/
def mergeLoop (mid hi i j k : UInt64) (src dst : UInt64Array)
    (hsz : dst.size < 2 ^ 64 := by u64)
    (hs : hi.toNat ≤ src.size := by u64) (hd : hi.toNat ≤ dst.size := by u64)
    (hmid : mid.toNat ≤ hi.toNat := by u64) (hi' : i.toNat ≤ mid.toNat := by u64)
    (hj : j.toNat ≤ hi.toNat := by u64) (hinv : i.toNat + j.toNat = k.toNat + mid.toNat := by u64) :
    { b : UInt64Array // b.size = dst.size } :=
  if hk : k < hi then
    have hk : k.toNat < hi.toNat := hk
    if hi'' : i < mid then
      have hi'' : i.toNat < mid.toNat := hi''
      if hj' : j < hi then
        have hj' : j.toNat < hi.toNat := hj'
        -- Branchless step: read both candidates, select the smaller one, advance its index.
        -- (The C compiler turns these selects into conditional moves: no branch to mispredict.)
        let x := src[i]
        let y := src[j]
        let takeLeft : Bool := decide (x ≤ y)
        let di : UInt64 := if takeLeft then 1 else 0
        have hdi : di.toNat ≤ 1 := by show (if takeLeft then (1 : UInt64) else 0).toNat ≤ 1; split <;> decide
        Fast.castSize (mergeLoop mid hi (i + di) (j + (1 - di)) (k + 1) src
          (dst.set k (if takeLeft then x else y))) (by simp)
      else
        Fast.castSize (mergeLoop mid hi (i + 1) j (k + 1) src (dst.set k (src[i]))) (by simp)
    else
      have hi'' : ¬ i.toNat < mid.toNat := hi''
      Fast.castSize (mergeLoop mid hi i (j + 1) (k + 1) src (dst.set k (src[j]))) (by simp)
  else ⟨dst, rfl⟩
termination_by hi.toNat - k.toNat
decreasing_by all_goals u64
```

The proofs in the signature are the loop invariants: both runs lie inside the buffers, `i` is inside
the left run, `j` inside the right one, and the output position `k` is where it should be. All of
them are auto-parameters, so the recursive call writes none of them. The result type
`{ b // b.size = dst.size }` carries the one fact every caller needs.

The merge loop sits in its own module. Otherwise clang inlines it into the pass loop and loses the
branchless code.

A pass merges adjacent pairs of runs and stops at the end; the width loop doubles the run length
until it covers the array:

```anchor passLoop (module := MergeSort.BottomUp)
/-- One pass: merge the runs `[lo, lo+w)` and `[lo+w, lo+2w)` (clipped to `n`) from `src` into
    `dst`, then continue at `lo + 2w`. -/
def passLoop (n w lo : UInt64) (src dst : UInt64Array)
    (hn : n.toNat < 2 ^ 62 := by u64) (hs : n.toNat ≤ src.size := by u64)
    (hd : n.toNat ≤ dst.size := by u64) (hdsz : dst.size < 2 ^ 64 := by u64)
    (hw : 1 ≤ w.toNat ∧ w.toNat < n.toNat := by u64) : { b : UInt64Array // b.size = dst.size } :=
  if h : lo < n then
    have h : lo.toNat < n.toNat := h
    let mid := if lo + w ≤ n then lo + w else n
    let hi := if lo + 2 * w ≤ n then lo + 2 * w else n
    have hmid : mid.toNat = min (lo.toNat + w.toNat) n.toNat := by
      show (if lo + w ≤ n then lo + w else n).toNat = _; split <;> u64
    have hhi : hi.toNat = min (lo.toNat + 2 * w.toNat) n.toNat := by
      show (if lo + 2 * w ≤ n then lo + 2 * w else n).toNat = _; split <;> u64
    let ⟨b, hb⟩ := mergeLoop mid hi lo mid lo src dst
    Fast.castSize (passLoop n w (lo + 2 * w) src b) hb
  else ⟨dst, rfl⟩
termination_by n.toNat - lo.toNat
decreasing_by u64
```

```anchor widthLoop (module := MergeSort.BottomUp)
/-- Double the run length until it covers the array; the result is the buffer that was last
    written (or `src` itself if nothing had to be done). -/
def widthLoop (n w : UInt64) (src dst : UInt64Array)
    (hn : n.toNat < 2 ^ 62 := by u64) (hs : n.toNat = src.size := by u64)
    (hd : n.toNat = dst.size := by u64) (hw : 1 ≤ w.toNat := by u64) :
    { b : UInt64Array // b.size = src.size } :=
  if h : w < n then
    have h : w.toNat < n.toNat := h
    let ⟨b, hb⟩ := passLoop n w 0 src dst
    Fast.castSize (widthLoop n (2 * w) b src (hs := by rw [hb]; exact hd)) (by omega)
  else ⟨src, rfl⟩
termination_by n.toNat - w.toNat
decreasing_by u64
```

```anchor sort (module := MergeSort.BottomUp)
/-- Bottom-up merge sort of an unboxed `UInt64` array, in place (plus one scratch buffer). -/
def sort (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : UInt64Array :=
  let n : UInt64 := xs.size.toUInt64
  have hn : n.toNat = xs.size := by simp [n]; omega
  (widthLoop n 1 xs (zeros xs.size)).1
```

The `2 ^ 62` bound on the size is there so that `2 * w` and `lo + 2 * w` cannot overflow a `UInt64`.

# Three things the runtime cares about
%%%
tag := "runtime"
%%%

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
%%%
tag := "part-2-proof"
%%%

The specification is the one from Part 1, and Part 1's `merge` is used as the reference: what the
loop computes is described as a list. To connect the two, a range of the array is turned into a list:

```anchor slice (module := MergeSort.Slice)
/-- The list `[a[off], a[off+1], ..., a[off+len-1]]`. -/
def slice (a : UInt64Array) (off len : Nat) : List UInt64 :=
  (List.range len).map (fun t => a.at' (off + t))
```

Every loop gets a theorem of the same shape: the slice it wrote equals some list function of the
slices it read, and every position outside that range is unchanged. The second half, the _frame_
clause, is what lets the theorem of one loop be used inside the proof of the next. For the merge loop:

```anchor mergeLoop_spec (module := MergeSort.BottomUpCorrect)
/-- What the merge loop does to `dst[lo, hi)`; `src` is only read. -/
theorem mergeLoop_spec (mid hi : UInt64) (src : UInt64Array) (lo : Nat) :
    ∀ (n : Nat) (i j k : UInt64) (dst : UInt64Array) hsz hs hd hmid hi' hj hinv,
    n = hi.toNat - k.toNat → lo ≤ k.toNat →
    (mergeLoop mid hi i j k src dst hsz hs hd hmid hi' hj hinv).1.slice lo (hi.toNat - lo) =
      dst.slice lo (k.toNat - lo) ++
        merge (src.slice i.toNat (mid.toNat - i.toNat)) (src.slice j.toNat (hi.toNat - j.toNat)) ∧
    ∀ x, (x < k.toNat ∨ hi.toNat ≤ x) →
      (mergeLoop mid hi i j k src dst hsz hs hd hmid hi' hj hinv).1.at' x = dst.at' x
```

The proof is by strong induction on `hi - k`: unfold one step of the loop, apply the induction
hypothesis to the array after the write, and rewrite slices. One lemma from `Slice.lean` does most of
the work, namely that a write outside a range does not change the slice of that range:

```anchor slice_set_of_not_mem (module := MergeSort.Slice)
/-- `slice` only depends on the elements in range: writing outside the range changes nothing. -/
theorem slice_set_of_not_mem (a : UInt64Array) (i : UInt64) (v : UInt64) (hi) (off len : Nat)
    (h : i.toNat < off ∨ off + len ≤ i.toNat) : (a.set i v hi).slice off len = a.slice off len
```

A pass merges adjacent runs; the list function that describes it, {name}`MergeSort.BottomUp.mergeRuns`, is
defined by recursion on the list, and a short theory says that a pass turns sorted runs of length
`w` into sorted runs of length `2w` ({name}`MergeSort.BottomUp.chunkSorted_mergeRuns`) and is a permutation
({name}`MergeSort.BottomUp.mergeRuns_perm`). The pass and width loops then have the expected statements:

```anchor passLoop_spec (module := MergeSort.BottomUpCorrect)
/-- What one pass does: `dst[lo, n)` becomes the merged runs of `src[lo, n)`; nothing else changes. -/
theorem passLoop_spec (n w : UInt64) (src : UInt64Array) (hw0 : 0 < w.toNat) :
    ∀ (m : Nat) (lo : UInt64) (dst : UInt64Array) hn hs hd hdsz hw, m = n.toNat - lo.toNat →
    (passLoop n w lo src dst hn hs hd hdsz hw).1.slice lo.toNat (n.toNat - lo.toNat) =
      mergeRuns w.toNat hw0 (src.slice lo.toNat (n.toNat - lo.toNat)) ∧
    ∀ x, (x < lo.toNat ∨ n.toNat ≤ x) →
      (passLoop n w lo src dst hn hs hd hdsz hw).1.at' x = dst.at' x
```

```anchor widthLoop_spec (module := MergeSort.BottomUpCorrect)
/-- Doubling the run length until it covers the array yields a sorted permutation. -/
theorem widthLoop_spec (n : UInt64) (hn2 : n.toNat < 2 ^ 62) :
    ∀ (m : Nat) (w : UInt64) (src dst : UInt64Array) hn hs hd hw, m = n.toNat - w.toNat →
    ChunkSorted w.toNat (by omega) (src.slice 0 n.toNat) →
    Sorted ((widthLoop n w src dst hn hs hd hw).1.slice 0 n.toNat) ∧
    ((widthLoop n w src dst hn hs hd hw).1.slice 0 n.toNat).Perm (src.slice 0 n.toNat)
```

And the sort itself:

```anchor sort_sorted (module := MergeSort.BottomUpCorrect)
/-- The bottom-up sort produces a sorted list. -/
theorem sort_sorted (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : Sorted (sort xs hsz).data.toList
```

```anchor sort_perm (module := MergeSort.BottomUpCorrect)
/-- The bottom-up sort produces a permutation of its input. -/
theorem sort_perm (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : (sort xs hsz).data.toList.Perm xs.data.toList
```

The proofs are about 250 lines for the loops plus 110 lines of list theory. Two habits made them
go smoothly. Right after `if h : k < n`, restate the hypothesis in `Nat` form
(`have h : k.toNat < n.toNat := h`) and never touch it again, because the proof terms of the auto-parameters depend on
the original. And rewrite only the goal, with a small `simp only` set followed by `omega`, rather than
`simp at *`.

# Numbers
%%%
tag := "part-2-numbers"
%%%

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
%%%
tag := "from-c"
%%%

A `UInt64Array` is a Lean scalar array, so a C program can allocate one, fill the buffer, hand it to
the sort and read the result from the same buffer. There is no marshalling. The Lean side is an
exported function:

```anchor sortExport (module := MergeSort.Export)
/-- Exported symbol for other languages. The size precondition is checked at runtime. -/
@[export mergesort_sort_u64]
def sortExport (xs : UInt64Array) : UInt64Array :=
  if h : xs.size < 2 ^ 62 then DriftSort.sort xs h else xs
```

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
