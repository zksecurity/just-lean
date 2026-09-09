import MergeSort.UInt64Array
/-! The merge step of the top-down sort, in its own module so the C compiler optimizes it as one
    separate loop (inlining it into the recursive driver loses the branchless codegen). -/
namespace MergeSort.Fast
open UInt64Array

/-- Re-index a size proof through an equal size. Erased at runtime. -/
@[inline] def castSize {a a' : UInt64Array} (r : { b : UInt64Array // b.size = a'.size })
    (h : a'.size = a.size) : { b : UInt64Array // b.size = a.size } := ⟨r.1, r.2.trans h⟩

/-- Merge `a[s+i, s+mid)` and `a[s+j, s+hi)` (both sorted) into `a[d+k, d+hi)`.
    The invariant `i + j = k + mid` says the output position tracks the two input positions. -/
def mergeLoop (s d mid hi i j k : UInt64) (a : UInt64Array)
    (hsz : a.size < 2 ^ 64 := by u64)
    (hs : s.toNat + hi.toNat ≤ a.size := by u64) (hd : d.toNat + hi.toNat ≤ a.size := by u64)
    (hmid : mid.toNat ≤ hi.toNat := by u64) (hi' : i.toNat ≤ mid.toNat := by u64)
    (hj : j.toNat ≤ hi.toNat := by u64) (hinv : i.toNat + j.toNat = k.toNat + mid.toNat := by u64) :
    { b : UInt64Array // b.size = a.size } :=
  if hk : k < hi then
    have hk : k.toNat < hi.toNat := hk
    if hi'' : i < mid then
      have hi'' : i.toNat < mid.toNat := hi''
      if hj' : j < hi then
        have hj' : j.toNat < hi.toNat := hj'
        -- Branchless step: read both candidates, select the smaller one, advance its index.
        let x := a.get (s + i)
        let y := a.get (s + j)
        let takeLeft : Bool := decide (x ≤ y)
        let di : UInt64 := if takeLeft then 1 else 0
        have hdi : di.toNat ≤ 1 := by show (if takeLeft then (1 : UInt64) else 0).toNat ≤ 1; split <;> decide
        castSize (mergeLoop s d mid hi (i + di) (j + (1 - di)) (k + 1)
          (a.set (d + k) (if takeLeft then x else y))) (by simp)
      else
        castSize (mergeLoop s d mid hi (i + 1) j (k + 1) (a.set (d + k) (a.get (s + i)))) (by simp)
    else
      have hi'' : ¬ i.toNat < mid.toNat := hi''
      castSize (mergeLoop s d mid hi i (j + 1) (k + 1) (a.set (d + k) (a.get (s + j)))) (by simp)
  else ⟨a, rfl⟩
termination_by hi.toNat - k.toNat
decreasing_by all_goals u64


end MergeSort.Fast
