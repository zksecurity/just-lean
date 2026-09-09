import MergeSort.Fast
/-! The merge step of the bottom-up sort, in its own module (so the C compiler keeps it as one
    separately optimized loop instead of inlining it into the pass loop). -/
namespace MergeSort.BottomUp
open UInt64Array

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
        let x := src.get i
        let y := src.get j
        let takeLeft : Bool := decide (x ≤ y)
        let di : UInt64 := if takeLeft then 1 else 0
        have hdi : di.toNat ≤ 1 := by show (if takeLeft then (1 : UInt64) else 0).toNat ≤ 1; split <;> decide
        Fast.castSize (mergeLoop mid hi (i + di) (j + (1 - di)) (k + 1) src
          (dst.set k (if takeLeft then x else y))) (by simp)
      else
        Fast.castSize (mergeLoop mid hi (i + 1) j (k + 1) src (dst.set k (src.get i))) (by simp)
    else
      have hi'' : ¬ i.toNat < mid.toNat := hi''
      Fast.castSize (mergeLoop mid hi i (j + 1) (k + 1) src (dst.set k (src.get j))) (by simp)
  else ⟨dst, rfl⟩
termination_by hi.toNat - k.toNat
decreasing_by all_goals u64


end MergeSort.BottomUp
