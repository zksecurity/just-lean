import MergeSort.Fast
/-! Generic loops: the comparison is a parameter of the merge loop; the pass loop takes the merge
    kernel as a parameter so that a specialised kernel can live in its own module. -/
namespace MergeSort.G
open UInt64Array

@[specialize] def mergeLoop (le : UInt64 → UInt64 → Bool) (mid hi i j k : UInt64) (src dst : UInt64Array)
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
        let x := src.get i
        let y := src.get j
        let takeLeft : Bool := le x y
        let di : UInt64 := if takeLeft then 1 else 0
        have hdi : di.toNat ≤ 1 := by show (if takeLeft then (1 : UInt64) else 0).toNat ≤ 1; split <;> decide
        Fast.castSize (mergeLoop le mid hi (i + di) (j + (1 - di)) (k + 1) src
          (dst.set k (if takeLeft then x else y))) (by simp)
      else
        Fast.castSize (mergeLoop le mid hi (i + 1) j (k + 1) src (dst.set k (src.get i))) (by simp)
    else
      have hi'' : ¬ i.toNat < mid.toNat := hi''
      Fast.castSize (mergeLoop le mid hi i (j + 1) (k + 1) src (dst.set k (src.get j))) (by simp)
  else ⟨dst, rfl⟩
termination_by hi.toNat - k.toNat
decreasing_by all_goals u64

/-- The type of a merge kernel: merge `src[lo, mid)` and `src[mid, hi)` into `dst[lo, hi)`. -/
abbrev Kernel := (lo mid hi : UInt64) → (src dst : UInt64Array) →
    dst.size < 2 ^ 64 → hi.toNat ≤ src.size → hi.toNat ≤ dst.size → lo.toNat ≤ mid.toNat → mid.toNat ≤ hi.toNat →
    { b : UInt64Array // b.size = dst.size }

@[specialize] def passLoop (merge : Kernel) (n w lo : UInt64) (src dst : UInt64Array)
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
    let ⟨b, hb⟩ := merge lo mid hi src dst hdsz (by omega) (by omega) (by omega) (by omega)
    Fast.castSize (passLoop merge n w (lo + 2 * w) src b) hb
  else ⟨dst, rfl⟩
termination_by n.toNat - lo.toNat
decreasing_by u64

@[specialize] def widthLoop (merge : Kernel) (n w : UInt64) (src dst : UInt64Array)
    (hn : n.toNat < 2 ^ 62 := by u64) (hs : n.toNat = src.size := by u64)
    (hd : n.toNat = dst.size := by u64) (hw : 1 ≤ w.toNat := by u64) :
    { b : UInt64Array // b.size = src.size } :=
  if h : w < n then
    have h : w.toNat < n.toNat := h
    let ⟨b, hb⟩ := passLoop merge n w 0 src dst
    Fast.castSize (widthLoop merge n (2 * w) b src (hs := by rw [hb]; exact hd)) (by omega)
  else ⟨src, rfl⟩
termination_by n.toNat - w.toNat
decreasing_by u64

end MergeSort.G
