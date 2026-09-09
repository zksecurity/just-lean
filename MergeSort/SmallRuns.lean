import MergeSort.BottomUp
/-!
# Simple trick: start the bottom-up sort from insertion-sorted runs of length 16

The first four merge passes (runs of 1, 2, 4, 8) are replaced by one in-place insertion sort of every
16-element block. The width loop then starts at `w = 16`; its specification is parametric in the
initial run length, so only the block sort needs a new proof.
-/
namespace MergeSort.BottomUp
open UInt64Array

/-- Move `a[k]` left inside the sorted prefix `a[lo, k)` until it is in place. -/
def insertLoop (lo k : UInt64) (a : UInt64Array)
    (hsz : a.size < 2 ^ 64 := by u64) (hk : k.toNat < a.size := by u64) (_hlo : lo.toNat ≤ k.toNat := by u64) :
    { b : UInt64Array // b.size = a.size } :=
  if h : lo < k then
    have h : lo.toNat < k.toNat := h
    let x := a.get k
    let y := a.get (k - 1)
    if x < y then
      Fast.castSize (insertLoop lo (k - 1) ((a.set k y).set (k - 1) x)) (by simp)
    else ⟨a, rfl⟩
  else ⟨a, rfl⟩
termination_by k.toNat
decreasing_by u64

/-- Insertion sort of `a[lo, hi)`: elements `a[lo, k)` are already sorted. -/
def insertionSortRange (lo hi k : UInt64) (a : UInt64Array)
    (hsz : a.size < 2 ^ 64 := by u64) (hhi : hi.toNat ≤ a.size := by u64)
    (_hlo : lo.toNat ≤ k.toNat := by u64) : { b : UInt64Array // b.size = a.size } :=
  if h : k < hi then
    have h : k.toNat < hi.toNat := h
    let ⟨b, hb⟩ := insertLoop lo k a
    Fast.castSize (insertionSortRange lo hi (k + 1) b) hb
  else ⟨a, rfl⟩
termination_by hi.toNat - k.toNat
decreasing_by u64

/-- Insertion-sort every block `[lo, lo + w)` (clipped to `n`). -/
def sortBlocks (n w lo : UInt64) (a : UInt64Array)
    (hsz : a.size < 2 ^ 64 := by u64) (hn : n.toNat ≤ a.size := by u64) (hn2 : n.toNat < 2 ^ 62 := by u64)
    (hw : 1 ≤ w.toNat ∧ w.toNat < n.toNat := by u64) : { b : UInt64Array // b.size = a.size } :=
  if h : lo < n then
    have h : lo.toNat < n.toNat := h
    let hi := if lo + w ≤ n then lo + w else n
    have hhi : hi.toNat ≤ n.toNat := by
      show (if lo + w ≤ n then lo + w else n).toNat ≤ _; split <;> u64
    let ⟨b, hb⟩ := insertionSortRange lo hi lo a
    Fast.castSize (sortBlocks n w (lo + w) b) hb
  else ⟨a, rfl⟩
termination_by n.toNat - lo.toNat
decreasing_by u64

/-- Bottom-up merge sort starting from insertion-sorted runs of 16. -/
def sort16 (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : UInt64Array :=
  let n : UInt64 := xs.size.toUInt64
  have hn : n.toNat = xs.size := by simp [n]; omega
  if h : 16 < n then
    have h : 16 < n.toNat := h
    let ⟨a, ha⟩ := sortBlocks n 16 0 xs
    (widthLoop n 16 a (zeros xs.size)).1
  else
    (insertionSortRange 0 n 0 xs).1

end MergeSort.BottomUp
