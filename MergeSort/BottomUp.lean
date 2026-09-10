import MergeSort.Fast
import MergeSort.BottomUpMerge
/-!
# Part 2b: bottom-up merge sort with two buffers

No recursion: pass `w` merges adjacent runs of length `w` from `src` into `dst`, the two buffers
swap roles, and `w` doubles until it covers the array. The input array itself is one of the two
buffers, so the sort works in place (plus one scratch buffer) and nothing is copied in or out.
This is the fastest plain merge sort we found in Lean; it matches the same algorithm in Rust.
-/
namespace MergeSort.BottomUp
open UInt64Array

-- ANCHOR: passLoop
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
-- ANCHOR_END: passLoop

-- ANCHOR: widthLoop
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
-- ANCHOR_END: widthLoop

-- ANCHOR: sort
/-- Bottom-up merge sort of an unboxed `UInt64` array, in place (plus one scratch buffer). -/
def sort (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : UInt64Array :=
  let n : UInt64 := xs.size.toUInt64
  have hn : n.toNat = xs.size := by simp [n]; omega
  (widthLoop n 1 xs (zeros xs.size)).1
-- ANCHOR_END: sort

end MergeSort.BottomUp
