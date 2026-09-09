import MergeSort.FastMerge
/-!
# Part 2: the same merge sort on a flat `UInt64` buffer

Top-down merge sort that "ping-pongs" between the two halves of a single buffer of length `2n`:
the input lives in both halves; `sortRange s d lo hi` sorts the range `[lo, hi)` reading from
half `s` and leaving the result in half `d`. Nothing is allocated during sorting.

Indices are `UInt64` (unboxed machine words). Every bound and every termination measure is proved,
so the compiled code contains no bounds checks and no `partial`.
-/
namespace MergeSort.Fast
open UInt64Array

/-- Sort `[lo, hi)`: input in half `s` (and also in half `d`), output in half `d`. -/
def sortRange (s d lo hi : UInt64) (a : UInt64Array)
    (hsz : a.size < 2 ^ 64 := by u64)
    (hs : s.toNat + hi.toNat ≤ a.size := by u64) (hd : d.toNat + hi.toNat ≤ a.size := by u64)
    (hlo : lo.toNat ≤ hi.toNat := by u64) : { b : UInt64Array // b.size = a.size } :=
  let mid := lo + (hi - lo) / 2
  have hmid : mid.toNat = lo.toNat + (hi.toNat - lo.toNat) / 2 := by
    show (lo + (hi - lo) / 2).toNat = _; u64
  have hmid' : mid.toNat = (lo + (hi - lo) / 2).toNat := rfl
  -- Every path consumes `a`, so the compiler keeps it owned (no copy-on-write).
  let ⟨a₁, h₁⟩ : { b : UInt64Array // b.size = a.size } :=
    if h : 2 ≤ mid - lo then
      have h : 2 ≤ mid.toNat - lo.toNat := by have h := UInt64.le_iff_toNat_le.mp h; u64
      sortRange d s lo mid a
    else ⟨a, rfl⟩
  let ⟨a₂, h₂⟩ : { b : UInt64Array // b.size = a.size } :=
    if h : 2 ≤ hi - mid then
      have h : 2 ≤ hi.toNat - mid.toNat := by have h := UInt64.le_iff_toNat_le.mp h; u64
      castSize (sortRange d s mid hi a₁) h₁
    else ⟨a₁, h₁⟩
  castSize (mergeLoop s d mid hi lo mid lo a₂) h₂
termination_by hi.toNat - lo.toNat
decreasing_by all_goals u64

/-- Copy `src[0, n)` into both halves of a fresh `2n` buffer. -/
def copyIn (src : UInt64Array) (n k : UInt64) (a : UInt64Array)
    (hn : n.toNat = src.size) (ha : a.size = 2 * src.size := by u64) (hsz : a.size < 2 ^ 64 := by u64)
    (_hk : k.toNat ≤ n.toNat := by u64) : { b : UInt64Array // b.size = a.size } :=
  if h : k < n then
    have h : k.toNat < n.toNat := h
    castSize (copyIn src n (k + 1) ((a.set k (src.get k)).set (n + k) (src.get k)) hn) (by simp)
  else ⟨a, rfl⟩
termination_by n.toNat - k.toNat
decreasing_by u64

/-- Copy `a[n, 2n)` out into `out[0, n)`. -/
def copyOut (a : UInt64Array) (n k : UInt64) (out : UInt64Array)
    (ha : 2 * n.toNat ≤ a.size := by u64) (hsz : a.size < 2 ^ 64 := by u64)
    (hout : out.size = n.toNat := by u64) (_hk : k.toNat ≤ n.toNat := by u64) :
    { b : UInt64Array // b.size = out.size } :=
  if h : k < n then
    have h : k.toNat < n.toNat := h
    castSize (copyOut a n (k + 1) (out.set k (a.get (n + k))) ha hsz) (by simp)
  else ⟨out, rfl⟩
termination_by n.toNat - k.toNat
decreasing_by u64

/-- Sort an unboxed `UInt64` array. (Arrays of 2^63 or more elements are not supported.) -/
def sort (xs : UInt64Array) (hsz : xs.size < 2 ^ 63) : UInt64Array :=
  let n : UInt64 := xs.size.toUInt64
  have hn : n.toNat = xs.size := by simp [n]; omega
  let ⟨a, ha⟩ := copyIn xs n 0 (zeros (2 * xs.size)) hn
  let ⟨a, ha'⟩ := sortRange 0 n 0 n a
  (copyOut a n 0 (zeros xs.size)).1

end MergeSort.Fast
