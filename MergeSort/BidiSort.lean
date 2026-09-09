import MergeSort.Bidi
import MergeSort.BottomUpCorrect
/-! Bottom-up merge sort whose passes use the bidirectional merge on equal-length runs. -/
namespace MergeSort.BottomUp
open UInt64Array MergeSort.Fast

/-- Merge `src[lo, mid)` and `src[mid, hi)` into `dst[lo, hi)`: bidirectionally when the runs have
    equal positive length, with the plain branchless loop otherwise (the last pair of a pass). -/
def mergeKernel (lo mid hi : UInt64) (src dst : UInt64Array)
    (hsz : dst.size < 2 ^ 64 := by u64) (hs : hi.toNat ≤ src.size := by u64) (hd : hi.toNat ≤ dst.size := by u64)
    (hlo : lo.toNat ≤ mid.toNat := by u64) (hmid : mid.toNat ≤ hi.toNat := by u64) :
    { b : UInt64Array // b.size = dst.size } :=
  if h : mid - lo = hi - mid ∧ lo < mid then
    have h1 : mid.toNat - lo.toNat = hi.toNat - mid.toNat := by
      have := h.1; have := congrArg UInt64.toNat this; u64
    have h2 : lo.toNat < mid.toNat := h.2
    mergeBidi mid hi lo mid lo mid hi hi (mid - lo) src dst
  else
    mergeLoop mid hi lo mid lo src dst

theorem mergeKernel_spec (lo mid hi : UInt64) (src dst : UInt64Array) hsz hs hd hlo hmid
    (hL : Sorted le64 (src.slice lo.toNat (mid.toNat - lo.toNat)))
    (hR : Sorted le64 (src.slice mid.toNat (hi.toNat - mid.toNat))) :
    (mergeKernel lo mid hi src dst hsz hs hd hlo hmid).1.slice lo.toNat (hi.toNat - lo.toNat) =
      merge le64 (src.slice lo.toNat (mid.toNat - lo.toNat)) (src.slice mid.toNat (hi.toNat - mid.toNat)) ∧
    ∀ x, (x < lo.toNat ∨ hi.toNat ≤ x) → (mergeKernel lo mid hi src dst hsz hs hd hlo hmid).1.at' x = dst.at' x := by
  rw [mergeKernel]
  split
  · rename_i h
    have h1 : mid.toNat - lo.toNat = hi.toNat - mid.toNat := by
      have := h.1; have := congrArg UInt64.toNat this; u64
    have h2 : lo.toNat < mid.toNat := h.2
    have ew : (mid - lo).toNat = mid.toNat - lo.toNat := by u64g
    dsimp only
    obtain ⟨F, B, Fr⟩ := mergeBidi_spec mid hi src lo.toNat (mid - lo).toNat lo mid lo mid hi hi (mid - lo) dst hsz hs hd hmid
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) rfl (Nat.le_refl _) (by omega)
    rw [Nat.sub_self, slice_zero, List.nil_append] at F
    rw [Nat.sub_self, slice_zero, List.append_nil] at B
    refine ⟨?_, fun x hx => Fr x (by omega)⟩
    rw [show hi.toNat - lo.toNat = (mid.toNat - lo.toNat) + (hi.toNat - mid.toNat) by omega, slice_add,
      show lo.toNat + (mid.toNat - lo.toNat) = mid.toNat by omega, F, B, ew]
    have hlen : (merge le64 (src.slice lo.toNat (mid.toNat - lo.toNat)) (src.slice mid.toNat (hi.toNat - mid.toNat))).length =
        (mid.toNat - lo.toNat) + (hi.toNat - mid.toNat) := by
      rw [(merge_perm le64 _ _).length_eq]; simp
    have hback : ((mergeBack (src.slice lo.toNat (mid.toNat - lo.toNat)).reverse
        (src.slice mid.toNat (hi.toNat - mid.toNat)).reverse).take (mid.toNat - lo.toNat)).reverse =
        (merge le64 (src.slice lo.toNat (mid.toNat - lo.toNat)) (src.slice mid.toNat (hi.toNat - mid.toNat))).drop
          (mid.toNat - lo.toNat) := by
      rw [drop_merge_eq _ _ hL hR, hlen, show mid.toNat - lo.toNat + (hi.toNat - mid.toNat) - (mid.toNat - lo.toNat) =
        mid.toNat - lo.toNat by omega]
    rw [hback, List.take_append_drop]
  · rename_i h
    obtain ⟨E, Fr⟩ := mergeLoop_spec mid hi src lo.toNat (hi.toNat - lo.toNat) lo mid lo dst hsz hs hd hmid hlo hmid
      (by omega) rfl (Nat.le_refl _)
    rw [Nat.sub_self, slice_zero, List.nil_append] at E
    exact ⟨E, fun x hx => Fr x (by omega)⟩

/-- One pass: merge the runs `[lo, lo+w)` and `[lo+w, lo+2w)` (clipped to `n`) from `src` into
    `dst`, then continue at `lo + 2w`. -/
def passLoop2 (n w lo : UInt64) (src dst : UInt64Array)
    (hn : n.toNat < 2 ^ 62 := by u64) (hs : n.toNat ≤ src.size := by u64)
    (hd : n.toNat ≤ dst.size := by u64) (hdsz : dst.size < 2 ^ 64 := by u64)
    (hw : 1 ≤ w.toNat ∧ w.toNat < 2 ^ 62 := by u64) : { b : UInt64Array // b.size = dst.size } :=
  if h : lo < n then
    have h : lo.toNat < n.toNat := h
    let mid := if lo + w ≤ n then lo + w else n
    let hi := if lo + 2 * w ≤ n then lo + 2 * w else n
    have hmid : mid.toNat = min (lo.toNat + w.toNat) n.toNat := by
      show (if lo + w ≤ n then lo + w else n).toNat = _; split <;> u64
    have hhi : hi.toNat = min (lo.toNat + 2 * w.toNat) n.toNat := by
      show (if lo + 2 * w ≤ n then lo + 2 * w else n).toNat = _; split <;> u64
    let ⟨b, hb⟩ := mergeKernel lo mid hi src dst
    Fast.castSize (passLoop2 n w (lo + 2 * w) src b) hb
  else ⟨dst, rfl⟩
termination_by n.toNat - lo.toNat
decreasing_by u64

/-- Double the run length until it covers the array; the result is the buffer that was last
    written (or `src` itself if nothing had to be done). -/
def widthLoop2 (n w : UInt64) (src dst : UInt64Array)
    (hn : n.toNat < 2 ^ 62 := by u64) (hs : n.toNat = src.size := by u64)
    (hd : n.toNat = dst.size := by u64) (hw : 1 ≤ w.toNat := by u64) :
    { b : UInt64Array // b.size = src.size } :=
  if h : w < n then
    have h : w.toNat < n.toNat := h
    let ⟨b, hb⟩ := passLoop2 n w 0 src dst
    Fast.castSize (widthLoop2 n (2 * w) b src (hs := by rw [hb]; exact hd)) (by omega)
  else ⟨src, rfl⟩
termination_by n.toNat - w.toNat
decreasing_by u64

/-- Bottom-up merge sort with bidirectional merges, in place (plus one scratch buffer). -/
def sort2 (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : UInt64Array :=
  let n : UInt64 := xs.size.toUInt64
  have hn : n.toNat = xs.size := by simp [n]; omega
  (widthLoop2 n 1 xs (zeros xs.size)).1


/-- What one pass does: `dst[lo, n)` becomes the merged runs of `src[lo, n)`; nothing else changes. -/
theorem passLoop2_spec (n w : UInt64) (src : UInt64Array) (hw0 : 0 < w.toNat) :
    ∀ (m : Nat) (lo : UInt64) (dst : UInt64Array) hn hs hd hdsz hw, m = n.toNat - lo.toNat →
    ChunkSorted w.toNat hw0 (src.slice lo.toNat (n.toNat - lo.toNat)) →
    (passLoop2 n w lo src dst hn hs hd hdsz hw).1.slice lo.toNat (n.toNat - lo.toNat) =
      mergeRuns w.toNat hw0 (src.slice lo.toNat (n.toNat - lo.toNat)) ∧
    ∀ x, (x < lo.toNat ∨ n.toNat ≤ x) →
      (passLoop2 n w lo src dst hn hs hd hdsz hw).1.at' x = dst.at' x := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro lo dst hn hs hd hdsz hw hm hcs
  rw [passLoop2]
  dsimp only
  split
  · rename_i h
    have h : lo.toNat < n.toNat := h
    let MID : UInt64 := if lo + w ≤ n then lo + w else n
    let HI : UInt64 := if lo + 2 * w ≤ n then lo + 2 * w else n
    have e1w : (lo + w).toNat = lo.toNat + w.toNat := by u64g
    have e2w : (lo + 2 * w).toNat = lo.toNat + 2 * w.toNat := by u64g
    have hMID : (lo.toNat + w.toNat ≤ n.toNat ∧ MID.toNat = lo.toNat + w.toNat) ∨
        (n.toNat < lo.toNat + w.toNat ∧ MID.toNat = n.toNat) := by
      by_cases hc : lo + w ≤ n
      · have hc' := UInt64.le_iff_toNat_le.mp hc
        left; refine ⟨by omega, ?_⟩
        show (if lo + w ≤ n then lo + w else n).toNat = _; rw [if_pos hc, e1w]
      · have hc' : ¬ (lo + w).toNat ≤ n.toNat := fun h => hc (UInt64.le_iff_toNat_le.mpr h)
        right; refine ⟨by omega, ?_⟩
        show (if lo + w ≤ n then lo + w else n).toNat = _; rw [if_neg hc]
    have hHI : (lo.toNat + 2 * w.toNat ≤ n.toNat ∧ HI.toNat = lo.toNat + 2 * w.toNat) ∨
        (n.toNat < lo.toNat + 2 * w.toNat ∧ HI.toNat = n.toNat) := by
      by_cases hc : lo + 2 * w ≤ n
      · have hc' := UInt64.le_iff_toNat_le.mp hc
        left; refine ⟨by omega, ?_⟩
        show (if lo + 2 * w ≤ n then lo + 2 * w else n).toNat = _; rw [if_pos hc, e2w]
      · have hc' : ¬ (lo + 2 * w).toNat ≤ n.toNat := fun h => hc (UInt64.le_iff_toNat_le.mpr h)
        right; refine ⟨by omega, ?_⟩
        show (if lo + 2 * w ≤ n then lo + 2 * w else n).toNat = _; rw [if_neg hc]
    -- the two runs are sorted, and the remainder is still `w`-run-sorted
    have hLs : Sorted le64 (src.slice lo.toNat (MID.toNat - lo.toNat)) := by
      by_cases hcase : n.toNat - lo.toNat ≤ w.toNat
      · rw [show MID.toNat - lo.toNat = n.toNat - lo.toNat by omega]
        exact (chunkSorted_of_length_le hw0 (by simp; omega)).mp hcs
      · have := ((chunkSorted_of_lt hw0 (by simp; omega)).mp hcs).1
        rwa [show n.toNat - lo.toNat = w.toNat + (n.toNat - lo.toNat - w.toNat) by omega, take_slice,
          show w.toNat = MID.toNat - lo.toNat by omega] at this
    have hcs' : (¬ n.toNat - lo.toNat ≤ w.toNat ∧
          ChunkSorted w.toNat hw0 (src.slice (lo.toNat + w.toNat) (n.toNat - lo.toNat - w.toNat))) ∨
        n.toNat - lo.toNat ≤ w.toNat := by
      by_cases hcase : n.toNat - lo.toNat ≤ w.toNat
      · exact Or.inr hcase
      · left; refine ⟨hcase, ?_⟩
        have := ((chunkSorted_of_lt hw0 (by simp; omega)).mp hcs).2
        rwa [show n.toNat - lo.toNat = w.toNat + (n.toNat - lo.toNat - w.toNat) by omega, drop_slice] at this
    have hRs : Sorted le64 (src.slice MID.toNat (HI.toNat - MID.toNat)) := by
      rcases hcs' with ⟨hgt, hcs'⟩ | hcase
      · by_cases h2 : n.toNat - lo.toNat - w.toNat ≤ w.toNat
        · have := (chunkSorted_of_length_le hw0 (by simp; omega)).mp hcs'
          rwa [show MID.toNat = lo.toNat + w.toNat by omega,
            show HI.toNat - (lo.toNat + w.toNat) = n.toNat - lo.toNat - w.toNat by omega]
        · have := ((chunkSorted_of_lt hw0 (by simp; omega)).mp hcs').1
          rw [show n.toNat - lo.toNat - w.toNat = w.toNat + (n.toNat - lo.toNat - w.toNat - w.toNat) by omega,
            take_slice] at this
          rwa [show MID.toNat = lo.toNat + w.toNat by omega, show HI.toNat - (lo.toNat + w.toNat) = w.toNat by omega]
      · rw [show HI.toNat - MID.toNat = 0 by omega, slice_zero]; simp [Sorted]
    have hcs2 : ChunkSorted w.toNat hw0 (src.slice (lo + 2 * w).toNat (n.toNat - (lo + 2 * w).toNat)) := by
      rcases hcs' with ⟨hgt, hcs'⟩ | hcase
      · by_cases h2 : n.toNat - lo.toNat - w.toNat ≤ w.toNat
        · rw [show n.toNat - (lo + 2 * w).toNat = 0 by omega, slice_zero, chunkSorted_of_length_le hw0 (by simp)]
          simp [Sorted]
        · have := ((chunkSorted_of_lt hw0 (by simp; omega)).mp hcs').2
          rwa [show n.toNat - lo.toNat - w.toNat = w.toNat + (n.toNat - lo.toNat - w.toNat - w.toNat) by omega,
            drop_slice, show lo.toNat + w.toNat + w.toNat = (lo + 2 * w).toNat by omega,
            show n.toNat - lo.toNat - w.toNat - w.toNat = n.toNat - (lo + 2 * w).toNat by omega] at this
      · rw [show n.toNat - (lo + 2 * w).toNat = 0 by omega, slice_zero, chunkSorted_of_length_le hw0 (by simp)]
        simp [Sorted]
    let Bs := mergeKernel lo MID HI src dst (by omega) (by omega) (by omega) (by omega) (by omega)
    obtain ⟨HB1, HB2⟩ := mergeKernel_spec lo MID HI src dst (by omega) (by omega) (by omega) (by omega) (by omega) hLs hRs
    obtain ⟨IH1, IH2⟩ := ih (n.toNat - (lo + 2 * w).toNat) (by omega) (lo + 2 * w) Bs.1 hn hs (by rw [Bs.2]; exact hd)
      (by rw [Bs.2]; exact hdsz) hw rfl hcs2
    simp only [castSize_val]
    refine ⟨?_, fun x hx => ?_⟩
    · have eL : ∀ R : UInt64Array, R.slice lo.toNat (n.toNat - lo.toNat) =
          R.slice lo.toNat (HI.toNat - lo.toNat) ++ R.slice (lo.toNat + (HI.toNat - lo.toNat)) (n.toNat - HI.toNat) := by
        intro R; rw [← slice_add]; congr 1; omega
      rw [eL]
      have eR1 : (passLoop2 n w (lo + 2 * w) src Bs.1 hn hs (by rw [Bs.2]; exact hd) (by rw [Bs.2]; exact hdsz) hw).1.slice
          lo.toNat (HI.toNat - lo.toNat) = Bs.1.slice lo.toNat (HI.toNat - lo.toNat) := by
        apply slice_congr; intro t ht; exact IH2 _ (Or.inl (by omega))
      rw [eR1, HB1]
      by_cases hcase : n.toNat - lo.toNat ≤ w.toNat
      · have hM : MID.toNat = n.toNat := by omega
        have hH : HI.toNat = n.toNat := by omega
        rw [mergeRuns_of_length_le hw0 _ (by simp; omega), hM, hH, Nat.sub_self, slice_zero, slice_zero,
          merge_nil_right, List.append_nil]
      · rw [mergeRuns_of_lt hw0 _ (by simp; omega)]
        have hM : MID.toNat = lo.toNat + w.toNat := by omega
        have eA : (src.slice lo.toNat (n.toNat - lo.toNat)).take w.toNat = src.slice lo.toNat (MID.toNat - lo.toNat) := by
          rw [show n.toNat - lo.toNat = w.toNat + (n.toNat - lo.toNat - w.toNat) by omega, take_slice]; congr 1; omega
        have eB : ((src.slice lo.toNat (n.toNat - lo.toNat)).drop w.toNat).take w.toNat =
            src.slice MID.toNat (HI.toNat - MID.toNat) := by
          rw [show n.toNat - lo.toNat = w.toNat + (n.toNat - lo.toNat - w.toNat) by omega, drop_slice]
          by_cases h2 : w.toNat ≤ n.toNat - lo.toNat - w.toNat
          · rw [show n.toNat - lo.toNat - w.toNat = w.toNat + (n.toNat - lo.toNat - w.toNat - w.toNat) by omega,
              take_slice]
            congr 1 <;> omega
          · rw [List.take_of_length_le (by simp; omega)]
            congr 1 <;> omega
        have eC : (src.slice lo.toNat (n.toNat - lo.toNat)).drop (2 * w.toNat) =
            src.slice (lo + 2 * w).toNat (n.toNat - (lo + 2 * w).toNat) := by
          by_cases h2 : 2 * w.toNat ≤ n.toNat - lo.toNat
          · rw [show n.toNat - lo.toNat = 2 * w.toNat + (n.toNat - lo.toNat - 2 * w.toNat) by omega, drop_slice]
            congr 1 <;> omega
          · rw [List.drop_eq_nil_of_le (by simp; omega), show n.toNat - (lo + 2 * w).toNat = 0 by omega, slice_zero]
        rw [eA, eB, eC, ← IH1]
        by_cases h2 : 2 * w.toNat ≤ n.toNat - lo.toNat
        · rw [show lo.toNat + (HI.toNat - lo.toNat) = (lo + 2 * w).toNat by omega,
            show n.toNat - HI.toNat = n.toNat - (lo + 2 * w).toNat by omega]
        · rw [show n.toNat - HI.toNat = 0 by omega, show n.toNat - (lo + 2 * w).toNat = 0 by omega, slice_zero,
            slice_zero]
    · rw [IH2 x (by omega), HB2 x (by omega)]
  · rename_i h
    have h : ¬ lo.toNat < n.toNat := h
    refine ⟨?_, fun x _ => rfl⟩
    rw [show n.toNat - lo.toNat = 0 by omega, slice_zero, slice_zero, mergeRuns_of_length_le hw0 _ (by simp)]

/-- Doubling the run length until it covers the array yields a sorted permutation. -/
theorem widthLoop2_spec (n : UInt64) (hn2 : n.toNat < 2 ^ 62) :
    ∀ (m : Nat) (w : UInt64) (src dst : UInt64Array) hn hs hd hw, m = n.toNat - w.toNat →
    ChunkSorted w.toNat (by omega) (src.slice 0 n.toNat) →
    Sorted le64 ((widthLoop2 n w src dst hn hs hd hw).1.slice 0 n.toNat) ∧
    ((widthLoop2 n w src dst hn hs hd hw).1.slice 0 n.toNat).Perm (src.slice 0 n.toNat) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro w src dst hn hs hd hw hm hcs
  rw [widthLoop2]
  dsimp only
  split
  · rename_i h
    have h : w.toNat < n.toNat := h
    have e2 : (2 * w).toNat = 2 * w.toNat := by u64g
    let Bs := passLoop2 n w 0 src dst hn (by omega) (by omega) (by omega) ⟨by omega, by omega⟩
    obtain ⟨HP1, HP2⟩ := passLoop2_spec n w src (by omega) (n.toNat - (0 : UInt64).toNat) 0 dst hn (by omega) (by omega)
      (by omega) ⟨by omega, by omega⟩ rfl (by simpa using hcs)
    simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.sub_zero] at HP1
    obtain ⟨IH1, IH2⟩ := ih (n.toNat - (2 * w).toNat) (by omega) (2 * w) Bs.1 src hn (by rw [Bs.2]; exact hd) hs
      (by omega) rfl (by rw [HP1]; exact chunkSorted_congr e2.symm _ _ (chunkSorted_mergeRuns (by omega) _ hcs))
    simp only [castSize_val]
    exact ⟨IH1, IH2.trans (by rw [HP1]; exact mergeRuns_perm _ _)⟩
  · rename_i h
    have h : ¬ w.toNat < n.toNat := h
    exact ⟨sorted_of_chunkSorted _ (by simp; omega) hcs, List.Perm.refl _⟩

/-- The bidirectional bottom-up sort produces a sorted list. -/
theorem sort2_sorted (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : Sorted le64 (sort2 xs hsz).data.toList := by
  rw [sort2]
  have hn : (xs.size.toUInt64).toNat = xs.size := by simp; omega
  obtain ⟨S, _⟩ := widthLoop2_spec xs.size.toUInt64 (by omega) _ 1 xs (zeros xs.size) (by omega) hn (by simp [hn])
    (by simp) rfl (chunkSorted_congr (by simp) _ _ (chunkSorted_one _))
  have hs' : (widthLoop2 xs.size.toUInt64 1 xs (zeros xs.size) (by omega) hn (by simp [hn]) (by simp)).1.size =
      (xs.size.toUInt64).toNat := by rw [(widthLoop2 _ _ _ _ _ _ _ _).2, hn]
  rw [← slice_eq_toList, hs']
  exact S

/-- The bidirectional bottom-up sort produces a permutation of its input. -/
theorem sort2_perm (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : (sort2 xs hsz).data.toList.Perm xs.data.toList := by
  rw [sort2]
  have hn : (xs.size.toUInt64).toNat = xs.size := by simp; omega
  obtain ⟨_, P⟩ := widthLoop2_spec xs.size.toUInt64 (by omega) _ 1 xs (zeros xs.size) (by omega) hn (by simp [hn])
    (by simp) rfl (chunkSorted_congr (by simp) _ _ (chunkSorted_one _))
  have hs' : (widthLoop2 xs.size.toUInt64 1 xs (zeros xs.size) (by omega) hn (by simp [hn]) (by simp)).1.size =
      (xs.size.toUInt64).toNat := by rw [(widthLoop2 _ _ _ _ _ _ _ _).2, hn]
  have exs : xs.slice 0 (xs.size.toUInt64).toNat = xs.data.toList := by rw [hn, slice_eq_toList]
  rw [← slice_eq_toList, hs', ← exs]
  exact P

end MergeSort.BottomUp
