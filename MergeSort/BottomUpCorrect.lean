import MergeSort.BottomUp
import MergeSort.Runs
/-! Correctness of the bottom-up sort: sorted output, permutation of the input. -/
namespace MergeSort.BottomUp
open UInt64Array MergeSort.Fast

-- ANCHOR: mergeLoop_spec
/-- What the merge loop does to `dst[lo, hi)`; `src` is only read. -/
theorem mergeLoop_spec (mid hi : UInt64) (src : UInt64Array) (lo : Nat) :
    ∀ (n : Nat) (i j k : UInt64) (dst : UInt64Array) hsz hs hd hmid hi' hj hinv,
    n = hi.toNat - k.toNat → lo ≤ k.toNat →
    (mergeLoop mid hi i j k src dst hsz hs hd hmid hi' hj hinv).1.slice lo (hi.toNat - lo) =
      dst.slice lo (k.toNat - lo) ++
        merge (src.slice i.toNat (mid.toNat - i.toNat)) (src.slice j.toNat (hi.toNat - j.toNat)) ∧
    ∀ x, (x < k.toNat ∨ hi.toNat ≤ x) →
      (mergeLoop mid hi i j k src dst hsz hs hd hmid hi' hj hinv).1.at' x = dst.at' x
-- ANCHOR_END: mergeLoop_spec
    := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro i j k dst hsz hs hd hmid hi' hj hinv hn hlo
  rw [mergeLoop]
  split
  · rename_i hk
    have hk : k.toNat < hi.toNat := hk
    have ek : (k + 1).toNat = k.toNat + 1 := by u64g
    have hend : ∀ v hp, (dst.set k v hp).slice lo (k.toNat + 1 - lo) = dst.slice lo (k.toNat - lo) ++ [v] := by
      intro v hp
      rw [show k.toNat + 1 - lo = (k.toNat - lo) + 1 by omega]
      exact slice_set_end _ _ _ _ _ _ (by omega)
    have hfr : ∀ v hp x, (x < k.toNat ∨ hi.toNat ≤ x) → (dst.set k v hp).at' x = dst.at' x := by
      intro v hp x hx
      apply at'_set_ne
      omega
    split
    · rename_i hi''
      have hi'' : i.toNat < mid.toNat := hi''
      have ei : (i + 1).toNat = i.toNat + 1 := by u64g
      split
      · rename_i hj'
        have hj' : j.toNat < hi.toNat := hj'
        have ej : (j + 1).toNat = j.toNat + 1 := by u64g
        dsimp only
        -- name the branchless step's ingredients (definitionally the ones in the goal)
        let TL : Bool := decide (src[i]'(by u64g) ≤ src[j]'(by u64g))
        let DI : UInt64 := if TL then 1 else 0
        let V : UInt64 := if TL then src[i]'(by u64g) else src[j]'(by u64g)
        have hDI : DI.toNat ≤ 1 := by show (if TL then (1 : UInt64) else 0).toNat ≤ 1; split <;> decide
        obtain ⟨ih1, ih2⟩ := ih (hi.toNat - (k + 1).toNat) (by omega) (i + DI) (j + (1 - DI)) (k + 1)
          (dst.set k V (by u64g)) (by u64g) hs (by u64g) hmid (by u64g) (by u64g) (by u64g) rfl (by omega)
        have eDI : (i + DI).toNat = i.toNat + DI.toNat := by simp only [UInt64.toNat_add, Nat.reducePow]; omega
        have eDJ : (j + (1 - DI)).toNat = j.toNat + (1 - DI.toNat) := by
          simp only [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
        refine ⟨?_, fun x hx => ?_⟩
        · rw [castSize_val, ih1, ek, hend]
          by_cases hle : src[i]'(by u64g) ≤ src[j]'(by u64g)
          · have hTL : TL = true := by simp [TL, hle]
            have e1 : (i + DI).toNat = i.toNat + 1 := by rw [eDI]; simp only [DI, hTL, ite_true]; u64g
            have e2 : (j + (1 - DI)).toNat = j.toNat := by rw [eDJ]; simp only [DI, hTL, ite_true]; u64g
            have hV : V = src[i]'(by u64g) := by simp [V, hTL]
            rw [e1, e2, hV]
            rw [show mid.toNat - i.toNat = (mid.toNat - (i.toNat + 1)) + 1 by omega, slice_cons,
              show hi.toNat - j.toNat = (hi.toNat - (j.toNat + 1)) + 1 by omega, slice_cons, merge_cons_cons]
            simp only [getElem_eq_get, get_eq_at'] at hle
            simp [hle, getElem_eq_get, get_eq_at']
          · have hTL : TL = false := by simp [TL, hle]
            have e1 : (i + DI).toNat = i.toNat := by rw [eDI]; simp only [DI, hTL, Bool.false_eq_true, ite_false]; u64g
            have e2 : (j + (1 - DI)).toNat = j.toNat + 1 := by
              rw [eDJ]; simp only [DI, hTL, Bool.false_eq_true, ite_false]; u64g
            have hV : V = src[j]'(by u64g) := by simp [V, hTL]
            rw [e1, e2, hV]
            rw [show mid.toNat - i.toNat = (mid.toNat - (i.toNat + 1)) + 1 by omega, slice_cons,
              show hi.toNat - j.toNat = (hi.toNat - (j.toNat + 1)) + 1 by omega, slice_cons, merge_cons_cons]
            simp only [getElem_eq_get, get_eq_at'] at hle
            simp [hle, getElem_eq_get, get_eq_at']
        · rw [castSize_val, ih2 x (by omega)]
          exact hfr _ _ x hx
      · rename_i hj'
        have hj' : ¬ j.toNat < hi.toNat := hj'
        dsimp only
        obtain ⟨ih1, ih2⟩ := ih (hi.toNat - (k + 1).toNat) (by omega) (i + 1) j (k + 1)
          (dst.set k (src[i]'(by u64g)) (by u64g)) (by u64g) hs (by u64g) hmid (by u64g) hj (by u64g) rfl (by omega)
        refine ⟨?_, fun x hx => ?_⟩
        · rw [castSize_val, ih1, ek, hend, ei]
          rw [show hi.toNat - j.toNat = 0 by omega, slice_zero, merge_nil_right, merge_nil_right,
            show mid.toNat - i.toNat = (mid.toNat - (i.toNat + 1)) + 1 by omega, slice_cons]
          simp [getElem_eq_get, get_eq_at']
        · rw [castSize_val, ih2 x (by omega)]
          exact hfr _ _ x hx
    · rename_i hi''
      have hi'' : ¬ i.toNat < mid.toNat := hi''
      have ej : (j + 1).toNat = j.toNat + 1 := by u64g
      dsimp only
      obtain ⟨ih1, ih2⟩ := ih (hi.toNat - (k + 1).toNat) (by omega) i (j + 1) (k + 1)
        (dst.set k (src[j]'(by u64g)) (by u64g)) (by u64g) hs (by u64g) hmid hi' (by u64g) (by u64g) rfl (by omega)
      refine ⟨?_, fun x hx => ?_⟩
      · rw [castSize_val, ih1, ek, hend, ej]
        rw [show mid.toNat - i.toNat = 0 by omega, slice_zero, merge_nil_left, merge_nil_left,
          show hi.toNat - j.toNat = (hi.toNat - (j.toNat + 1)) + 1 by omega, slice_cons]
        simp [getElem_eq_get, get_eq_at']
      · rw [castSize_val, ih2 x (by omega)]
        exact hfr _ _ x hx
  · rename_i hk
    have hk : ¬ k.toNat < hi.toNat := hk
    refine ⟨?_, fun x _ => rfl⟩
    have hi0 : mid.toNat - i.toNat = 0 := by omega
    have hj0 : hi.toNat - j.toNat = 0 := by omega
    rw [hi0, hj0, slice_zero, slice_zero, merge_nil_left, List.append_nil]
    congr 1
    omega


-- ANCHOR: passLoop_spec
/-- What one pass does: `dst[lo, n)` becomes the merged runs of `src[lo, n)`; nothing else changes. -/
theorem passLoop_spec (n w : UInt64) (src : UInt64Array) (hw0 : 0 < w.toNat) :
    ∀ (m : Nat) (lo : UInt64) (dst : UInt64Array) hn hs hd hdsz hw, m = n.toNat - lo.toNat →
    (passLoop n w lo src dst hn hs hd hdsz hw).1.slice lo.toNat (n.toNat - lo.toNat) =
      mergeRuns w.toNat hw0 (src.slice lo.toNat (n.toNat - lo.toNat)) ∧
    ∀ x, (x < lo.toNat ∨ n.toNat ≤ x) →
      (passLoop n w lo src dst hn hs hd hdsz hw).1.at' x = dst.at' x
-- ANCHOR_END: passLoop_spec
    := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro lo dst hn hs hd hdsz hw hm
  rw [passLoop]
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
    let Bs := mergeLoop MID HI lo MID lo src dst (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
    obtain ⟨HB1, HB2⟩ := mergeLoop_spec MID HI src lo.toNat (HI.toNat - lo.toNat) lo MID lo dst (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) rfl (Nat.le_refl _)
    obtain ⟨IH1, IH2⟩ := ih (n.toNat - (lo + 2 * w).toNat) (by omega) (lo + 2 * w) Bs.1 hn hs (by rw [Bs.2]; exact hd)
      (by rw [Bs.2]; exact hdsz) hw rfl
    simp only [castSize_val]
    refine ⟨?_, fun x hx => ?_⟩
    · have eL : ∀ R : UInt64Array, R.slice lo.toNat (n.toNat - lo.toNat) =
          R.slice lo.toNat (HI.toNat - lo.toNat) ++ R.slice (lo.toNat + (HI.toNat - lo.toNat)) (n.toNat - HI.toNat) := by
        intro R; rw [← slice_add]; congr 1; omega
      rw [eL]
      have eR1 : (passLoop n w (lo + 2 * w) src Bs.1 hn hs (by rw [Bs.2]; exact hd) (by rw [Bs.2]; exact hdsz) hw).1.slice
          lo.toNat (HI.toNat - lo.toNat) = Bs.1.slice lo.toNat (HI.toNat - lo.toNat) := by
        apply slice_congr; intro t ht; exact IH2 _ (Or.inl (by omega))
      rw [eR1, HB1, Nat.sub_self, slice_zero, List.nil_append]
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

-- ANCHOR: widthLoop_spec
/-- Doubling the run length until it covers the array yields a sorted permutation. -/
theorem widthLoop_spec (n : UInt64) (hn2 : n.toNat < 2 ^ 62) :
    ∀ (m : Nat) (w : UInt64) (src dst : UInt64Array) hn hs hd hw, m = n.toNat - w.toNat →
    ChunkSorted w.toNat (by omega) (src.slice 0 n.toNat) →
    Sorted ((widthLoop n w src dst hn hs hd hw).1.slice 0 n.toNat) ∧
    ((widthLoop n w src dst hn hs hd hw).1.slice 0 n.toNat).Perm (src.slice 0 n.toNat)
-- ANCHOR_END: widthLoop_spec
    := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro w src dst hn hs hd hw hm hcs
  rw [widthLoop]
  dsimp only
  split
  · rename_i h
    have h : w.toNat < n.toNat := h
    have e2 : (2 * w).toNat = 2 * w.toNat := by u64g
    let Bs := passLoop n w 0 src dst hn (by omega) (by omega) (by omega) ⟨by omega, by omega⟩
    obtain ⟨HP1, HP2⟩ := passLoop_spec n w src (by omega) (n.toNat - (0 : UInt64).toNat) 0 dst hn (by omega) (by omega)
      (by omega) ⟨by omega, by omega⟩ rfl
    simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.sub_zero] at HP1
    obtain ⟨IH1, IH2⟩ := ih (n.toNat - (2 * w).toNat) (by omega) (2 * w) Bs.1 src hn (by rw [Bs.2]; exact hd) hs
      (by omega) rfl (by rw [HP1]; exact chunkSorted_congr e2.symm _ _ (chunkSorted_mergeRuns (by omega) _ hcs))
    simp only [castSize_val]
    exact ⟨IH1, IH2.trans (by rw [HP1]; exact mergeRuns_perm _ _)⟩
  · rename_i h
    have h : ¬ w.toNat < n.toNat := h
    exact ⟨sorted_of_chunkSorted _ (by simp; omega) hcs, List.Perm.refl _⟩

-- ANCHOR: sort_sorted
/-- The bottom-up sort produces a sorted list. -/
theorem sort_sorted (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : Sorted (sort xs hsz).data.toList
-- ANCHOR_END: sort_sorted
    := by
  rw [sort]
  have hn : (xs.size.toUInt64).toNat = xs.size := by simp; omega
  obtain ⟨S, _⟩ := widthLoop_spec xs.size.toUInt64 (by omega) _ 1 xs (zeros xs.size) (by omega) hn (by simp [hn])
    (by simp) rfl (chunkSorted_congr (by simp) _ _ (chunkSorted_one _))
  have hs' : (widthLoop xs.size.toUInt64 1 xs (zeros xs.size) (by omega) hn (by simp [hn]) (by simp)).1.size =
      (xs.size.toUInt64).toNat := by rw [(widthLoop _ _ _ _ _ _ _ _).2, hn]
  rw [← slice_eq_toList, hs']
  exact S

-- ANCHOR: sort_perm
/-- The bottom-up sort produces a permutation of its input. -/
theorem sort_perm (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : (sort xs hsz).data.toList.Perm xs.data.toList
-- ANCHOR_END: sort_perm
    := by
  rw [sort]
  have hn : (xs.size.toUInt64).toNat = xs.size := by simp; omega
  obtain ⟨_, P⟩ := widthLoop_spec xs.size.toUInt64 (by omega) _ 1 xs (zeros xs.size) (by omega) hn (by simp [hn])
    (by simp) rfl (chunkSorted_congr (by simp) _ _ (chunkSorted_one _))
  have hs' : (widthLoop xs.size.toUInt64 1 xs (zeros xs.size) (by omega) hn (by simp [hn]) (by simp)).1.size =
      (xs.size.toUInt64).toNat := by rw [(widthLoop _ _ _ _ _ _ _ _).2, hn]
  have exs : xs.slice 0 (xs.size.toUInt64).toNat = xs.data.toList := by rw [hn, slice_eq_toList]
  rw [← slice_eq_toList, hs', ← exs]
  exact P

end MergeSort.BottomUp
