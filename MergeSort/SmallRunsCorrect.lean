import MergeSort.SmallRuns
import MergeSort.InsertionList
import MergeSort.BottomUpCorrect
/-! Correctness of the insertion-sorted initial runs, and of `sort16`. -/
namespace MergeSort.BottomUp
open UInt64Array MergeSort.Fast

/-- Insert all elements of the second list into the sorted accumulator. -/
def insertAll (acc : List UInt64) : List UInt64 → List UInt64
  | [] => acc
  | x :: l => insertAll (insertSorted x acc) l

theorem insertAll_sorted (acc l : List UInt64) (h : Sorted acc) : Sorted (insertAll acc l) := by
  induction l generalizing acc with
  | nil => simpa [insertAll]
  | cons x l ih => exact ih _ (insertSorted_sorted x acc h)

theorem insertAll_perm (acc l : List UInt64) : (insertAll acc l).Perm (acc ++ l) := by
  induction l generalizing acc with
  | nil => simp [insertAll]
  | cons x l ih =>
    simp only [insertAll]
    exact (ih _).trans (((insertSorted_perm x acc).append_right l).trans List.perm_middle.symm)

theorem insertSorted_append_last (x y : UInt64) (l : List UInt64) (hxy : x < y)
    (hl : ∀ z ∈ l, z ≤ y) : insertSorted x (l ++ [y]) = insertSorted x l ++ [y] := by
  induction l with
  | nil => simp [insertSorted, hxy]
  | cons z l ih =>
    simp only [List.cons_append, insertSorted]
    split
    · rfl
    · rw [ih (fun w hw => hl w (List.mem_cons_of_mem z hw))]; simp

theorem insertSorted_of_last_le (x y : UInt64) (l : List UInt64) (hyx : y ≤ x)
    (hl : ∀ z ∈ l, z ≤ y) : insertSorted x (l ++ [y]) = l ++ [y, x] := by
  induction l with
  | nil => simp [insertSorted, UInt64.not_lt.mpr hyx]
  | cons z l ih =>
    have hzx : ¬ x < z := UInt64.not_lt.mpr (UInt64.le_trans (hl z (List.mem_cons_self ..)) hyx)
    simp only [List.cons_append, insertSorted, hzx, ite_false]
    rw [ih (fun w hw => hl w (List.mem_cons_of_mem z hw))]

theorem sorted_last_le (l : List UInt64) (y : UInt64) (h : Sorted (l ++ [y])) : ∀ z ∈ l, z ≤ y := by
  intro z hz
  have := List.pairwise_append.mp h
  simpa using this.2.2 z hz y (List.mem_singleton.mpr rfl)

/-- `insertLoop` inserts `a[k]` into the sorted run `a[lo, k)`. -/
theorem insertLoop_spec (lo : UInt64) :
    ∀ (m : Nat) (k : UInt64) (a : UInt64Array) hsz hk hlo, m = k.toNat →
    Sorted (a.slice lo.toNat (k.toNat - lo.toNat)) →
    (insertLoop lo k a hsz hk hlo).1.slice lo.toNat (k.toNat + 1 - lo.toNat) =
      insertSorted (a.at' k.toNat) (a.slice lo.toNat (k.toNat - lo.toNat)) ∧
    ∀ x, (x < lo.toNat ∨ k.toNat < x) → (insertLoop lo k a hsz hk hlo).1.at' x = a.at' x := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro k a hsz hk hlo hm hs
  rw [insertLoop]
  split
  · rename_i h
    have h : lo.toNat < k.toNat := h
    have ek : (k - 1).toNat = k.toNat - 1 := by u64g
    dsimp only
    split
    · rename_i hxy
      -- one swap, then recurse on k - 1
      let A := (a.set k (a.get (k - 1) (by u64g)) (by u64g)).set (k - 1) (a.get k (by u64g)) (by u64g)
      have hA : A.size = a.size := by simp [A]
      -- the prefix `[lo, k-1)` is untouched, position `k-1` holds `x`, position `k` holds `y`
      have hpre : A.slice lo.toNat (k.toNat - 1 - lo.toNat) = a.slice lo.toNat (k.toNat - 1 - lo.toNat) := by
        show ((a.set k _ _).set (k - 1) _ _).slice _ _ = _
        rw [slice_set_of_not_mem _ _ _ _ _ _ (by omega), slice_set_of_not_mem _ _ _ _ _ _ (by omega)]
      have hAk : A.at' k.toNat = a.at' (k.toNat - 1) := by
        show ((a.set k _ _).set (k - 1) _ _).at' _ = _
        rw [at'_set_ne _ _ _ _ _ (by omega), at'_set_self, get_eq_at', ek]
      have hsplit : a.slice lo.toNat (k.toNat - lo.toNat) =
          a.slice lo.toNat (k.toNat - 1 - lo.toNat) ++ [a.at' (k.toNat - 1)] := by
        rw [show k.toNat - lo.toNat = (k.toNat - 1 - lo.toNat) + 1 by omega, slice_succ,
          show lo.toNat + (k.toNat - 1 - lo.toNat) = k.toNat - 1 by omega]
      obtain ⟨ih1, ih2⟩ := ih (k - 1).toNat (by omega) (k - 1) A (by rw [hA]; exact hsz) (by rw [hA, ek]; omega)
        (by rw [ek]; omega) rfl
        (by rw [ek, hpre]; rw [hsplit] at hs; exact (List.pairwise_append.mp hs).1)
      refine ⟨?_, fun x hx => ?_⟩
      · have eK : k.toNat + 1 - lo.toNat = (k.toNat - lo.toNat) + 1 := by omega
        rw [castSize_val, eK, slice_succ, show lo.toNat + (k.toNat - lo.toNat) = k.toNat by omega,
          ih2 k.toNat (by omega), hAk]
        have eR : (insertLoop lo (k - 1) A (by rw [hA]; exact hsz) (by rw [hA, ek]; omega) (by rw [ek]; omega)).1.slice
            lo.toNat (k.toNat - lo.toNat) =
            (insertLoop lo (k - 1) A (by rw [hA]; exact hsz) (by rw [hA, ek]; omega) (by rw [ek]; omega)).1.slice
            lo.toNat ((k - 1).toNat + 1 - lo.toNat) := by
          congr 1; omega
        rw [eR, ih1, ek, hpre]
        have hxA : A.at' (k.toNat - 1) = a.at' k.toNat := by
          show ((a.set k _ _).set (k - 1) _ _).at' _ = _
          rw [← ek, at'_set_self, get_eq_at']
        rw [hxA, hsplit, insertSorted_append_last _ _ _ (by simpa [get_eq_at', ek] using hxy)
          (sorted_last_le _ _ (hsplit ▸ hs))]
      · rw [castSize_val, ih2 x (by omega)]
        show ((a.set k _ _).set (k - 1) _ _).at' _ = _
        rw [at'_set_ne _ _ _ _ _ (by omega), at'_set_ne _ _ _ _ _ (by omega)]
    · rename_i hxy
      have hyx : a.at' (k.toNat - 1) ≤ a.at' k.toNat := by
        have := UInt64.not_lt.mp hxy; simpa [get_eq_at', ek] using this
      refine ⟨?_, fun x _ => rfl⟩
      have hsplit : a.slice lo.toNat (k.toNat - lo.toNat) =
          a.slice lo.toNat (k.toNat - 1 - lo.toNat) ++ [a.at' (k.toNat - 1)] := by
        rw [show k.toNat - lo.toNat = (k.toNat - 1 - lo.toNat) + 1 by omega, slice_succ,
          show lo.toNat + (k.toNat - 1 - lo.toNat) = k.toNat - 1 by omega]
      show a.slice lo.toNat (k.toNat + 1 - lo.toNat) = _
      rw [show k.toNat + 1 - lo.toNat = (k.toNat - 1 - lo.toNat) + 1 + 1 by omega, slice_succ, slice_succ,
        show lo.toNat + (k.toNat - 1 - lo.toNat) = k.toNat - 1 by omega,
        show lo.toNat + (k.toNat - 1 - lo.toNat + 1) = k.toNat by omega, hsplit,
        insertSorted_of_last_le _ _ _ hyx (sorted_last_le _ _ (hsplit ▸ hs))]
      simp
  · rename_i h
    have h : ¬ lo.toNat < k.toNat := h
    refine ⟨?_, fun x _ => rfl⟩
    rw [show k.toNat - lo.toNat = 0 by omega, show k.toNat + 1 - lo.toNat = 1 by omega, slice_one, slice_zero,
      show lo.toNat = k.toNat by omega]
    rfl

/-- `insertionSortRange`: the run `[lo, hi)` becomes the insertion sort of its contents. -/
theorem insertionSortRange_spec (lo hi : UInt64) :
    ∀ (m : Nat) (k : UInt64) (a : UInt64Array) hsz hhi hlo, m = hi.toNat - k.toNat → k.toNat ≤ hi.toNat →
    Sorted (a.slice lo.toNat (k.toNat - lo.toNat)) →
    (insertionSortRange lo hi k a hsz hhi hlo).1.slice lo.toNat (hi.toNat - lo.toNat) =
      insertAll (a.slice lo.toNat (k.toNat - lo.toNat)) (a.slice k.toNat (hi.toNat - k.toNat)) ∧
    ∀ x, (x < lo.toNat ∨ hi.toNat ≤ x) → (insertionSortRange lo hi k a hsz hhi hlo).1.at' x = a.at' x := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro k a hsz hhi hlo hm hkhi hs
  rw [insertionSortRange]
  dsimp only
  split
  · rename_i h
    have h : k.toNat < hi.toNat := h
    have ek : (k + 1).toNat = k.toNat + 1 := by u64g
    let Bs := insertLoop lo k a (by u64g) (by u64g) (by u64g)
    obtain ⟨HB1, HB2⟩ := insertLoop_spec lo k.toNat k a (by u64g) (by u64g) (by u64g) rfl hs
    have hBpre : Bs.1.slice lo.toNat ((k + 1).toNat - lo.toNat) = insertSorted (a.at' k.toNat) (a.slice lo.toNat (k.toNat - lo.toNat)) := by
      rw [ek]; exact HB1
    obtain ⟨IH1, IH2⟩ := ih (hi.toNat - (k + 1).toNat) (by rw [ek]; omega) (k + 1) Bs.1 (by rw [Bs.2]; exact hsz)
      (by rw [Bs.2]; exact hhi) (by rw [ek]; omega) rfl (by rw [ek]; omega) (by rw [hBpre]; exact insertSorted_sorted _ _ hs)
    simp only [castSize_val]
    refine ⟨?_, fun x hx => ?_⟩
    · rw [IH1, hBpre, ek]
      have hrest : Bs.1.slice (k.toNat + 1) (hi.toNat - (k.toNat + 1)) = a.slice (k.toNat + 1) (hi.toNat - (k.toNat + 1)) := by
        apply slice_congr; intro t ht; exact HB2 _ (Or.inr (by omega))
      rw [hrest, show hi.toNat - k.toNat = (hi.toNat - (k.toNat + 1)) + 1 by omega, slice_cons]
      rfl
    · rw [IH2 x (by omega), HB2 x (by omega)]
  · rename_i h
    have h : ¬ k.toNat < hi.toNat := h
    refine ⟨?_, fun x _ => rfl⟩
    rw [show hi.toNat - k.toNat = 0 by omega, slice_zero]
    have : hi.toNat - lo.toNat = k.toNat - lo.toNat := by omega
    rw [this]; rfl

/-- `sortBlocks` makes every `w`-block sorted and keeps the contents. -/
theorem sortBlocks_spec (n w : UInt64) (hw0 : 0 < w.toNat) :
    ∀ (m : Nat) (lo : UInt64) (a : UInt64Array) hsz hn hn2 hw, m = n.toNat - lo.toNat →
    ChunkSorted w.toNat hw0 ((sortBlocks n w lo a hsz hn hn2 hw).1.slice lo.toNat (n.toNat - lo.toNat)) ∧
    ((sortBlocks n w lo a hsz hn hn2 hw).1.slice lo.toNat (n.toNat - lo.toNat)).Perm (a.slice lo.toNat (n.toNat - lo.toNat)) ∧
    ∀ x, x < lo.toNat → (sortBlocks n w lo a hsz hn hn2 hw).1.at' x = a.at' x := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro lo a hsz hn hn2 hw hm
  rw [sortBlocks]
  dsimp only
  split
  · rename_i h
    have h : lo.toNat < n.toNat := h
    let HI : UInt64 := if lo + w ≤ n then lo + w else n
    have e1w : (lo + w).toNat = lo.toNat + w.toNat := by u64g
    have hHI : (lo.toNat + w.toNat ≤ n.toNat ∧ HI.toNat = lo.toNat + w.toNat) ∨
        (n.toNat < lo.toNat + w.toNat ∧ HI.toNat = n.toNat) := by
      by_cases hc : lo + w ≤ n
      · have hc' := UInt64.le_iff_toNat_le.mp hc
        left; refine ⟨by omega, ?_⟩
        show (if lo + w ≤ n then lo + w else n).toNat = _; rw [if_pos hc, e1w]
      · have hc' : ¬ (lo + w).toNat ≤ n.toNat := fun h => hc (UInt64.le_iff_toNat_le.mpr h)
        right; refine ⟨by omega, ?_⟩
        show (if lo + w ≤ n then lo + w else n).toNat = _; rw [if_neg hc]
    let Bs := insertionSortRange lo HI lo a (by u64g) (by omega) (by u64g)
    obtain ⟨HB1, HB2⟩ := insertionSortRange_spec lo HI (HI.toNat - lo.toNat) lo a (by u64g) (by omega) (by u64g) rfl
      (by omega) (by rw [Nat.sub_self, slice_zero]; simp [Sorted])
    rw [Nat.sub_self, slice_zero] at HB1
    obtain ⟨IH1, IH2, IH3⟩ := ih (n.toNat - (lo + w).toNat) (by omega) (lo + w) Bs.1 (by rw [Bs.2]; exact hsz)
      (by rw [Bs.2]; exact hn) hn2 hw rfl
    simp only [castSize_val]
    -- decompose `[lo, n)` into the block `[lo, HI)` and the rest
    have eL : ∀ R : UInt64Array, R.slice lo.toNat (n.toNat - lo.toNat) =
        R.slice lo.toNat (HI.toNat - lo.toNat) ++ R.slice HI.toNat (n.toNat - HI.toNat) := by
      intro R
      rw [show R.slice HI.toNat (n.toNat - HI.toNat) = R.slice (lo.toNat + (HI.toNat - lo.toNat)) (n.toNat - HI.toNat) by
        congr 1; omega, ← slice_add]
      congr 1; omega
    have hblock : (sortBlocks n w (lo + w) Bs.1 (by rw [Bs.2]; exact hsz) (by rw [Bs.2]; exact hn) hn2 hw).1.slice
        lo.toNat (HI.toNat - lo.toNat) = Bs.1.slice lo.toNat (HI.toNat - lo.toNat) := by
      apply slice_congr; intro t ht; exact IH3 _ (by omega)
    have hrest : (sortBlocks n w (lo + w) Bs.1 (by rw [Bs.2]; exact hsz) (by rw [Bs.2]; exact hn) hn2 hw).1.slice
        HI.toNat (n.toNat - HI.toNat) =
        (sortBlocks n w (lo + w) Bs.1 (by rw [Bs.2]; exact hsz) (by rw [Bs.2]; exact hn) hn2 hw).1.slice
        (lo + w).toNat (n.toNat - (lo + w).toNat) := by
      rcases hHI with ⟨_, hH⟩ | ⟨_, hH⟩
      · rw [hH, e1w]
      · rw [hH, show n.toNat - n.toNat = 0 by omega, show n.toNat - (lo + w).toNat = 0 by omega, slice_zero, slice_zero]
    have hBrest : Bs.1.slice HI.toNat (n.toNat - HI.toNat) = a.slice HI.toNat (n.toNat - HI.toNat) := by
      apply slice_congr; intro t ht; exact HB2 _ (Or.inr (by omega))
    have hBblockSorted : Sorted (Bs.1.slice lo.toNat (HI.toNat - lo.toNat)) := by
      rw [HB1]; exact insertAll_sorted _ _ (by simp [Sorted])
    have hBblockPerm : (Bs.1.slice lo.toNat (HI.toNat - lo.toNat)).Perm (a.slice lo.toNat (HI.toNat - lo.toNat)) := by
      rw [HB1]; simpa using insertAll_perm [] _
    have hlen : (Bs.1.slice lo.toNat (HI.toNat - lo.toNat)).length = HI.toNat - lo.toNat := by simp
    refine ⟨?_, ?_, fun x hx => ?_⟩
    · rw [eL, hblock, hrest]
      rcases hHI with ⟨hle, hH⟩ | ⟨hlt, hH⟩
      · -- a full block of length w, then the rest
        by_cases hrest0 : n.toNat - (lo + w).toNat = 0
        · rw [hrest0, slice_zero, List.append_nil, chunkSorted_of_length_le _ (by simp; omega)]
          exact hBblockSorted
        · rw [chunkSorted_of_lt _ (by rw [List.length_append, hlen]; simp; omega)]
          rw [List.take_left' (by rw [hlen, hH]; omega), List.drop_left' (by rw [hlen, hH]; omega)]
          exact ⟨hBblockSorted, IH1⟩
      · -- last, short block
        rw [show n.toNat - (lo + w).toNat = 0 by omega, slice_zero, List.append_nil,
          chunkSorted_of_length_le _ (by simp; omega)]
        exact hBblockSorted
    · rw [eL, hblock, hrest, eL a]
      rcases hHI with ⟨hle, hH⟩ | ⟨hlt, hH⟩
      · rw [show HI.toNat = (lo + w).toNat by rw [hH, e1w]] at hBrest hBblockPerm ⊢
        exact hBblockPerm.append (IH2.trans (by rw [hBrest]))
      · rw [show n.toNat - (lo + w).toNat = 0 by omega, show n.toNat - HI.toNat = 0 by omega, slice_zero, slice_zero,
          List.append_nil, List.append_nil]
        exact hBblockPerm
    · rw [IH3 x (by omega), HB2 x (Or.inl hx)]
  · rename_i h
    have h : ¬ lo.toNat < n.toNat := h
    refine ⟨?_, ?_, fun x _ => rfl⟩
    · rw [show n.toNat - lo.toNat = 0 by omega, slice_zero, chunkSorted_of_length_le _ (by simp)]; simp [Sorted]
    · exact List.Perm.refl _

theorem sort16_sorted (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : Sorted (sort16 xs hsz).data.toList := by
  rw [sort16]
  have hn : (xs.size.toUInt64).toNat = xs.size := by simp; omega
  split
  · rename_i h
    have h : 16 < (xs.size.toUInt64).toNat := h
    let Bs := sortBlocks xs.size.toUInt64 16 0 xs (by omega) (by omega) (by omega) (by u64g)
    obtain ⟨S1, P1, _⟩ := sortBlocks_spec xs.size.toUInt64 16 (by decide) ((xs.size.toUInt64).toNat - (0 : UInt64).toNat) 0 xs
      (by omega) (by omega) (by omega) (by u64g) rfl
    simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.sub_zero] at S1
    obtain ⟨S, _⟩ := widthLoop_spec xs.size.toUInt64 (by omega) _ 16 Bs.1 (zeros xs.size) (by omega)
      (by rw [Bs.2]; exact hn) (by simp [hn]) (by decide) rfl (chunkSorted_congr (by decide) _ _ S1)
    have hs' : (widthLoop xs.size.toUInt64 16 Bs.1 (zeros xs.size) (by omega) (by rw [Bs.2]; exact hn) (by simp [hn]) (by decide)).1.size =
        (xs.size.toUInt64).toNat := by rw [(widthLoop _ _ _ _ _ _ _ _).2, Bs.2, hn]
    rw [← slice_eq_toList, hs']
    exact S
  · rename_i h
    have h : ¬ 16 < (xs.size.toUInt64).toNat := h
    obtain ⟨S1, _⟩ := insertionSortRange_spec 0 xs.size.toUInt64 ((xs.size.toUInt64).toNat - (0 : UInt64).toNat) 0 xs
      (by omega) (by omega) (by u64g) rfl (by u64g) (by simp [Sorted])
    simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.sub_zero, slice_zero] at S1
    have hs' : (insertionSortRange 0 xs.size.toUInt64 0 xs (by omega) (by omega) (by u64g)).1.size = (xs.size.toUInt64).toNat := by
      rw [(insertionSortRange _ _ _ _ _ _ _).2, hn]
    rw [← slice_eq_toList, hs', S1]
    exact insertAll_sorted _ _ (by simp [Sorted])

theorem sort16_perm (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : (sort16 xs hsz).data.toList.Perm xs.data.toList := by
  rw [sort16]
  have hn : (xs.size.toUInt64).toNat = xs.size := by simp; omega
  have exs : xs.slice 0 (xs.size.toUInt64).toNat = xs.data.toList := by rw [hn, slice_eq_toList]
  split
  · rename_i h
    have h : 16 < (xs.size.toUInt64).toNat := h
    let Bs := sortBlocks xs.size.toUInt64 16 0 xs (by omega) (by omega) (by omega) (by u64g)
    obtain ⟨S1, P1, _⟩ := sortBlocks_spec xs.size.toUInt64 16 (by decide) ((xs.size.toUInt64).toNat - (0 : UInt64).toNat) 0 xs
      (by omega) (by omega) (by omega) (by u64g) rfl
    simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.sub_zero] at S1 P1
    obtain ⟨_, P⟩ := widthLoop_spec xs.size.toUInt64 (by omega) _ 16 Bs.1 (zeros xs.size) (by omega)
      (by rw [Bs.2]; exact hn) (by simp [hn]) (by decide) rfl (chunkSorted_congr (by decide) _ _ S1)
    have hs' : (widthLoop xs.size.toUInt64 16 Bs.1 (zeros xs.size) (by omega) (by rw [Bs.2]; exact hn) (by simp [hn]) (by decide)).1.size =
        (xs.size.toUInt64).toNat := by rw [(widthLoop _ _ _ _ _ _ _ _).2, Bs.2, hn]
    rw [← slice_eq_toList, hs', ← exs]
    exact P.trans P1
  · rename_i h
    have h : ¬ 16 < (xs.size.toUInt64).toNat := h
    obtain ⟨S1, _⟩ := insertionSortRange_spec 0 xs.size.toUInt64 ((xs.size.toUInt64).toNat - (0 : UInt64).toNat) 0 xs
      (by omega) (by omega) (by u64g) rfl (by u64g) (by simp [Sorted])
    simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.sub_zero, slice_zero] at S1
    have hs' : (insertionSortRange 0 xs.size.toUInt64 0 xs (by omega) (by omega) (by u64g)).1.size = (xs.size.toUInt64).toNat := by
      rw [(insertionSortRange _ _ _ _ _ _ _).2, hn]
    rw [← slice_eq_toList, hs', S1, ← exs]
    simpa using insertAll_perm [] _

end MergeSort.BottomUp
