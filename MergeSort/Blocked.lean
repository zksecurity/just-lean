import MergeSort.BidiSort
/-!
# Advanced trick: cache-blocked pass order

Sort every block of `B` elements completely (all its passes stay in cache), then merge the blocks
with the usual width loop starting at `w = B`. Passes come in pairs (`src → dst → src`), so every
block's result lands back in `src` and no buffer bookkeeping is needed; a pair whose run length
already exceeds the block is a harmless copy.
-/
namespace MergeSort.BottomUp
open UInt64Array MergeSort.Fast

/-- Both buffers are threaded through (returning only one would leave a second reference to the
    other, and the next write would copy it). -/
abbrev Pair (a b : UInt64Array) := { p : UInt64Array × UInt64Array // p.1.size = a.size ∧ p.2.size = b.size }

@[inline] def castPair {a b a' b' : UInt64Array} (r : Pair a b) (h1 : a.size = a'.size) (h2 : b.size = b'.size) :
    Pair a' b' := ⟨r.1, r.2.1.trans h1, r.2.2.trans h2⟩

@[simp] theorem castPair_val {a b a' b' : UInt64Array} (r : Pair a b) (h1 : a.size = a'.size) (h2 : b.size = b'.size) :
    (castPair r h1 h2).1 = r.1 := rfl

/-- Two passes over `[lo, hi)`: run length `w` from `src` into `dst`, then `2w` back into `src`. -/
def twoPasses (w lo hi : UInt64) (src dst : UInt64Array)
    (hhi : hi.toNat < 2 ^ 62 := by u64) (hs : hi.toNat ≤ src.size := by u64) (hd : hi.toNat ≤ dst.size := by u64)
    (hssz : src.size < 2 ^ 64 := by u64) (hdsz : dst.size < 2 ^ 64 := by u64)
    (hw : 1 ≤ w.toNat ∧ w.toNat < 2 ^ 61 := by u64) : Pair src dst :=
  let ⟨d, hd'⟩ := passLoop2 hi w lo src dst
  let ⟨s, hs'⟩ := passLoop2 hi (2 * w) lo d src (hs := by rw [hd']; exact hd) (hw := by u64)
  ⟨(s, d), hs', hd'⟩

/-- Sort the block `[lo, hi)` (of length at most `B`) with pairs of passes; result in `src`.
    Passes stop as soon as one run covers the block, so small blocks do not pay for empty passes. -/
def blockPasses (w B lo hi : UInt64) (src dst : UInt64Array)
    (hhi : hi.toNat < 2 ^ 62 := by u64) (hs : hi.toNat ≤ src.size := by u64) (hd : hi.toNat ≤ dst.size := by u64)
    (hssz : src.size < 2 ^ 64 := by u64) (hdsz : dst.size < 2 ^ 64 := by u64)
    (hw : 1 ≤ w.toNat := by u64) (hB : B.toNat < 2 ^ 61 := by u64) (hlo : lo.toNat ≤ hi.toNat := by u64)
    (hlen : hi.toNat - lo.toNat ≤ B.toNat := by u64) : Pair src dst :=
  if h : w < hi - lo then
    have h : w.toNat < hi.toNat - lo.toNat := by have := UInt64.lt_iff_toNat_lt.mp h; u64
    let r := twoPasses w lo hi src dst
    castPair (blockPasses (4 * w) B lo hi r.1.1 r.1.2 (hs := by rw [r.2.1]; exact hs) (hd := by rw [r.2.2]; exact hd)
      (hssz := by rw [r.2.1]; exact hssz) (hdsz := by rw [r.2.2]; exact hdsz) (hw := by u64)) r.2.1 r.2.2
  else ⟨(src, dst), rfl, rfl⟩
termination_by B.toNat - w.toNat
decreasing_by u64

/-- Sort every block `[lo, lo + B)` (clipped to `n`); results stay in `src`. -/
def blocksLoop (B n lo : UInt64) (src dst : UInt64Array)
    (hn : n.toNat < 2 ^ 62 := by u64) (hs : n.toNat ≤ src.size := by u64) (hd : n.toNat ≤ dst.size := by u64)
    (hssz : src.size < 2 ^ 64 := by u64) (hdsz : dst.size < 2 ^ 64 := by u64)
    (hB : 1 ≤ B.toNat ∧ B.toNat < 2 ^ 61 := by u64) : Pair src dst :=
  if h : lo < n then
    have h : lo.toNat < n.toNat := h
    let hi := if lo + B ≤ n then lo + B else n
    have hhi : hi.toNat ≤ n.toNat := by
      show (if lo + B ≤ n then lo + B else n).toNat ≤ _; split <;> u64
    have hlo' : lo.toNat ≤ hi.toNat := by
      show lo.toNat ≤ (if lo + B ≤ n then lo + B else n).toNat; split <;> u64
    have hlen' : hi.toNat - lo.toNat ≤ B.toNat := by
      show (if lo + B ≤ n then lo + B else n).toNat - lo.toNat ≤ B.toNat; split <;> u64
    let r := blockPasses 1 B lo hi src dst (hlo := hlo') (hlen := hlen')
    castPair (blocksLoop B n (lo + B) r.1.1 r.1.2 (hs := by rw [r.2.1]; exact hs) (hd := by rw [r.2.2]; exact hd)
      (hssz := by rw [r.2.1]; exact hssz) (hdsz := by rw [r.2.2]; exact hdsz)) r.2.1 r.2.2
  else ⟨(src, dst), rfl, rfl⟩
termination_by n.toNat - lo.toNat
decreasing_by u64

/-- Cache-blocked bidirectional bottom-up merge sort with block size `B`. -/
def sortBlockedB (B : UInt64) (xs : UInt64Array) (hsz : xs.size < 2 ^ 62)
    (hB : 1 ≤ B.toNat ∧ B.toNat < 2 ^ 61) : UInt64Array :=
  let n : UInt64 := xs.size.toUInt64
  have hn : n.toNat = xs.size := by simp [n]; omega
  let r := blocksLoop B n 0 xs (zeros xs.size)
  (widthLoop2 n B r.1.1 r.1.2 (hs := by rw [r.2.1]; exact hn) (hd := by rw [r.2.2]; simp [hn])).1

/-- Blocks of 2^14 elements (128 KiB of `u64`). -/
def sortBlocked (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : UInt64Array :=
  sortBlockedB 16384 xs hsz (by u64)

/-! ## Specifications -/

theorem twoPasses_spec (w lo hi : UInt64) (src dst : UInt64Array) hhi hs hd hssz hdsz hw (hw0 : 0 < w.toNat)
    (hcs : ChunkSorted w.toNat hw0 (src.slice lo.toNat (hi.toNat - lo.toNat))) :
    ChunkSorted (4 * w.toNat) (by omega) ((twoPasses w lo hi src dst hhi hs hd hssz hdsz hw).1.1.slice lo.toNat (hi.toNat - lo.toNat)) ∧
    ((twoPasses w lo hi src dst hhi hs hd hssz hdsz hw).1.1.slice lo.toNat (hi.toNat - lo.toNat)).Perm
      (src.slice lo.toNat (hi.toNat - lo.toNat)) ∧
    ∀ x, (x < lo.toNat ∨ hi.toNat ≤ x) → (twoPasses w lo hi src dst hhi hs hd hssz hdsz hw).1.1.at' x = src.at' x := by
  rw [twoPasses]
  dsimp only
  have e2 : (2 * w).toNat = 2 * w.toNat := by u64g
  have hw' : 1 ≤ w.toNat ∧ w.toNat < 2 ^ 62 := ⟨hw.1, by omega⟩
  let D := passLoop2 hi w lo src dst hhi hs hd hdsz hw'
  obtain ⟨P1, P2⟩ := passLoop2_spec hi w src hw0 (hi.toNat - lo.toNat) lo dst hhi hs hd hdsz hw' rfl hcs
  have hcs2 : ChunkSorted (2 * w).toNat (by omega) (D.1.slice lo.toNat (hi.toNat - lo.toNat)) := by
    rw [P1]; exact chunkSorted_congr e2.symm _ _ (chunkSorted_mergeRuns hw0 _ hcs)
  obtain ⟨Q1, Q2⟩ := passLoop2_spec hi (2 * w) D.1 (by omega) (hi.toNat - lo.toNat) lo src hhi (by rw [D.2]; exact hd) hs hssz
    (by u64) rfl hcs2
  refine ⟨?_, ?_, fun x hx => Q2 x hx⟩
  · rw [Q1]
    have h2 := chunkSorted_mergeRuns (w := (2 * w).toNat) (by omega) _ hcs2
    exact chunkSorted_congr (by omega) _ _ h2
  · rw [Q1]
    exact (mergeRuns_perm (by omega) (D.1.slice lo.toNat (hi.toNat - lo.toNat))).trans (by rw [P1]; exact mergeRuns_perm hw0 _)

theorem blockPasses_spec (B lo hi : UInt64) :
    ∀ (m : Nat) (w : UInt64) (src dst : UInt64Array) hhi hs hd hssz hdsz hw hB hlo hlen, m = B.toNat - w.toNat →
    ChunkSorted w.toNat (by omega) (src.slice lo.toNat (hi.toNat - lo.toNat)) →
    Sorted ((blockPasses w B lo hi src dst hhi hs hd hssz hdsz hw hB hlo hlen).1.1.slice lo.toNat (hi.toNat - lo.toNat)) ∧
    ((blockPasses w B lo hi src dst hhi hs hd hssz hdsz hw hB hlo hlen).1.1.slice lo.toNat (hi.toNat - lo.toNat)).Perm
      (src.slice lo.toNat (hi.toNat - lo.toNat)) ∧
    ∀ x, (x < lo.toNat ∨ hi.toNat ≤ x) →
      (blockPasses w B lo hi src dst hhi hs hd hssz hdsz hw hB hlo hlen).1.1.at' x = src.at' x := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro w src dst hhi hs hd hssz hdsz hw hB hlo hlen hm hcs
  rw [blockPasses]
  dsimp only
  split
  · rename_i h
    have h : w.toNat < hi.toNat - lo.toNat := by have := UInt64.lt_iff_toNat_lt.mp h; u64
    have e4 : (4 * w).toNat = 4 * w.toNat := by u64g
    let S := twoPasses w lo hi src dst hhi hs hd hssz hdsz (by u64)
    obtain ⟨T1, T2, T3⟩ := twoPasses_spec w lo hi src dst hhi hs hd hssz hdsz (by u64) (by omega) hcs
    obtain ⟨IH1, IH2, IH3⟩ := ih (B.toNat - (4 * w).toNat) (by omega) (4 * w) S.1.1 S.1.2 hhi (by rw [S.2.1]; exact hs)
      (by rw [S.2.2]; exact hd) (by rw [S.2.1]; exact hssz) (by rw [S.2.2]; exact hdsz) (by u64) hB hlo hlen rfl
      (chunkSorted_congr e4.symm _ _ T1)
    simp only [castPair_val]
    exact ⟨IH1, IH2.trans T2, fun x hx => (IH3 x hx).trans (T3 x hx)⟩
  · rename_i h
    have h : ¬ w.toNat < hi.toNat - lo.toNat := fun c => h (UInt64.lt_iff_toNat_lt.mpr (by u64g))
    exact ⟨sorted_of_chunkSorted _ (by simp; omega) hcs, List.Perm.refl _, fun x _ => rfl⟩

theorem blocksLoop_spec (B n : UInt64) (hB0 : 0 < B.toNat) :
    ∀ (m : Nat) (lo : UInt64) (src dst : UInt64Array) hn hs hd hssz hdsz hB, m = n.toNat - lo.toNat →
    ChunkSorted B.toNat hB0 ((blocksLoop B n lo src dst hn hs hd hssz hdsz hB).1.1.slice lo.toNat (n.toNat - lo.toNat)) ∧
    ((blocksLoop B n lo src dst hn hs hd hssz hdsz hB).1.1.slice lo.toNat (n.toNat - lo.toNat)).Perm
      (src.slice lo.toNat (n.toNat - lo.toNat)) ∧
    ∀ x, x < lo.toNat → (blocksLoop B n lo src dst hn hs hd hssz hdsz hB).1.1.at' x = src.at' x := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro lo src dst hn hs hd hssz hdsz hB hm
  rw [blocksLoop]
  dsimp only
  split
  · rename_i h
    have h : lo.toNat < n.toNat := h
    let HI : UInt64 := if lo + B ≤ n then lo + B else n
    have e1 : (lo + B).toNat = lo.toNat + B.toNat := by u64g
    have hHI : (lo.toNat + B.toNat ≤ n.toNat ∧ HI.toNat = lo.toNat + B.toNat) ∨
        (n.toNat < lo.toNat + B.toNat ∧ HI.toNat = n.toNat) := by
      by_cases hc : lo + B ≤ n
      · have hc' := UInt64.le_iff_toNat_le.mp hc
        left; refine ⟨by omega, ?_⟩
        show (if lo + B ≤ n then lo + B else n).toNat = _; rw [if_pos hc, e1]
      · have hc' : ¬ (lo + B).toNat ≤ n.toNat := fun h => hc (UInt64.le_iff_toNat_le.mpr h)
        right; refine ⟨by omega, ?_⟩
        show (if lo + B ≤ n then lo + B else n).toNat = _; rw [if_neg hc]
    let S := blockPasses 1 B lo HI src dst (by omega) (by omega) (by omega) hssz hdsz (by u64) (by omega) (by omega) (by omega)
    obtain ⟨T1, T2, T3⟩ := blockPasses_spec B lo HI (B.toNat - (1 : UInt64).toNat) 1 src dst (by omega) (by omega)
      (by omega) hssz hdsz (by u64) (by omega) (by omega) (by omega) rfl (chunkSorted_congr (by simp) _ _ (chunkSorted_one _))
    obtain ⟨IH1, IH2, IH3⟩ := ih (n.toNat - (lo + B).toNat) (by omega) (lo + B) S.1.1 S.1.2 hn (by rw [S.2.1]; exact hs)
      (by rw [S.2.2]; exact hd) (by rw [S.2.1]; exact hssz) (by rw [S.2.2]; exact hdsz) hB rfl
    simp only [castPair_val]
    have eL : ∀ R : UInt64Array, R.slice lo.toNat (n.toNat - lo.toNat) =
        R.slice lo.toNat (HI.toNat - lo.toNat) ++ R.slice HI.toNat (n.toNat - HI.toNat) := by
      intro R
      rw [show R.slice HI.toNat (n.toNat - HI.toNat) = R.slice (lo.toNat + (HI.toNat - lo.toNat)) (n.toNat - HI.toNat) by
        congr 1; omega, ← slice_add]
      congr 1; omega
    have hblock : (blocksLoop B n (lo + B) S.1.1 S.1.2 hn (by rw [S.2.1]; exact hs) (by rw [S.2.2]; exact hd) (by rw [S.2.1]; exact hssz) (by rw [S.2.2]; exact hdsz) hB).1.1.slice
        lo.toNat (HI.toNat - lo.toNat) = S.1.1.slice lo.toNat (HI.toNat - lo.toNat) := by
      apply slice_congr; intro t ht; exact IH3 _ (by omega)
    have hrest : (blocksLoop B n (lo + B) S.1.1 S.1.2 hn (by rw [S.2.1]; exact hs) (by rw [S.2.2]; exact hd) (by rw [S.2.1]; exact hssz) (by rw [S.2.2]; exact hdsz) hB).1.1.slice
        HI.toNat (n.toNat - HI.toNat) =
        (blocksLoop B n (lo + B) S.1.1 S.1.2 hn (by rw [S.2.1]; exact hs) (by rw [S.2.2]; exact hd) (by rw [S.2.1]; exact hssz) (by rw [S.2.2]; exact hdsz) hB).1.1.slice
        (lo + B).toNat (n.toNat - (lo + B).toNat) := by
      rcases hHI with ⟨_, hH⟩ | ⟨_, hH⟩
      · rw [hH, e1]
      · rw [hH, show n.toNat - n.toNat = 0 by omega, show n.toNat - (lo + B).toNat = 0 by omega, slice_zero, slice_zero]
    have hSrest : S.1.1.slice HI.toNat (n.toNat - HI.toNat) = src.slice HI.toNat (n.toNat - HI.toNat) := by
      apply slice_congr; intro t ht; exact T3 _ (Or.inr (by omega))
    have hlen : (S.1.1.slice lo.toNat (HI.toNat - lo.toNat)).length = HI.toNat - lo.toNat := by simp
    refine ⟨?_, ?_, fun x hx => ?_⟩
    · rw [eL, hblock, hrest]
      rcases hHI with ⟨hle, hH⟩ | ⟨hlt, hH⟩
      · by_cases hrest0 : n.toNat - (lo + B).toNat = 0
        · rw [hrest0, slice_zero, List.append_nil, chunkSorted_of_length_le _ (by simp; omega)]
          exact T1
        · rw [chunkSorted_of_lt _ (by rw [List.length_append, hlen]; simp; omega)]
          rw [List.take_left' (by rw [hlen, hH]; omega), List.drop_left' (by rw [hlen, hH]; omega)]
          exact ⟨T1, IH1⟩
      · rw [show n.toNat - (lo + B).toNat = 0 by omega, slice_zero, List.append_nil,
          chunkSorted_of_length_le _ (by simp; omega)]
        exact T1
    · rw [eL, hblock, hrest, eL src]
      rcases hHI with ⟨hle, hH⟩ | ⟨hlt, hH⟩
      · have hSrest' : S.1.1.slice (lo + B).toNat (n.toNat - (lo + B).toNat) = src.slice (lo + B).toNat (n.toNat - (lo + B).toNat) := by
          rw [e1, ← hH]; exact hSrest
        rw [show src.slice HI.toNat (n.toNat - HI.toNat) = src.slice (lo + B).toNat (n.toNat - (lo + B).toNat) by rw [hH, e1]]
        exact T2.append (IH2.trans (by rw [hSrest']))
      · rw [show n.toNat - (lo + B).toNat = 0 by omega, show n.toNat - HI.toNat = 0 by omega, slice_zero, slice_zero,
          List.append_nil, List.append_nil]
        exact T2
    · rw [IH3 x (by omega), T3 x (Or.inl hx)]
  · rename_i h
    have h : ¬ lo.toNat < n.toNat := h
    refine ⟨?_, ?_, fun x _ => rfl⟩
    · rw [show n.toNat - lo.toNat = 0 by omega, slice_zero, chunkSorted_of_length_le _ (by simp)]; simp [Sorted]
    · exact List.Perm.refl _

theorem sortBlockedB_sorted (B : UInt64) (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) (hB : 1 ≤ B.toNat ∧ B.toNat < 2 ^ 61) :
    Sorted (sortBlockedB B xs hsz hB).data.toList := by
  rw [sortBlockedB]
  have hn : (xs.size.toUInt64).toNat = xs.size := by simp; omega
  let A := blocksLoop B xs.size.toUInt64 0 xs (zeros xs.size) (by omega) (by omega) (by simp; omega) (by omega) (by simp; omega) hB
  have hA2 : A.1.2.size = xs.size := by simpa using A.2.2
  obtain ⟨C1, _, _⟩ := blocksLoop_spec B xs.size.toUInt64 (by omega) ((xs.size.toUInt64).toNat - (0 : UInt64).toNat) 0 xs
    (zeros xs.size) (by omega) (by omega) (by simp; omega) (by omega) (by simp; omega) hB rfl
  simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.sub_zero] at C1
  obtain ⟨S, _⟩ := widthLoop2_spec xs.size.toUInt64 (by omega) _ B A.1.1 A.1.2 (by omega)
    (by rw [A.2.1]; exact hn) (by rw [hA2]; exact hn) (by omega) rfl C1
  have hs' : (widthLoop2 xs.size.toUInt64 B A.1.1 A.1.2 (by omega) (by rw [A.2.1]; exact hn) (by rw [hA2]; exact hn) (by omega)).1.size =
      (xs.size.toUInt64).toNat := by rw [(widthLoop2 _ _ _ _ _ _ _ _).2, A.2.1, hn]
  rw [← slice_eq_toList, hs']
  exact S

theorem sortBlockedB_perm (B : UInt64) (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) (hB : 1 ≤ B.toNat ∧ B.toNat < 2 ^ 61) :
    (sortBlockedB B xs hsz hB).data.toList.Perm xs.data.toList := by
  rw [sortBlockedB]
  have hn : (xs.size.toUInt64).toNat = xs.size := by simp; omega
  have exs : xs.slice 0 (xs.size.toUInt64).toNat = xs.data.toList := by rw [hn, slice_eq_toList]
  let A := blocksLoop B xs.size.toUInt64 0 xs (zeros xs.size) (by omega) (by omega) (by simp; omega) (by omega) (by simp; omega) hB
  have hA2 : A.1.2.size = xs.size := by simpa using A.2.2
  obtain ⟨C1, C2, _⟩ := blocksLoop_spec B xs.size.toUInt64 (by omega) ((xs.size.toUInt64).toNat - (0 : UInt64).toNat) 0 xs
    (zeros xs.size) (by omega) (by omega) (by simp; omega) (by omega) (by simp; omega) hB rfl
  simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.sub_zero] at C1 C2
  obtain ⟨_, P⟩ := widthLoop2_spec xs.size.toUInt64 (by omega) _ B A.1.1 A.1.2 (by omega)
    (by rw [A.2.1]; exact hn) (by rw [hA2]; exact hn) (by omega) rfl C1
  have hs' : (widthLoop2 xs.size.toUInt64 B A.1.1 A.1.2 (by omega) (by rw [A.2.1]; exact hn) (by rw [hA2]; exact hn) (by omega)).1.size =
      (xs.size.toUInt64).toNat := by rw [(widthLoop2 _ _ _ _ _ _ _ _).2, A.2.1, hn]
  rw [← slice_eq_toList, hs', ← exs]
  exact P.trans C2

theorem sortBlocked_sorted (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : Sorted (sortBlocked xs hsz).data.toList :=
  sortBlockedB_sorted 16384 xs hsz _

theorem sortBlocked_perm (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : (sortBlocked xs hsz).data.toList.Perm xs.data.toList :=
  sortBlockedB_perm 16384 xs hsz _

end MergeSort.BottomUp
