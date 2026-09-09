import MergeSort.Blocked
import MergeSort.SmallRunsCorrect
/-! A verified "already sorted?" pre-check, so presorted inputs cost one linear pass. -/
namespace MergeSort.BottomUp
open UInt64Array MergeSort.Fast

/-- Is `a[k-1] ≤ a[k]` for all `k` in `[i, n)`? -/
def isSortedFrom (n i : UInt64) (a : UInt64Array) (hsz : a.size < 2 ^ 64 := by u64) (hn : n.toNat ≤ a.size := by u64)
    (hi : 1 ≤ i.toNat ∧ i.toNat ≤ n.toNat := by u64) : Bool :=
  if h : i < n then
    have h : i.toNat < n.toNat := h
    if a.get (i - 1) ≤ a.get i then isSortedFrom n (i + 1) a else false
  else true
termination_by n.toNat - i.toNat
decreasing_by u64

theorem isSortedFrom_sorted (n : UInt64) (a : UInt64Array) :
    ∀ (m : Nat) (i : UInt64) hsz hn hi, m = n.toNat - i.toNat →
    Sorted le64 (a.slice 0 i.toNat) → isSortedFrom n i a hsz hn hi = true → Sorted le64 (a.slice 0 n.toNat) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro i hsz hn hi hm hs hb
  rw [isSortedFrom] at hb
  split at hb
  · rename_i h
    have h : i.toNat < n.toNat := h
    have ei : (i + 1).toNat = i.toNat + 1 := by u64g
    have ei' : (i - 1).toNat = i.toNat - 1 := by u64g
    dsimp only at hb
    split at hb
    · rename_i hle
      refine ih (n.toNat - (i + 1).toNat) (by omega) (i + 1) hsz hn (by omega) rfl ?_ hb
      rw [ei, slice_succ, Nat.zero_add]
      have hlast : ∀ z ∈ a.slice 0 i.toNat, z ≤ a.at' i.toNat := by
        intro z hz
        have hsplit : a.slice 0 i.toNat = a.slice 0 (i.toNat - 1) ++ [a.at' (i.toNat - 1)] := by
          rw [show i.toNat = (i.toNat - 1) + 1 by omega, slice_succ, Nat.zero_add,
            show i.toNat - 1 + 1 - 1 = i.toNat - 1 by omega]
        rw [hsplit] at hz hs
        have hle' : a.at' (i.toNat - 1) ≤ a.at' i.toNat := by simpa [get_eq_at', ei'] using hle
        rcases List.mem_append.mp hz with hz | hz
        · exact UInt64.le_trans (sorted_last_le _ _ hs z hz) hle'
        · simp at hz; subst hz; exact hle'
      rw [Sorted, List.pairwise_append]
      exact ⟨hs, List.pairwise_singleton _ _, fun z hz y hy => by simp at hy; subst hy; simpa using hlast z hz⟩
    · simp at hb
  · rename_i h
    have h : ¬ i.toNat < n.toNat := h
    rw [show n.toNat = i.toNat by omega]
    exact hs

/-- Check for an already sorted input first (one linear pass), otherwise sort. -/
def sortAdaptive (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : UInt64Array :=
  let n : UInt64 := xs.size.toUInt64
  have hn : n.toNat = xs.size := by simp [n]; omega
  if h : 1 < n then
    have h : 1 < n.toNat := h
    if isSortedFrom n 1 xs then xs else sortBlocked xs hsz
  else xs

/-- The adaptive sort (sorted check only) produces a sorted list. -/
theorem sortAdaptive_sorted (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : Sorted le64 (sortAdaptive xs hsz).data.toList := by
  rw [sortAdaptive]
  have hn : (xs.size.toUInt64).toNat = xs.size := by simp; omega
  dsimp only
  split
  · rename_i h
    have h : 1 < (xs.size.toUInt64).toNat := h
    split
    · rename_i hb
      have := isSortedFrom_sorted xs.size.toUInt64 xs _ 1 (by omega) (by omega) (by u64g) rfl
        (by simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, slice_one]; simp [Sorted]) hb
      rw [hn, slice_eq_toList] at this
      exact this
    · exact sortBlocked_sorted xs hsz
  · rename_i h
    have h : ¬ 1 < (xs.size.toUInt64).toNat := h
    rw [← slice_eq_toList]
    exact sorted_of_length_le_one _ (by simp; omega)

/-- The adaptive sort (sorted check only) produces a permutation of its input. -/
theorem sortAdaptive_perm (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : (sortAdaptive xs hsz).data.toList.Perm xs.data.toList := by
  rw [sortAdaptive]
  dsimp only
  split
  · split
    · exact List.Perm.refl _
    · exact sortBlocked_perm xs hsz
  · exact List.Perm.refl _

end MergeSort.BottomUp

namespace MergeSort.BottomUp
open UInt64Array MergeSort.Fast

/-- Is `a[k-1] > a[k]` for all `k` in `[i, n)` (strictly descending)? -/
def isDescFrom (n i : UInt64) (a : UInt64Array) (hsz : a.size < 2 ^ 64 := by u64) (hn : n.toNat ≤ a.size := by u64)
    (hi : 1 ≤ i.toNat ∧ i.toNat ≤ n.toNat := by u64) : Bool :=
  if h : i < n then
    have h : i.toNat < n.toNat := h
    if a.get i < a.get (i - 1) then isDescFrom n (i + 1) a else false
  else true

/-- Reverse `a[lo, hi)` in place. -/
def reverseRange (lo hi : UInt64) (a : UInt64Array) (hsz : a.size < 2 ^ 64 := by u64) (hhi : hi.toNat ≤ a.size := by u64)
    (hlo : lo.toNat ≤ hi.toNat := by u64) : { b : UInt64Array // b.size = a.size } :=
  if h : 1 < hi - lo then
    have h : lo.toNat + 1 < hi.toNat := by have := UInt64.lt_iff_toNat_lt.mp h; u64
    let x := a.get lo
    let y := a.get (hi - 1)
    Fast.castSize (reverseRange (lo + 1) (hi - 1) ((a.set lo y).set (hi - 1) x)) (by simp)
  else ⟨a, rfl⟩
termination_by hi.toNat - lo.toNat
decreasing_by u64

end MergeSort.BottomUp

namespace MergeSort.BottomUp
open UInt64Array MergeSort.Fast

theorem reverseRange_spec :
    ∀ (m : Nat) (lo hi : UInt64) (a : UInt64Array) hsz hhi hlo, m = hi.toNat - lo.toNat →
    (reverseRange lo hi a hsz hhi hlo).1.slice lo.toNat (hi.toNat - lo.toNat) = (a.slice lo.toNat (hi.toNat - lo.toNat)).reverse ∧
    ∀ x, (x < lo.toNat ∨ hi.toNat ≤ x) → (reverseRange lo hi a hsz hhi hlo).1.at' x = a.at' x := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro lo hi a hsz hhi hlo hm
  rw [reverseRange]
  dsimp only
  split
  · rename_i h
    have h : lo.toNat + 1 < hi.toNat := by have := UInt64.lt_iff_toNat_lt.mp h; u64
    have elo : (lo + 1).toNat = lo.toNat + 1 := by u64g
    have ehi : (hi - 1).toNat = hi.toNat - 1 := by u64g
    let A := (a.set lo (a.get (hi - 1) (by u64g)) (by u64g)).set (hi - 1) (a.get lo (by u64g)) (by u64g)
    have hA : A.size = a.size := by simp [A]
    obtain ⟨IH1, IH2⟩ := ih (hi.toNat - 1 - (lo.toNat + 1)) (by omega) (lo + 1) (hi - 1) A (by rw [hA]; exact hsz)
      (by rw [hA, ehi]; omega) (by rw [elo, ehi]; omega) (by rw [elo, ehi])
    simp only [castSize_val]
    -- the untouched middle, plus the two swapped ends
    have hmid : A.slice (lo.toNat + 1) (hi.toNat - 1 - (lo.toNat + 1)) = a.slice (lo.toNat + 1) (hi.toNat - 1 - (lo.toNat + 1)) := by
      show ((a.set lo _ _).set (hi - 1) _ _).slice _ _ = _
      rw [slice_set_of_not_mem _ _ _ _ _ _ (by omega), slice_set_of_not_mem _ _ _ _ _ _ (by omega)]
    have hAlo : A.at' lo.toNat = a.at' (hi.toNat - 1) := by
      show ((a.set lo _ _).set (hi - 1) _ _).at' _ = _
      rw [at'_set_ne _ _ _ _ _ (by omega), at'_set_self, get_eq_at', ehi]
    have hAhi : A.at' (hi.toNat - 1) = a.at' lo.toNat := by
      show ((a.set lo _ _).set (hi - 1) _ _).at' _ = _
      rw [at'_set_eq _ _ _ _ _ (by omega), get_eq_at']
    refine ⟨?_, fun x hx => ?_⟩
    · -- decompose [lo, hi) = [lo] ++ [lo+1, hi-1) ++ [hi-1] on both sides
      have eR : ∀ R : UInt64Array, R.slice lo.toNat (hi.toNat - lo.toNat) =
          R.at' lo.toNat :: (R.slice (lo.toNat + 1) (hi.toNat - 1 - (lo.toNat + 1)) ++ [R.at' (hi.toNat - 1)]) := by
        intro R
        rw [show hi.toNat - lo.toNat = (hi.toNat - 1 - (lo.toNat + 1) + 1) + 1 by omega, slice_cons, slice_succ,
          show lo.toNat + 1 + (hi.toNat - 1 - (lo.toNat + 1)) = hi.toNat - 1 by omega]
      rw [eR, eR a, IH2 lo.toNat (by omega), IH2 (hi.toNat - 1) (by omega), hAlo, hAhi]
      have eS : (reverseRange (lo + 1) (hi - 1) A (by rw [hA]; exact hsz) (by rw [hA, ehi]; omega) (by rw [elo, ehi]; omega)).1.slice
          (lo.toNat + 1) (hi.toNat - 1 - (lo.toNat + 1)) =
          (reverseRange (lo + 1) (hi - 1) A (by rw [hA]; exact hsz) (by rw [hA, ehi]; omega) (by rw [elo, ehi]; omega)).1.slice
          (lo + 1).toNat ((hi - 1).toNat - (lo + 1).toNat) := by simp only [elo, ehi]
      rw [eS, IH1]
      simp only [elo, ehi, hmid]
      simp
    · rw [IH2 x (by omega)]
      show ((a.set lo _ _).set (hi - 1) _ _).at' x = _
      rw [at'_set_ne _ _ _ _ _ (by omega), at'_set_ne _ _ _ _ _ (by omega)]
  · rename_i h
    have h : ¬ 1 < (hi - lo).toNat := fun c => h (UInt64.lt_iff_toNat_lt.mpr (by simpa using c))
    have e : (hi - lo).toNat = hi.toNat - lo.toNat := by u64g
    refine ⟨?_, fun x _ => rfl⟩
    rcases Nat.lt_or_ge (hi.toNat - lo.toNat) 1 with h0 | h1
    · rw [show hi.toNat - lo.toNat = 0 by omega, slice_zero]; rfl
    · rw [show hi.toNat - lo.toNat = 1 by omega, slice_one]; rfl

/-- `isDescFrom` accepts exactly strictly descending ranges (given a descending prefix). -/
theorem isDescFrom_desc (n : UInt64) (a : UInt64Array) :
    ∀ (m : Nat) (i : UInt64) hsz hn hi, m = n.toNat - i.toNat →
    (a.slice 0 i.toNat).Pairwise (fun x y => y < x) → isDescFrom n i a hsz hn hi = true →
    (a.slice 0 n.toNat).Pairwise (fun x y => y < x) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro i hsz hn hi hm hs hb
  rw [isDescFrom] at hb
  split at hb
  · rename_i h
    have h : i.toNat < n.toNat := h
    have ei : (i + 1).toNat = i.toNat + 1 := by u64g
    have ei' : (i - 1).toNat = i.toNat - 1 := by u64g
    dsimp only at hb
    split at hb
    · rename_i hlt
      refine ih (n.toNat - (i + 1).toNat) (by omega) (i + 1) hsz hn (by omega) rfl ?_ hb
      rw [ei, slice_succ, Nat.zero_add]
      have hsplit : a.slice 0 i.toNat = a.slice 0 (i.toNat - 1) ++ [a.at' (i.toNat - 1)] := by
        rw [show i.toNat = (i.toNat - 1) + 1 by omega, slice_succ, Nat.zero_add,
          show i.toNat - 1 + 1 - 1 = i.toNat - 1 by omega]
      have hlt' : a.at' i.toNat < a.at' (i.toNat - 1) := by simpa [get_eq_at', ei'] using hlt
      rw [List.pairwise_append]
      refine ⟨hs, List.pairwise_singleton _ _, fun z hz y hy => ?_⟩
      simp at hy; subst hy
      rw [hsplit] at hz hs
      rcases List.mem_append.mp hz with hz | hz
      · have := (List.pairwise_append.mp hs).2.2 z hz _ (List.mem_singleton.mpr rfl)
        exact UInt64.lt_trans hlt' this
      · simp at hz; subst hz; exact hlt'
    · simp at hb
  · rename_i h
    have h : ¬ i.toNat < n.toNat := h
    rw [show n.toNat = i.toNat by omega]
    exact hs

/-- Sorted input: return it. Strictly descending input: reverse it in place. Otherwise sort. -/
def sortAdaptive2 (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : UInt64Array :=
  let n : UInt64 := xs.size.toUInt64
  have hn : n.toNat = xs.size := by simp [n]; omega
  if h : 1 < n then
    have h : 1 < n.toNat := h
    if isSortedFrom n 1 xs then xs
    else if isDescFrom n 1 xs then (reverseRange 0 n xs).1
    else sortBlocked xs hsz
  else xs

/-- The adaptive sort produces a sorted list. -/
theorem sortAdaptive2_sorted (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : Sorted le64 (sortAdaptive2 xs hsz).data.toList := by
  rw [sortAdaptive2]
  have hn : (xs.size.toUInt64).toNat = xs.size := by simp; omega
  dsimp only
  split
  · rename_i h
    have h : 1 < (xs.size.toUInt64).toNat := h
    split
    · rename_i hb
      have := isSortedFrom_sorted xs.size.toUInt64 xs _ 1 (by omega) (by omega) (by u64g) rfl
        (by simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, slice_one]; simp [Sorted]) hb
      rw [hn, slice_eq_toList] at this
      exact this
    · split
      · rename_i hb
        have hd := isDescFrom_desc xs.size.toUInt64 xs _ 1 (by omega) (by omega) (by u64g) rfl
          (by simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, slice_one]; simp) hb
        obtain ⟨R1, _⟩ := reverseRange_spec ((xs.size.toUInt64).toNat - (0 : UInt64).toNat) 0 xs.size.toUInt64 xs (by omega)
          (by omega) (by u64g) rfl
        simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.sub_zero] at R1
        have hs' : (reverseRange 0 xs.size.toUInt64 xs (by omega) (by omega) (by u64g)).1.size = (xs.size.toUInt64).toNat := by
          rw [(reverseRange _ _ _ _ _ _).2, hn]
        rw [← slice_eq_toList, hs', R1, Sorted, List.pairwise_reverse]
        exact hd.imp fun hxy => by simpa using UInt64.le_of_lt hxy
      · exact sortBlocked_sorted xs hsz
  · rename_i h
    have h : ¬ 1 < (xs.size.toUInt64).toNat := h
    rw [← slice_eq_toList]
    exact sorted_of_length_le_one _ (by simp; omega)

/-- The adaptive sort produces a permutation of its input. -/
theorem sortAdaptive2_perm (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : (sortAdaptive2 xs hsz).data.toList.Perm xs.data.toList := by
  rw [sortAdaptive2]
  have hn : (xs.size.toUInt64).toNat = xs.size := by simp; omega
  dsimp only
  split
  · split
    · exact List.Perm.refl _
    · split
      · obtain ⟨R1, _⟩ := reverseRange_spec ((xs.size.toUInt64).toNat - (0 : UInt64).toNat) 0 xs.size.toUInt64 xs (by omega)
          (by omega) (by u64g) rfl
        simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.sub_zero] at R1
        have hs' : (reverseRange 0 xs.size.toUInt64 xs (by omega) (by omega) (by u64g)).1.size = (xs.size.toUInt64).toNat := by
          rw [(reverseRange _ _ _ _ _ _).2, hn]
        have exs : xs.slice 0 (xs.size.toUInt64).toNat = xs.data.toList := by rw [hn, slice_eq_toList]
        rw [← slice_eq_toList, hs', R1, ← exs]
        exact List.reverse_perm _
      · exact sortBlocked_perm xs hsz
  · exact List.Perm.refl _

end MergeSort.BottomUp

namespace MergeSort.BottomUp
open UInt64Array MergeSort.Fast

/-- One scan deciding both "already sorted" and "strictly descending"; stops early once neither can hold. -/
def scanFrom (n i : UInt64) (a : UInt64Array) (asc desc : Bool)
    (hsz : a.size < 2 ^ 64 := by u64) (hn : n.toNat ≤ a.size := by u64)
    (hi : 1 ≤ i.toNat ∧ i.toNat ≤ n.toNat := by u64) : Bool × Bool :=
  if h : i < n ∧ (asc || desc) then
    have h : i.toNat < n.toNat := h.1
    let x := a.get (i - 1)
    let y := a.get i
    scanFrom n (i + 1) a (asc && decide (x ≤ y)) (desc && decide (y < x))
  else (asc, desc)
termination_by n.toNat - i.toNat
decreasing_by u64

theorem scanFrom_spec (n : UInt64) (a : UInt64Array) :
    ∀ (m : Nat) (i : UInt64) (asc desc : Bool) hsz hn hi, m = n.toNat - i.toNat →
    (asc = true → Sorted le64 (a.slice 0 i.toNat)) →
    (desc = true → (a.slice 0 i.toNat).Pairwise (fun x y => y < x)) →
    ((scanFrom n i a asc desc hsz hn hi).1 = true → Sorted le64 (a.slice 0 n.toNat)) ∧
    ((scanFrom n i a asc desc hsz hn hi).2 = true → (a.slice 0 n.toNat).Pairwise (fun x y => y < x)) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro i asc desc hsz hn hi hm hs hd
  rw [scanFrom]
  split
  · rename_i h
    have h' : i.toNat < n.toNat := h.1
    have ei : (i + 1).toNat = i.toNat + 1 := by u64g
    have ei' : (i - 1).toNat = i.toNat - 1 := by u64g
    dsimp only
    have hsplit : a.slice 0 i.toNat = a.slice 0 (i.toNat - 1) ++ [a.at' (i.toNat - 1)] := by
      rw [show i.toNat = (i.toNat - 1) + 1 by omega, slice_succ, Nat.zero_add,
        show i.toNat - 1 + 1 - 1 = i.toNat - 1 by omega]
    refine ih (n.toNat - (i + 1).toNat) (by omega) (i + 1) _ _ hsz hn (by omega) rfl ?_ ?_
    · intro hb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      have hs := hs hb.1
      have hle' : a.at' (i.toNat - 1) ≤ a.at' i.toNat := by simpa [get_eq_at', ei'] using hb.2
      rw [ei, slice_succ, Nat.zero_add, Sorted, List.pairwise_append]
      refine ⟨hs, List.pairwise_singleton _ _, fun z hz y hy => ?_⟩
      simp at hy; subst hy
      rw [hsplit] at hz hs
      rcases List.mem_append.mp hz with hz | hz
      · simpa using UInt64.le_trans (sorted_last_le _ _ hs z hz) hle'
      · simp at hz; subst hz; simpa using hle'
    · intro hb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      have hd := hd hb.1
      have hlt' : a.at' i.toNat < a.at' (i.toNat - 1) := by simpa [get_eq_at', ei'] using hb.2
      rw [ei, slice_succ, Nat.zero_add, List.pairwise_append]
      refine ⟨hd, List.pairwise_singleton _ _, fun z hz y hy => ?_⟩
      simp at hy; subst hy
      rw [hsplit] at hz hd
      rcases List.mem_append.mp hz with hz | hz
      · exact UInt64.lt_trans hlt' ((List.pairwise_append.mp hd).2.2 z hz _ (List.mem_singleton.mpr rfl))
      · simp at hz; subst hz; exact hlt'
  · rename_i h
    have h : ¬ (i.toNat < n.toNat ∧ (asc || desc) = true) := fun c => h ⟨UInt64.lt_iff_toNat_lt.mpr c.1, c.2⟩
    dsimp only
    refine ⟨fun ha => ?_, fun hdd => ?_⟩
    · have : ¬ i.toNat < n.toNat := fun c => h ⟨c, by simp [ha]⟩
      rw [show n.toNat = i.toNat by omega]; exact hs ha
    · have : ¬ i.toNat < n.toNat := fun c => h ⟨c, by simp [hdd]⟩
      rw [show n.toNat = i.toNat by omega]; exact hd hdd

/-- Single-scan adaptive sort: sorted input is returned, strictly descending input is reversed. -/
def sortAdaptive3 (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : UInt64Array :=
  let n : UInt64 := xs.size.toUInt64
  have hn : n.toNat = xs.size := by simp [n]; omega
  if h : 1 < n then
    have h : 1 < n.toNat := h
    let r := scanFrom n 1 xs true true
    if r.1 then xs
    else if r.2 then (reverseRange 0 n xs).1
    else sortBlocked xs hsz
  else xs

/-- The single-scan adaptive sort produces a sorted list. -/
theorem sortAdaptive3_sorted (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : Sorted le64 (sortAdaptive3 xs hsz).data.toList := by
  rw [sortAdaptive3]
  have hn : (xs.size.toUInt64).toNat = xs.size := by simp; omega
  dsimp only
  split
  · rename_i h
    have h : 1 < (xs.size.toUInt64).toNat := h
    obtain ⟨S1, D1⟩ := scanFrom_spec xs.size.toUInt64 xs _ 1 true true (by omega) (by omega) (by u64g) rfl
      (fun _ => by simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, slice_one]; simp [Sorted])
      (fun _ => by simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, slice_one]; simp)
    split
    · rename_i hb
      have := S1 hb
      rw [hn, slice_eq_toList] at this
      exact this
    · split
      · rename_i hb
        have hd := D1 hb
        obtain ⟨R1, _⟩ := reverseRange_spec ((xs.size.toUInt64).toNat - (0 : UInt64).toNat) 0 xs.size.toUInt64 xs (by omega)
          (by omega) (by u64g) rfl
        simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.sub_zero] at R1
        have hs' : (reverseRange 0 xs.size.toUInt64 xs (by omega) (by omega) (by u64g)).1.size = (xs.size.toUInt64).toNat := by
          rw [(reverseRange _ _ _ _ _ _).2, hn]
        rw [← slice_eq_toList, hs', R1, Sorted, List.pairwise_reverse]
        exact hd.imp fun hxy => by simpa using UInt64.le_of_lt hxy
      · exact sortBlocked_sorted xs hsz
  · rename_i h
    have h : ¬ 1 < (xs.size.toUInt64).toNat := h
    rw [← slice_eq_toList]
    exact sorted_of_length_le_one _ (by simp; omega)

/-- The single-scan adaptive sort produces a permutation of its input. -/
theorem sortAdaptive3_perm (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : (sortAdaptive3 xs hsz).data.toList.Perm xs.data.toList := by
  rw [sortAdaptive3]
  have hn : (xs.size.toUInt64).toNat = xs.size := by simp; omega
  dsimp only
  split
  · split
    · exact List.Perm.refl _
    · split
      · obtain ⟨R1, _⟩ := reverseRange_spec ((xs.size.toUInt64).toNat - (0 : UInt64).toNat) 0 xs.size.toUInt64 xs (by omega)
          (by omega) (by u64g) rfl
        simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.sub_zero] at R1
        have hs' : (reverseRange 0 xs.size.toUInt64 xs (by omega) (by omega) (by u64g)).1.size = (xs.size.toUInt64).toNat := by
          rw [(reverseRange _ _ _ _ _ _).2, hn]
        have exs : xs.slice 0 (xs.size.toUInt64).toNat = xs.data.toList := by rw [hn, slice_eq_toList]
        rw [← slice_eq_toList, hs', R1, ← exs]
        exact List.reverse_perm _
      · exact sortBlocked_perm xs hsz
  · exact List.Perm.refl _

end MergeSort.BottomUp
