import MergeSort.Adaptive
import MergeSort.SmallRunsCorrect
/-!
# Part 3 building block: natural-run detection, verified

`findRun lo n a` returns the end `hi` of the maximal ascending or strictly descending run that starts
at `lo` (a descending run is reversed in place), so that `a[lo, hi)` is sorted afterwards.
-/
namespace MergeSort.BottomUp
open UInt64Array MergeSort.Fast

/-- End of the ascending run: `[lo, i)` is already known to be sorted, scan on from `i`. -/
def ascEnd (n i : UInt64) (a : UInt64Array) (hsz : a.size < 2 ^ 64 := by u64) (hn : n.toNat ≤ a.size := by u64)
    (hi : 1 ≤ i.toNat ∧ i.toNat ≤ n.toNat := by u64) : { r : UInt64 // i.toNat ≤ r.toNat ∧ r.toNat ≤ n.toNat } :=
  if h : i < n then
    have h : i.toNat < n.toNat := h
    have ei : (i + 1).toNat = i.toNat + 1 := by u64
    if a.get (i - 1) ≤ a.get i then
      let ⟨r, hr⟩ := ascEnd n (i + 1) a
      ⟨r, by omega⟩
    else ⟨i, by omega⟩
  else ⟨i, by omega⟩
termination_by n.toNat - i.toNat
decreasing_by u64

/-- End of the strictly descending run. -/
def descEnd (n i : UInt64) (a : UInt64Array) (hsz : a.size < 2 ^ 64 := by u64) (hn : n.toNat ≤ a.size := by u64)
    (hi : 1 ≤ i.toNat ∧ i.toNat ≤ n.toNat := by u64) : { r : UInt64 // i.toNat ≤ r.toNat ∧ r.toNat ≤ n.toNat } :=
  if h : i < n then
    have h : i.toNat < n.toNat := h
    have ei : (i + 1).toNat = i.toNat + 1 := by u64
    if a.get i < a.get (i - 1) then
      let ⟨r, hr⟩ := descEnd n (i + 1) a
      ⟨r, by omega⟩
    else ⟨i, by omega⟩
  else ⟨i, by omega⟩
termination_by n.toNat - i.toNat
decreasing_by u64

theorem ascEnd_spec (n lo : UInt64) (a : UInt64Array) :
    ∀ (m : Nat) (i : UInt64) hsz hn hi, m = n.toNat - i.toNat → lo.toNat < i.toNat →
    Sorted (a.slice lo.toNat (i.toNat - lo.toNat)) →
    Sorted (a.slice lo.toNat ((ascEnd n i a hsz hn hi).1.toNat - lo.toNat)) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro i hsz hn hi hm hlo hs
  rw [ascEnd]
  split
  · rename_i h
    have h : i.toNat < n.toNat := h
    have ei : (i + 1).toNat = i.toNat + 1 := by u64g
    have ei' : (i - 1).toNat = i.toNat - 1 := by u64g
    dsimp only
    split
    · rename_i hle
      have hsplit : a.slice lo.toNat (i.toNat - lo.toNat) = a.slice lo.toNat (i.toNat - 1 - lo.toNat) ++ [a.at' (i.toNat - 1)] := by
        rw [show i.toNat - lo.toNat = (i.toNat - 1 - lo.toNat) + 1 by omega, slice_succ,
          show lo.toNat + (i.toNat - 1 - lo.toNat) = i.toNat - 1 by omega]
      refine ih (n.toNat - (i + 1).toNat) (by omega) (i + 1) hsz hn (by omega) rfl (by omega) ?_
      have hle' : a.at' (i.toNat - 1) ≤ a.at' i.toNat := by simpa [get_eq_at', ei'] using hle
      rw [ei, show i.toNat + 1 - lo.toNat = (i.toNat - lo.toNat) + 1 by omega, slice_succ,
        show lo.toNat + (i.toNat - lo.toNat) = i.toNat by omega, Sorted, List.pairwise_append]
      refine ⟨hs, List.pairwise_singleton _ _, fun z hz y hy => ?_⟩
      simp at hy; subst hy
      rw [hsplit] at hz hs
      rcases List.mem_append.mp hz with hz | hz
      · simpa using UInt64.le_trans (sorted_last_le _ _ hs z hz) hle'
      · simp at hz; subst hz; simpa using hle'
    · exact hs
  · exact hs

theorem descEnd_spec (n lo : UInt64) (a : UInt64Array) :
    ∀ (m : Nat) (i : UInt64) hsz hn hi, m = n.toNat - i.toNat → lo.toNat < i.toNat →
    (a.slice lo.toNat (i.toNat - lo.toNat)).Pairwise (fun x y => y < x) →
    (a.slice lo.toNat ((descEnd n i a hsz hn hi).1.toNat - lo.toNat)).Pairwise (fun x y => y < x) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro i hsz hn hi hm hlo hd
  rw [descEnd]
  split
  · rename_i h
    have h : i.toNat < n.toNat := h
    have ei : (i + 1).toNat = i.toNat + 1 := by u64g
    have ei' : (i - 1).toNat = i.toNat - 1 := by u64g
    dsimp only
    split
    · rename_i hlt
      have hsplit : a.slice lo.toNat (i.toNat - lo.toNat) = a.slice lo.toNat (i.toNat - 1 - lo.toNat) ++ [a.at' (i.toNat - 1)] := by
        rw [show i.toNat - lo.toNat = (i.toNat - 1 - lo.toNat) + 1 by omega, slice_succ,
          show lo.toNat + (i.toNat - 1 - lo.toNat) = i.toNat - 1 by omega]
      refine ih (n.toNat - (i + 1).toNat) (by omega) (i + 1) hsz hn (by omega) rfl (by omega) ?_
      have hlt' : a.at' i.toNat < a.at' (i.toNat - 1) := by simpa [get_eq_at', ei'] using hlt
      rw [ei, show i.toNat + 1 - lo.toNat = (i.toNat - lo.toNat) + 1 by omega, slice_succ,
        show lo.toNat + (i.toNat - lo.toNat) = i.toNat by omega, List.pairwise_append]
      refine ⟨hd, List.pairwise_singleton _ _, fun z hz y hy => ?_⟩
      simp at hy; subst hy
      rw [hsplit] at hz hd
      rcases List.mem_append.mp hz with hz | hz
      · exact UInt64.lt_trans hlt' ((List.pairwise_append.mp hd).2.2 z hz _ (List.mem_singleton.mpr rfl))
      · simp at hz; subst hz; exact hlt'
    · exact hd
  · exact hd

/-- The maximal run starting at `lo` (`lo < n`): returns its end and the array with a descending run
    reversed in place. -/
def findRun (lo n : UInt64) (a : UInt64Array) (hsz : a.size < 2 ^ 64 := by u64) (hn : n.toNat ≤ a.size := by u64)
    (hlo : lo.toNat < n.toNat := by u64) :
    { p : UInt64 × UInt64Array // lo.toNat < p.1.toNat ∧ p.1.toNat ≤ n.toNat ∧ p.2.size = a.size } :=
  have e1 : (lo + 1).toNat = lo.toNat + 1 := by u64
  if h : lo + 1 < n then
    have h : lo.toNat + 1 < n.toNat := by have := UInt64.lt_iff_toNat_lt.mp h; omega
    have e2 : (lo + 2).toNat = lo.toNat + 2 := by u64
    if a.get (lo + 1) < a.get lo then
      let ⟨r, hr⟩ := descEnd n (lo + 2) a
      let ⟨b, hb⟩ := reverseRange lo r a (hhi := by omega) (hlo := by omega)
      ⟨(r, b), by show lo.toNat < r.toNat; omega, by show r.toNat ≤ n.toNat; omega, hb⟩
    else
      let ⟨r, hr⟩ := ascEnd n (lo + 2) a
      ⟨(r, a), by show lo.toNat < r.toNat; omega, by show r.toNat ≤ n.toNat; omega, rfl⟩
  else ⟨(lo + 1, a), by show lo.toNat < (lo + 1).toNat; omega, by show (lo + 1).toNat ≤ n.toNat; omega, rfl⟩

theorem findRun_spec (lo n : UInt64) (a : UInt64Array) hsz hn hlo :
    Sorted ((findRun lo n a hsz hn hlo).1.2.slice lo.toNat ((findRun lo n a hsz hn hlo).1.1.toNat - lo.toNat)) ∧
    ((findRun lo n a hsz hn hlo).1.2.slice lo.toNat ((findRun lo n a hsz hn hlo).1.1.toNat - lo.toNat)).Perm
      (a.slice lo.toNat ((findRun lo n a hsz hn hlo).1.1.toNat - lo.toNat)) ∧
    ∀ x, (x < lo.toNat ∨ (findRun lo n a hsz hn hlo).1.1.toNat ≤ x) → (findRun lo n a hsz hn hlo).1.2.at' x = a.at' x := by
  rw [findRun]
  have e1 : (lo + 1).toNat = lo.toNat + 1 := by u64g
  dsimp only
  split
  · rename_i h
    have h : lo.toNat + 1 < n.toNat := by have := UInt64.lt_iff_toNat_lt.mp h; omega
    have e2 : (lo + 2).toNat = lo.toNat + 2 := by u64g
    have two : a.slice lo.toNat ((lo + 2).toNat - lo.toNat) = [a.at' lo.toNat, a.at' (lo.toNat + 1)] := by
      rw [e2, show lo.toNat + 2 - lo.toNat = 1 + 1 by omega, slice_succ, slice_one]; rfl
    split
    · rename_i hlt
      have hlt' : a.at' (lo.toNat + 1) < a.at' lo.toNat := by simpa [get_eq_at', e1] using hlt
      have D := descEnd_spec n lo a _ (lo + 2) hsz hn (by omega) rfl (by omega) (by rw [two]; simp [hlt'])
      have hD := (descEnd n (lo + 2) a hsz hn (by omega)).2
      dsimp only
      obtain ⟨R1, R2⟩ := reverseRange_spec ((descEnd n (lo + 2) a hsz hn (by omega)).1.toNat - lo.toNat) lo _ a hsz (by omega) (by omega) rfl
      refine ⟨?_, ?_, fun x hx => R2 x hx⟩
      · rw [R1, Sorted, List.pairwise_reverse]
        exact D.imp fun hxy => by simpa using UInt64.le_of_lt hxy
      · rw [R1]; exact List.reverse_perm _
    · rename_i hge
      have hle' : a.at' lo.toNat ≤ a.at' (lo.toNat + 1) := by
        have := UInt64.not_lt.mp hge; simpa [get_eq_at', e1] using this
      have A := ascEnd_spec n lo a _ (lo + 2) hsz hn (by omega) rfl (by omega) (by rw [two]; simp [Sorted, hle'])
      exact ⟨A, List.Perm.refl _, fun _ _ => rfl⟩
  · refine ⟨?_, List.Perm.refl _, fun _ _ => rfl⟩
    rw [e1, Nat.add_sub_cancel_left, slice_one]; simp [Sorted]

end MergeSort.BottomUp
