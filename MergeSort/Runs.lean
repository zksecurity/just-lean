import MergeSort.Correct
/-! List-level theory of one bottom-up pass: merging adjacent runs of length `w`. -/
namespace MergeSort.BottomUp
open MergeSort.Fast

/-- Merge adjacent runs of length `w` (the last pair may be shorter). -/
def mergeRuns (w : Nat) (hw : 0 < w) (l : List UInt64) : List UInt64 :=
  if _h : l.length ≤ w then l
  else merge (l.take w) ((l.drop w).take w) ++ mergeRuns w hw (l.drop (2 * w))
termination_by l.length
decreasing_by simp; omega

/-- Every run of length `w` is sorted (the last one may be shorter). -/
def ChunkSorted (w : Nat) (hw : 0 < w) (l : List UInt64) : Prop :=
  if _h : l.length ≤ w then Sorted l
  else Sorted (l.take w) ∧ ChunkSorted w hw (l.drop w)
termination_by l.length
decreasing_by simp; omega

theorem mergeRuns_of_length_le {w : Nat} (hw) (l : List UInt64) (h : l.length ≤ w) : mergeRuns w hw l = l := by
  rw [mergeRuns, dif_pos h]

theorem mergeRuns_of_lt {w : Nat} (hw) (l : List UInt64) (h : ¬ l.length ≤ w) :
    mergeRuns w hw l = merge (l.take w) ((l.drop w).take w) ++ mergeRuns w hw (l.drop (2 * w)) := by
  rw [mergeRuns, dif_neg h]

theorem chunkSorted_of_length_le {w : Nat} (hw) {l : List UInt64} (h : l.length ≤ w) :
    ChunkSorted w hw l ↔ Sorted l := by
  rw [ChunkSorted, dif_pos h]

theorem chunkSorted_of_lt {w : Nat} (hw) {l : List UInt64} (h : ¬ l.length ≤ w) :
    ChunkSorted w hw l ↔ Sorted (l.take w) ∧ ChunkSorted w hw (l.drop w) := by
  rw [ChunkSorted, dif_neg h]

theorem sorted_of_length_le_one (l : List UInt64) (h : l.length ≤ 1) : Sorted l := by
  match l, h with
  | [], _ => simp [Sorted]
  | [x], _ => simp [Sorted]

theorem chunkSorted_one (l : List UInt64) : ChunkSorted 1 (by omega) l := by
  induction l with
  | nil => rw [chunkSorted_of_length_le _ (by simp)]; exact sorted_of_length_le_one _ (by simp)
  | cons x l ih =>
    by_cases h : (x :: l).length ≤ 1
    · rw [chunkSorted_of_length_le _ h]; exact sorted_of_length_le_one _ h
    · rw [chunkSorted_of_lt _ h]
      exact ⟨sorted_of_length_le_one _ (by simp), by simpa using ih⟩

theorem mergeRuns_perm {w : Nat} (hw) (l : List UInt64) : (mergeRuns w hw l).Perm l := by
  induction l using mergeRuns.induct w hw with
  | case1 l h => rw [mergeRuns_of_length_le hw l h]
  | case2 l h ih =>
    rw [mergeRuns_of_lt hw l h]
    have e : l.take w ++ ((l.drop w).take w ++ l.drop (2 * w)) = l := by
      rw [show 2 * w = w + w by omega, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
    calc (merge (l.take w) ((l.drop w).take w) ++ mergeRuns w hw (l.drop (2 * w))).Perm
          ((l.take w ++ (l.drop w).take w) ++ l.drop (2 * w)) := (merge_perm _ _).append ih
      _ = l := by rw [List.append_assoc, e]

theorem le64_trans : ∀ a b c : UInt64, a ≤ b → b ≤ c → a ≤ c := fun _ _ _ => UInt64.le_trans
theorem le64_total : ∀ a b : UInt64, a ≤ b ∨ b ≤ a := UInt64.le_total

/-- A pass turns `w`-sorted runs into `2w`-sorted runs. -/
theorem chunkSorted_mergeRuns {w : Nat} (hw : 0 < w) (l : List UInt64) (hl : ChunkSorted w hw l) :
    ChunkSorted (2 * w) (by omega) (mergeRuns w hw l) := by
  induction l using mergeRuns.induct w hw with
  | case1 l h =>
    rw [mergeRuns_of_length_le hw l h, chunkSorted_of_length_le _ (by omega)]
    exact (chunkSorted_of_length_le hw h).mp hl
  | case2 l h ih =>
    rw [mergeRuns_of_lt hw l h]
    obtain ⟨hA, hrest⟩ := (chunkSorted_of_lt hw h).mp hl
    -- the second run is sorted, and the remainder is `w`-sorted
    have hB : Sorted ((l.drop w).take w) ∧ ChunkSorted w hw (l.drop (2 * w)) := by
      by_cases h2 : (l.drop w).length ≤ w
      · rw [chunkSorted_of_length_le hw h2] at hrest
        refine ⟨by rwa [List.take_of_length_le h2], ?_⟩
        have : l.drop (2 * w) = [] := List.drop_eq_nil_of_le (by simp at h2 ⊢; omega)
        rw [this, chunkSorted_of_length_le hw (by simp)]
        exact sorted_of_length_le_one _ (by simp)
      · rw [chunkSorted_of_lt hw h2] at hrest
        refine ⟨hrest.1, ?_⟩
        have : l.drop (2 * w) = (l.drop w).drop w := by rw [List.drop_drop]; congr 1; omega
        rw [this]; exact hrest.2
    have hAB : Sorted (merge (l.take w) ((l.drop w).take w)) := merge_sorted le64_trans le64_total hA hB.1
    have ihM := ih hB.2
    by_cases hlen : l.length ≤ 2 * w
    · -- the remainder is empty
      have hM : l.drop (2 * w) = [] := List.drop_eq_nil_of_le hlen
      rw [hM, mergeRuns_of_length_le hw [] (by simp), List.append_nil,
        chunkSorted_of_length_le _ (by rw [(merge_perm _ _).length_eq]; simp; omega)]
      exact hAB
    · have hlenAB : (merge (l.take w) ((l.drop w).take w)).length = 2 * w := by
        rw [(merge_perm _ _).length_eq]; simp; omega
      have hlenM : (mergeRuns w hw (l.drop (2 * w))).length = l.length - 2 * w := by
        rw [(mergeRuns_perm hw _).length_eq, List.length_drop]
      rw [chunkSorted_of_lt _ (by rw [List.length_append, hlenAB, hlenM]; omega)]
      rw [List.take_left' hlenAB, List.drop_left' hlenAB]
      exact ⟨hAB, ihM⟩

theorem sorted_of_chunkSorted {w : Nat} (hw) {l : List UInt64} (h : l.length ≤ w) (hl : ChunkSorted w hw l) :
    Sorted l := (chunkSorted_of_length_le hw h).mp hl

theorem chunkSorted_congr {w₁ w₂ : Nat} (h : w₁ = w₂) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) {l : List UInt64}
    (hl : ChunkSorted w₁ hw₁ l) : ChunkSorted w₂ hw₂ l := by subst h; exact hl

end MergeSort.BottomUp
