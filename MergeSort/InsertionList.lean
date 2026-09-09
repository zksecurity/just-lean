import MergeSort.Runs
/-! List-level insertion sort: ordered insert, its sortedness and permutation properties. -/
namespace MergeSort.BottomUp
open MergeSort.Fast

/-- Insert `x` into a sorted list, after all elements `≤ x` (stable). -/
def insertSorted (x : UInt64) : List UInt64 → List UInt64
  | [] => [x]
  | y :: l => if x < y then x :: y :: l else y :: insertSorted x l

theorem insertSorted_perm (x : UInt64) (l : List UInt64) : (insertSorted x l).Perm (x :: l) := by
  induction l with
  | nil => simp [insertSorted]
  | cons y l ih =>
    simp only [insertSorted]
    split
    · exact List.Perm.refl _
    · exact (ih.cons y).trans (List.Perm.swap x y l)

theorem mem_insertSorted {a x : UInt64} {l : List UInt64} : a ∈ insertSorted x l ↔ a = x ∨ a ∈ l := by
  rw [(insertSorted_perm x l).mem_iff, List.mem_cons]

theorem insertSorted_sorted (x : UInt64) (l : List UInt64) (hl : Sorted le64 l) : Sorted le64 (insertSorted x l) := by
  induction l with
  | nil => simp [insertSorted, Sorted]
  | cons y l ih =>
    simp only [insertSorted]
    have hy := List.pairwise_cons.mp hl
    split
    · rename_i hxy
      refine List.pairwise_cons.mpr ⟨?_, hl⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · simpa using UInt64.le_of_lt hxy
      · simpa using UInt64.le_trans (UInt64.le_of_lt hxy) (by simpa using hy.1 b hb)
    · rename_i hxy
      have hyx : y ≤ x := by simpa using UInt64.not_lt.mp hxy
      refine List.pairwise_cons.mpr ⟨?_, ih hy.2⟩
      intro b hb
      rcases mem_insertSorted.mp hb with rfl | hb
      · simpa using hyx
      · exact hy.1 b hb

end MergeSort.BottomUp
