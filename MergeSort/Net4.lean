import MergeSort.Runs
/-!
# Part 3 building block: a verified 4-element sorting network

Five compare-exchanges (`(0,1) (2,3) (0,2) (1,3) (1,2)`), each a pair of branchless selects.
The proof is a case analysis on the five comparisons, closed by `omega`.
-/
namespace MergeSort.BottomUp
open MergeSort.Fast

/-- Branchless selects: the C compiler compiles both `if`s into conditional moves. -/
@[inline] def mn (a b : UInt64) : UInt64 := if a ≤ b then a else b
@[inline] def mx (a b : UInt64) : UInt64 := if a ≤ b then b else a

/-- The 5-comparator network on four values, as a list. -/
def net4 (a b c d : UInt64) : List UInt64 :=
  let a1 := mn a b
  let b1 := mx a b
  let c1 := mn c d
  let d1 := mx c d
  let a2 := mn a1 c1
  let c2 := mx a1 c1
  let b2 := mn b1 d1
  let d2 := mx b1 d1
  let b3 := mn c2 b2
  let c3 := mx c2 b2
  [a2, b3, c3, d2]

theorem net4_sorted (a b c d : UInt64) : Sorted le64 (net4 a b c d) := by
  unfold net4 mn mx
  simp only [Sorted, le64, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    List.Pairwise.nil, decide_eq_true_eq, forall_eq_or_imp, forall_eq, and_true, or_false]
  repeat' split
  all_goals (simp only [UInt64.le_iff_toNat_le, Nat.not_le, false_implies, implies_true, and_true] at *; omega)

theorem net4_perm (a b c d : UInt64) : (net4 a b c d).Perm [a, b, c, d] := by
  unfold net4 mn mx
  dsimp only
  repeat' split
  all_goals first
    | exact List.Perm.refl _
    | (apply List.perm_iff_count.mpr; intro x
       simp only [UInt64.le_iff_toNat_le, Nat.not_le] at *
       simp only [List.count_cons, List.count_nil, beq_iff_eq]; omega)

end MergeSort.BottomUp
