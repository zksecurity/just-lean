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

namespace MergeSort.BottomUp
open UInt64Array MergeSort.Fast

/-- Sort `a[lo], a[lo+1], a[lo+2], a[lo+3]` in place with the network (straight-line, branchless). -/
def sort4 (lo : UInt64) (a : UInt64Array) (hsz : a.size < 2 ^ 64 := by u64)
    (h : lo.toNat + 4 ≤ a.size := by u64) : { b : UInt64Array // b.size = a.size } :=
  have e1 : (lo + 1).toNat = lo.toNat + 1 := by u64
  have e2 : (lo + 2).toNat = lo.toNat + 2 := by u64
  have e3 : (lo + 3).toNat = lo.toNat + 3 := by u64
  let x0 := a.get lo
  let x1 := a.get (lo + 1)
  let x2 := a.get (lo + 2)
  let x3 := a.get (lo + 3)
  let a1 := mn x0 x1
  let b1 := mx x0 x1
  let c1 := mn x2 x3
  let d1 := mx x2 x3
  let a2 := mn a1 c1
  let c2 := mx a1 c1
  let b2 := mn b1 d1
  let d2 := mx b1 d1
  let b3 := mn c2 b2
  let c3 := mx c2 b2
  ⟨(((a.set lo a2).set (lo + 1) b3 (by simp; omega)).set (lo + 2) c3 (by simp; omega)).set (lo + 3) d2 (by simp; omega),
    by simp⟩

theorem sort4_spec (lo : UInt64) (a : UInt64Array) hsz h :
    (sort4 lo a hsz h).1.slice lo.toNat 4 =
      net4 (a.at' lo.toNat) (a.at' (lo.toNat + 1)) (a.at' (lo.toNat + 2)) (a.at' (lo.toNat + 3)) ∧
    ∀ x, (x < lo.toNat ∨ lo.toNat + 4 ≤ x) → (sort4 lo a hsz h).1.at' x = a.at' x := by
  have e1 : (lo + 1).toNat = lo.toNat + 1 := by u64g
  have e2 : (lo + 2).toNat = lo.toNat + 2 := by u64g
  have e3 : (lo + 3).toNat = lo.toNat + 3 := by u64g
  unfold sort4 net4
  dsimp only
  refine ⟨?_, fun x hx => ?_⟩
  · simp only [show (4 : Nat) = 0 + 1 + 1 + 1 + 1 from rfl, slice_succ, slice_zero, List.nil_append,
      Nat.add_zero, at'_set, e1, e2, e3, get_eq_at']
    simp
  · simp only [at'_set, e1, e2, e3]
    have h0 : lo.toNat ≠ x := by omega
    have h1 : lo.toNat + 1 ≠ x := by omega
    have h2 : lo.toNat + 2 ≠ x := by omega
    have h3 : lo.toNat + 3 ≠ x := by omega
    simp [h0, h1, h2, h3]

end MergeSort.BottomUp
