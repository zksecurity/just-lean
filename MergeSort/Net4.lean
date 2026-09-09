import MergeSort.Runs
import MergeSort.BidiSort
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

namespace MergeSort.BottomUp
open UInt64Array MergeSort.Fast

/-- `src.slice lo 4` spelled out. -/
theorem slice_four (a : UInt64Array) (lo : Nat) :
    a.slice lo 4 = [a.at' lo, a.at' (lo + 1), a.at' (lo + 2), a.at' (lo + 3)] := by
  simp only [show (4 : Nat) = 0 + 1 + 1 + 1 + 1 from rfl, slice_succ, slice_zero, List.nil_append, Nat.add_zero]
  rfl

/-- driftsort's `sort8_stable`: two 4-element networks in place, then one (bidirectional) merge of the
    two runs into `dst[lo, lo+8)`. -/
def sort8 (lo : UInt64) (src dst : UInt64Array) (hssz : src.size < 2 ^ 64 := by u64) (hdsz : dst.size < 2 ^ 64 := by u64)
    (hs : lo.toNat + 8 ≤ src.size := by u64) (hd : lo.toNat + 8 ≤ dst.size := by u64) :
    { b : UInt64Array // b.size = dst.size } :=
  have e4 : (lo + 4).toNat = lo.toNat + 4 := by u64
  have e8 : (lo + 8).toNat = lo.toNat + 8 := by u64
  let r1 := sort4 lo src
  let r2 := sort4 (lo + 4) r1.1 (by rw [r1.2]; exact hssz) (by rw [r1.2]; omega)
  mergeKernel lo (lo + 4) (lo + 8) r2.1 dst hdsz (by rw [r2.2, r1.2]; omega) (by omega) (by omega) (by omega)

theorem sort8_spec (lo : UInt64) (src dst : UInt64Array) hssz hdsz hs hd :
    Sorted le64 ((sort8 lo src dst hssz hdsz hs hd).1.slice lo.toNat 8) ∧
    ((sort8 lo src dst hssz hdsz hs hd).1.slice lo.toNat 8).Perm (src.slice lo.toNat 8) ∧
    ∀ x, (x < lo.toNat ∨ lo.toNat + 8 ≤ x) → (sort8 lo src dst hssz hdsz hs hd).1.at' x = dst.at' x := by
  have e4 : (lo + 4).toNat = lo.toNat + 4 := by u64g
  have e8 : (lo + 8).toNat = lo.toNat + 8 := by u64g
  unfold sort8
  dsimp only
  obtain ⟨A1, F1⟩ := sort4_spec lo src hssz (by omega)
  have h1 := (sort4 lo src hssz (by omega)).2
  obtain ⟨A2, F2⟩ := sort4_spec (lo + 4) (sort4 lo src hssz (by omega)).1 (by rw [h1]; exact hssz) (by rw [h1]; omega)
  have h2 := (sort4 (lo + 4) (sort4 lo src hssz (by omega)).1 (by rw [h1]; exact hssz) (by rw [h1]; omega)).2
  -- left run: untouched by the second network
  have L : (sort4 (lo + 4) (sort4 lo src hssz (by omega)).1 (by rw [h1]; exact hssz) (by rw [h1]; omega)).1.slice lo.toNat 4 =
      net4 (src.at' lo.toNat) (src.at' (lo.toNat + 1)) (src.at' (lo.toNat + 2)) (src.at' (lo.toNat + 3)) := by
    rw [← A1]; apply slice_congr; intro t ht; exact F2 _ (Or.inl (by omega))
  -- right run: the original elements, untouched by the first network
  have R : (sort4 (lo + 4) (sort4 lo src hssz (by omega)).1 (by rw [h1]; exact hssz) (by rw [h1]; omega)).1.slice (lo + 4).toNat 4 =
      net4 (src.at' (lo.toNat + 4)) (src.at' (lo.toNat + 4 + 1)) (src.at' (lo.toNat + 4 + 2)) (src.at' (lo.toNat + 4 + 3)) := by
    rw [A2, e4]; congr 1 <;> exact F1 _ (Or.inr (by omega))
  have hL : Sorted le64 ((sort4 (lo + 4) (sort4 lo src hssz (by omega)).1 (by rw [h1]; exact hssz) (by rw [h1]; omega)).1.slice lo.toNat 4) := by
    rw [L]; exact net4_sorted _ _ _ _
  have hR : Sorted le64 ((sort4 (lo + 4) (sort4 lo src hssz (by omega)).1 (by rw [h1]; exact hssz) (by rw [h1]; omega)).1.slice (lo + 4).toNat 4) := by
    rw [R]; exact net4_sorted _ _ _ _
  obtain ⟨M, FM⟩ := mergeKernel_spec lo (lo + 4) (lo + 8) _ dst hdsz (by rw [h2, h1]; omega) (by omega) (by omega) (by omega)
    (by rw [show (lo + 4).toNat - lo.toNat = 4 by omega]; exact hL)
    (by rw [show (lo + 8).toNat - (lo + 4).toNat = 4 by omega]; exact hR)
  rw [show (lo + 4).toNat - lo.toNat = 4 by omega, show (lo + 8).toNat - (lo + 4).toNat = 4 by omega,
    show (lo + 8).toNat - lo.toNat = 8 by omega] at M
  refine ⟨?_, ?_, fun x hx => FM x (by rcases hx with hx | hx; exact Or.inl hx; exact Or.inr (by omega))⟩
  · have S := merge_sorted le64 le64_trans le64_total hL hR
    rwa [← M] at S
  · have P : (merge le64 ((sort4 (lo + 4) (sort4 lo src hssz (by omega)).1 (by rw [h1]; exact hssz) (by rw [h1]; omega)).1.slice lo.toNat 4)
        ((sort4 (lo + 4) (sort4 lo src hssz (by omega)).1 (by rw [h1]; exact hssz) (by rw [h1]; omega)).1.slice (lo + 4).toNat 4)).Perm
        (src.slice lo.toNat 8) := by
      rw [show (8 : Nat) = 4 + 4 from rfl, slice_add src]
      refine (merge_perm le64 _ _).trans (List.Perm.append ?_ ?_)
      · rw [L, slice_four]; exact net4_perm _ _ _ _
      · rw [R, slice_four]; exact net4_perm _ _ _ _
    rwa [← M] at P

end MergeSort.BottomUp
