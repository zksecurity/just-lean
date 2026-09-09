import MergeSort.MergeBack
import MergeSort.BottomUpMerge
/-!
# Advanced trick: bidirectional branchless merge

For two runs of equal length `w`, merge from the front (smallest first, ties from the left run) and
from the back (largest first, ties from the right run) in one interleaved loop. Each direction
performs exactly `w` steps, so neither can run past its run and no bounds tests are needed in the
loop; the two dependency chains overlap in the CPU.
-/
namespace MergeSort.BottomUp
open UInt64Array MergeSort.Fast

/-- One interleaved front+back merge step, `cnt` steps remaining.
    Front: `i` in `L = src[lo, mid)`, `j` in `R = src[mid, hi)`, writes at `k`.
    Back (exclusive ends): reads `src[i' - 1]` and `src[j' - 1]`, writes at `k' - 1`. -/
def mergeBidi (mid hi i j k i' j' k' cnt : UInt64) (src dst : UInt64Array)
    (hsz : dst.size < 2 ^ 64 := by u64) (hs : hi.toNat ≤ src.size := by u64) (hd : hi.toNat ≤ dst.size := by u64)
    (hmid : mid.toNat ≤ hi.toNat := by u64)
    -- both runs still hold at least `cnt` unconsumed elements for each direction:
    (hi1 : i.toNat + cnt.toNat ≤ mid.toNat := by u64) (hj1 : j.toNat + cnt.toNat ≤ hi.toNat := by u64)
    (hi2 : cnt.toNat ≤ i'.toNat ∧ i'.toNat ≤ mid.toNat := by u64)
    (hj2 : mid.toNat + cnt.toNat ≤ j'.toNat ∧ j'.toNat ≤ hi.toNat := by u64)
    -- write positions: the front fills `[lo, mid)` upward, the back fills `[mid, hi)` downward
    (hk1 : k.toNat + cnt.toNat = mid.toNat := by u64) (hk2 : k'.toNat = mid.toNat + cnt.toNat := by u64) :
    { b : UInt64Array // b.size = dst.size } :=
  if hc : 0 < cnt then
    have hc' : (0 : UInt64).toNat < cnt.toNat := UInt64.lt_iff_toNat_lt.mp hc
    -- front step (ties: left)
    let x := src.get i
    let y := src.get j
    let takeL : Bool := decide (x ≤ y)
    let di : UInt64 := if takeL then 1 else 0
    have hdi : di.toNat ≤ 1 := by show (if takeL then (1 : UInt64) else 0).toNat ≤ 1; split <;> decide
    -- back step (ties: right)
    let x' := src.get (i' - 1)
    let y' := src.get (j' - 1)
    let takeR : Bool := decide (x' ≤ y')
    let dj : UInt64 := if takeR then 1 else 0
    have hdj : dj.toNat ≤ 1 := by show (if takeR then (1 : UInt64) else 0).toNat ≤ 1; split <;> decide
    Fast.castSize (mergeBidi mid hi (i + di) (j + (1 - di)) (k + 1) (i' - (1 - dj)) (j' - dj) (k' - 1) (cnt - 1) src
      ((dst.set k (if takeL then x else y)).set (k' - 1) (if takeR then y' else x'))) (by simp)
  else ⟨dst, rfl⟩
termination_by cnt.toNat
decreasing_by u64

/-! ## List-level unfolding of the two directions -/

theorem take_merge_cons_cons (n : Nat) (x y : UInt64) (xs ys : List UInt64) :
    (merge le64 (x :: xs) (y :: ys)).take (n + 1) =
      if x ≤ y then x :: (merge le64 xs (y :: ys)).take n else y :: (merge le64 (x :: xs) ys).take n := by
  rw [merge_cons_cons]; split <;> simp

theorem take_mergeBack_cons_cons (n : Nat) (x y : UInt64) (xs ys : List UInt64) :
    (mergeBack (x :: xs) (y :: ys)).take (n + 1) =
      if x ≤ y then y :: (mergeBack (x :: xs) ys).take n else x :: (mergeBack xs (y :: ys)).take n := by
  simp only [mergeBack]; split <;> simp

/-- A slice read backwards: the last element first. -/
theorem reverse_slice_succ (a : UInt64Array) (off len : Nat) :
    (a.slice off (len + 1)).reverse = a.at' (off + len) :: (a.slice off len).reverse := by
  rw [slice_succ, List.reverse_append]; rfl


/-- The two written regions after `cnt` more interleaved steps. -/
theorem mergeBidi_spec (mid hi : UInt64) (src : UInt64Array) (lo : Nat) :
    ∀ (m : Nat) (i j k i' j' k' cnt : UInt64) (dst : UInt64Array) hsz hs hd hmid hi1 hj1 hi2 hj2 hk1 hk2,
    m = cnt.toNat → lo ≤ k.toNat → lo + cnt.toNat ≤ i'.toNat →
    (mergeBidi mid hi i j k i' j' k' cnt src dst hsz hs hd hmid hi1 hj1 hi2 hj2 hk1 hk2).1.slice lo (mid.toNat - lo) =
      dst.slice lo (k.toNat - lo) ++
        (merge le64 (src.slice i.toNat (mid.toNat - i.toNat)) (src.slice j.toNat (hi.toNat - j.toNat))).take cnt.toNat ∧
    (mergeBidi mid hi i j k i' j' k' cnt src dst hsz hs hd hmid hi1 hj1 hi2 hj2 hk1 hk2).1.slice mid.toNat (hi.toNat - mid.toNat) =
      ((mergeBack (src.slice lo (i'.toNat - lo)).reverse (src.slice mid.toNat (j'.toNat - mid.toNat)).reverse).take cnt.toNat).reverse ++
        dst.slice k'.toNat (hi.toNat - k'.toNat) ∧
    ∀ x, (x < k.toNat ∨ k'.toNat ≤ x) →
      (mergeBidi mid hi i j k i' j' k' cnt src dst hsz hs hd hmid hi1 hj1 hi2 hj2 hk1 hk2).1.at' x = dst.at' x := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro i j k i' j' k' cnt dst hsz hs hd hmid hi1 hj1 hi2 hj2 hk1 hk2 hm hlo hlo'
  rw [mergeBidi]
  split
  · rename_i hc
    have hc : 0 < cnt.toNat := hc
    dsimp only
    -- name the step's ingredients (definitionally those in the goal)
    let TL : Bool := decide (src.get i (by u64g) ≤ src.get j (by u64g))
    let DI : UInt64 := if TL then 1 else 0
    let V : UInt64 := if TL then src.get i (by u64g) else src.get j (by u64g)
    let TR : Bool := decide (src.get (i' - 1) (by u64g) ≤ src.get (j' - 1) (by u64g))
    let DJ : UInt64 := if TR then 1 else 0
    let V' : UInt64 := if TR then src.get (j' - 1) (by u64g) else src.get (i' - 1) (by u64g)
    have hDI : DI.toNat ≤ 1 := by show (if TL then (1 : UInt64) else 0).toNat ≤ 1; split <;> decide
    have hDJ : DJ.toNat ≤ 1 := by show (if TR then (1 : UInt64) else 0).toNat ≤ 1; split <;> decide
    have ek : (k + 1).toNat = k.toNat + 1 := by u64g
    have ek' : (k' - 1).toNat = k'.toNat - 1 := by u64g
    have ec : (cnt - 1).toNat = cnt.toNat - 1 := by u64g
    have ei' : (i' - 1).toNat = i'.toNat - 1 := by u64g
    have ej' : (j' - 1).toNat = j'.toNat - 1 := by u64g
    have eDI : (i + DI).toNat = i.toNat + DI.toNat := by simp only [UInt64.toNat_add, Nat.reducePow]; omega
    have eDJ : (j + (1 - DI)).toNat = j.toNat + (1 - DI.toNat) := by
      simp only [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
    have eDI' : (i' - (1 - DJ)).toNat = i'.toNat - (1 - DJ.toNat) := by
      simp only [UInt64.toNat_sub, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
    have eDJ' : (j' - DJ).toNat = j'.toNat - DJ.toNat := by
      simp only [UInt64.toNat_sub, Nat.reducePow]; omega
    let D2 := (dst.set k V (by u64g)).set (k' - 1) V' (by u64g)
    obtain ⟨ih1, ih2, ih3⟩ := ih (cnt - 1).toNat (by omega) (i + DI) (j + (1 - DI)) (k + 1) (i' - (1 - DJ)) (j' - DJ) (k' - 1)
      (cnt - 1) D2 (by simp [D2]; exact hsz) hs (by simp [D2]; exact hd) hmid (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) rfl (by omega) (by omega)
    simp only [castSize_val]
    -- the two writes land at `k` (front) and `k' - 1` (back); the regions they extend
    have hfrontW : D2.slice lo (k.toNat + 1 - lo) = dst.slice lo (k.toNat - lo) ++ [V] := by
      show ((dst.set k V _).set (k' - 1) V' _).slice lo (k.toNat + 1 - lo) = _
      rw [slice_set_of_not_mem _ _ _ _ _ _ (by omega), show k.toNat + 1 - lo = (k.toNat - lo) + 1 by omega]
      exact slice_set_end _ _ _ _ _ _ (by omega)
    have hbackW : D2.slice (k'.toNat - 1) (hi.toNat - (k'.toNat - 1)) = V' :: dst.slice k'.toNat (hi.toNat - k'.toNat) := by
      show ((dst.set k V _).set (k' - 1) V' _).slice (k'.toNat - 1) (hi.toNat - (k'.toNat - 1)) = _
      rw [show hi.toNat - (k'.toNat - 1) = (hi.toNat - k'.toNat) + 1 by omega, slice_cons,
        show k'.toNat - 1 + 1 = k'.toNat by omega, slice_set_of_not_mem _ _ _ _ _ _ (by omega),
        slice_set_of_not_mem _ _ _ _ _ _ (by omega), at'_set_eq _ _ _ _ _ (by omega)]
    refine ⟨?_, ?_, fun x hx => ?_⟩
    · -- front region
      rw [ih1, ek, hfrontW, ec]
      have hsplitL : src.slice i.toNat (mid.toNat - i.toNat) = src.at' i.toNat :: src.slice (i.toNat + 1) (mid.toNat - (i.toNat + 1)) := by
        rw [show mid.toNat - i.toNat = (mid.toNat - (i.toNat + 1)) + 1 by omega, slice_cons]
      have hsplitR : src.slice j.toNat (hi.toNat - j.toNat) = src.at' j.toNat :: src.slice (j.toNat + 1) (hi.toNat - (j.toNat + 1)) := by
        rw [show hi.toNat - j.toNat = (hi.toNat - (j.toNat + 1)) + 1 by omega, slice_cons]
      rw [hsplitL, hsplitR, show cnt.toNat = (cnt.toNat - 1) + 1 by omega, take_merge_cons_cons,
        show cnt.toNat - 1 + 1 - 1 = cnt.toNat - 1 by omega]
      by_cases hle : src.get i (by u64g) ≤ src.get j (by u64g)
      · have hTL : TL = true := by simp [TL, hle]
        have e1 : (i + DI).toNat = i.toNat + 1 := by rw [eDI]; simp only [DI, hTL, ite_true]; u64g
        have e2 : (j + (1 - DI)).toNat = j.toNat := by rw [eDJ]; simp only [DI, hTL, ite_true]; u64g
        have hV : V = src.get i (by u64g) := by simp [V, hTL]
        rw [e1, e2, hV, hsplitR]
        simp only [get_eq_at'] at hle
        simp [hle, get_eq_at']
      · have hTL : TL = false := by simp [TL, hle]
        have e1 : (i + DI).toNat = i.toNat := by rw [eDI]; simp only [DI, hTL, Bool.false_eq_true, ite_false]; u64g
        have e2 : (j + (1 - DI)).toNat = j.toNat + 1 := by rw [eDJ]; simp only [DI, hTL, Bool.false_eq_true, ite_false]; u64g
        have hV : V = src.get j (by u64g) := by simp [V, hTL]
        rw [e1, e2, hV, hsplitL]
        simp only [get_eq_at'] at hle
        simp [hle, get_eq_at']
    · -- back region
      rw [ih2, ek', hbackW, ec]
      have hsplitL : (src.slice lo (i'.toNat - lo)).reverse = src.at' (i'.toNat - 1) :: (src.slice lo (i'.toNat - 1 - lo)).reverse := by
        rw [show i'.toNat - lo = (i'.toNat - 1 - lo) + 1 by omega, reverse_slice_succ,
          show lo + (i'.toNat - 1 - lo) = i'.toNat - 1 by omega]
      have hsplitR : (src.slice mid.toNat (j'.toNat - mid.toNat)).reverse =
          src.at' (j'.toNat - 1) :: (src.slice mid.toNat (j'.toNat - 1 - mid.toNat)).reverse := by
        rw [show j'.toNat - mid.toNat = (j'.toNat - 1 - mid.toNat) + 1 by omega, reverse_slice_succ,
          show mid.toNat + (j'.toNat - 1 - mid.toNat) = j'.toNat - 1 by omega]
      rw [hsplitL, hsplitR, show cnt.toNat = (cnt.toNat - 1) + 1 by omega, take_mergeBack_cons_cons,
        show cnt.toNat - 1 + 1 - 1 = cnt.toNat - 1 by omega]
      by_cases hle : src.get (i' - 1) (by u64g) ≤ src.get (j' - 1) (by u64g)
      · have hTR : TR = true := by simp [TR, hle]
        have e1 : (i' - (1 - DJ)).toNat = i'.toNat := by rw [eDI']; simp only [DJ, hTR, ite_true]; u64g
        have e2 : (j' - DJ).toNat = j'.toNat - 1 := by rw [eDJ']; simp only [DJ, hTR, ite_true]; u64g
        have hV : V' = src.get (j' - 1) (by u64g) := by simp [V', hTR]
        rw [e1, e2, hV, hsplitL]
        simp only [get_eq_at', ei', ej'] at hle
        simp [hle, get_eq_at', ej']
      · have hTR : TR = false := by simp [TR, hle]
        have e1 : (i' - (1 - DJ)).toNat = i'.toNat - 1 := by rw [eDI']; simp only [DJ, hTR, Bool.false_eq_true, ite_false]; u64g
        have e2 : (j' - DJ).toNat = j'.toNat := by rw [eDJ']; simp only [DJ, hTR, Bool.false_eq_true, ite_false]; u64g
        have hV : V' = src.get (i' - 1) (by u64g) := by simp [V', hTR]
        rw [e1, e2, hV, hsplitR]
        simp only [get_eq_at', ei', ej'] at hle
        simp [hle, get_eq_at', ei']
    · -- frame
      rw [ih3 x (by omega)]
      show ((dst.set k V _).set (k' - 1) V' _).at' x = _
      rw [at'_set_ne _ _ _ _ _ (by omega), at'_set_ne _ _ _ _ _ (by omega)]
  · rename_i hc
    have hc : ¬ 0 < cnt.toNat := hc
    refine ⟨?_, ?_, fun x _ => rfl⟩
    · rw [show cnt.toNat = 0 by omega, List.take_zero, List.append_nil, show mid.toNat - lo = k.toNat - lo by omega]
    · rw [show cnt.toNat = 0 by omega, List.take_zero, List.reverse_nil, List.nil_append,
        show hi.toNat - mid.toNat = hi.toNat - k'.toNat by omega, show mid.toNat = k'.toNat by omega]

end MergeSort.BottomUp
