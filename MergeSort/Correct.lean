import MergeSort.Simple
import MergeSort.Fast
import MergeSort.Slice
/-!
# Part 2, continued: the fast sort computes exactly what the simple sort computes

We prove `(Fast.sort xs).data.toList = mergeSort le xs.data.toList`. Everything proved about
`mergeSort` in Part 1 (sortedness, permutation) then transfers to the fast implementation for free.
-/
namespace MergeSort.Fast
open UInt64Array

/-- The comparison the fast sort uses. -/
abbrev le64 : UInt64 → UInt64 → Bool := fun x y => decide (x ≤ y)

/-- Goal-only `UInt64` arithmetic (does not touch hypotheses). -/
macro "u64g" : tactic => `(tactic|
  ((try simp only [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_ofNat,
      UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, Nat.reducePow, Nat.reduceMod, size_set, size_zeros])
   <;> omega))

@[simp] theorem castSize_val {a a' : UInt64Array} (r : { b : UInt64Array // b.size = a'.size })
    (h : a'.size = a.size) : (castSize r h).1 = r.1 := rfl

theorem merge_nil_left (ys : List UInt64) : merge le64 [] ys = ys := by simp [merge]
theorem merge_nil_right (xs : List UInt64) : merge le64 xs [] = xs := by cases xs <;> simp [merge]
theorem merge_cons_cons (x y : UInt64) (xs ys : List UInt64) :
    merge le64 (x :: xs) (y :: ys) =
      if x ≤ y then x :: merge le64 xs (y :: ys) else y :: merge le64 (x :: xs) ys := by
  simp [merge]

/-- Writing at position `k` extends the already-written prefix `[lo, k)` by one element. -/
theorem slice_set_end (a : UInt64Array) (p : UInt64) (v : UInt64) (hp) (off len : Nat)
    (h : p.toNat = off + len) :
    (a.set p v hp).slice off (len + 1) = a.slice off len ++ [v] := by
  rw [slice_succ, slice_set_of_not_mem _ _ _ _ _ _ (by omega), ← h, at'_set_self]

/-- What one run of the merge loop does to the output range `[lo, hi)` of half `d`. -/
theorem mergeLoop_spec (s d mid hi : UInt64) (lo : Nat)
    (hdisj : s.toNat + hi.toNat ≤ d.toNat ∨ d.toNat + hi.toNat ≤ s.toNat) :
    ∀ (n : Nat) (i j k : UInt64) (a : UInt64Array) hsz hs hd hmid hi' hj hinv,
    n = hi.toNat - k.toNat → lo ≤ k.toNat →
    (mergeLoop s d mid hi i j k a hsz hs hd hmid hi' hj hinv).1.slice (d.toNat + lo) (hi.toNat - lo) =
      a.slice (d.toNat + lo) (k.toNat - lo) ++
        merge le64 (a.slice (s.toNat + i.toNat) (mid.toNat - i.toNat))
                   (a.slice (s.toNat + j.toNat) (hi.toNat - j.toNat)) ∧
    ∀ x, (x < d.toNat + k.toNat ∨ d.toNat + hi.toNat ≤ x) →
      (mergeLoop s d mid hi i j k a hsz hs hd hmid hi' hj hinv).1.at' x = a.at' x := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro i j k a hsz hs hd hmid hi' hj hinv hn hlo
  rw [mergeLoop]
  split
  · rename_i hk
    have hk : k.toNat < hi.toNat := hk
    have ek : (k + 1).toNat = k.toNat + 1 := by u64g
    have edk : (d + k).toNat = d.toNat + k.toNat := by u64g
    -- the two facts we use in every branch: the write lands at the end of the written prefix, and
    -- it does not touch the source half
    have hend : ∀ v hp, (a.set (d + k) v hp).slice (d.toNat + lo) (k.toNat + 1 - lo) =
        a.slice (d.toNat + lo) (k.toNat - lo) ++ [v] := by
      intro v hp
      rw [show k.toNat + 1 - lo = (k.toNat - lo) + 1 by omega]
      exact slice_set_end _ _ _ _ _ _ (by omega)
    have hsrc : ∀ v hp off len, off + len ≤ s.toNat + hi.toNat → s.toNat ≤ off →
        (a.set (d + k) v hp).slice off len = a.slice off len := by
      intro v hp off len h1 h2
      apply slice_set_of_not_mem
      omega
    have hfr : ∀ v hp x, (x < d.toNat + k.toNat ∨ d.toNat + hi.toNat ≤ x) →
        (a.set (d + k) v hp).at' x = a.at' x := by
      intro v hp x hx
      apply at'_set_ne
      omega
    split
    · rename_i hi''
      have hi'' : i.toNat < mid.toNat := hi''
      have ei : (i + 1).toNat = i.toNat + 1 := by u64g
      have esi : (s + i).toNat = s.toNat + i.toNat := by u64g
      split
      · rename_i hj'
        have hj' : j.toNat < hi.toNat := hj'
        have esj : (s + j).toNat = s.toNat + j.toNat := by u64g
        have ej : (j + 1).toNat = j.toNat + 1 := by u64g
        dsimp only
        let TL : Bool := decide (a.get (s + i) (by u64g) ≤ a.get (s + j) (by u64g))
        let DI : UInt64 := if TL then 1 else 0
        let V : UInt64 := if TL then a.get (s + i) (by u64g) else a.get (s + j) (by u64g)
        have hDI : DI.toNat ≤ 1 := by show (if TL then (1 : UInt64) else 0).toNat ≤ 1; split <;> decide
        obtain ⟨ih1, ih2⟩ := ih (hi.toNat - (k + 1).toNat) (by omega) (i + DI) (j + (1 - DI)) (k + 1)
          (a.set (d + k) V (by u64g)) (by rw [size_set]; exact hsz) (by rw [size_set]; exact hs) (by rw [size_set]; exact hd)
          hmid (by simp only [UInt64.toNat_add, Nat.reducePow]; omega)
          (by simp only [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega)
          (by simp only [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega)
          rfl (by omega)
        have eDI : (i + DI).toNat = i.toNat + DI.toNat := by simp only [UInt64.toNat_add, Nat.reducePow]; omega
        have eDJ : (j + (1 - DI)).toNat = j.toNat + (1 - DI.toNat) := by
          simp only [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
        refine ⟨?_, fun x hx => ?_⟩
        · rw [castSize_val, ih1, ek, hend, hsrc _ _ _ _ (by omega) (by omega), hsrc _ _ _ _ (by omega) (by omega)]
          by_cases hle : a.get (s + i) (by u64g) ≤ a.get (s + j) (by u64g)
          · have hTL : TL = true := by simp [TL, hle]
            have e1 : (i + DI).toNat = i.toNat + 1 := by rw [eDI]; simp only [DI, hTL, ite_true]; u64g
            have e2 : (j + (1 - DI)).toNat = j.toNat := by rw [eDJ]; simp only [DI, hTL, ite_true]; u64g
            have hV : V = a.get (s + i) (by u64g) := by simp [V, hTL]
            rw [e1, e2, hV]
            rw [show mid.toNat - i.toNat = (mid.toNat - (i.toNat + 1)) + 1 by omega, slice_cons,
              show hi.toNat - j.toNat = (hi.toNat - (j.toNat + 1)) + 1 by omega, slice_cons, merge_cons_cons]
            simp only [get_eq_at', esi, esj] at hle
            simp [hle, Nat.add_assoc, get_eq_at', esi]
          · have hTL : TL = false := by simp [TL, hle]
            have e1 : (i + DI).toNat = i.toNat := by rw [eDI]; simp only [DI, hTL, Bool.false_eq_true, ite_false]; u64g
            have e2 : (j + (1 - DI)).toNat = j.toNat + 1 := by
              rw [eDJ]; simp only [DI, hTL, Bool.false_eq_true, ite_false]; u64g
            have hV : V = a.get (s + j) (by u64g) := by simp [V, hTL]
            rw [e1, e2, hV]
            rw [show mid.toNat - i.toNat = (mid.toNat - (i.toNat + 1)) + 1 by omega, slice_cons,
              show hi.toNat - j.toNat = (hi.toNat - (j.toNat + 1)) + 1 by omega, slice_cons, merge_cons_cons]
            simp only [get_eq_at', esi, esj] at hle
            simp [hle, Nat.add_assoc, get_eq_at', esj]
        · rw [castSize_val, ih2 x (by omega)]
          exact hfr _ _ x hx
      · -- right run exhausted: take from the left run
        rename_i hj'
        have hj' : ¬ j.toNat < hi.toNat := hj'
        dsimp only
        obtain ⟨ih1, ih2⟩ := ih (hi.toNat - (k + 1).toNat) (by omega) (i + 1) j (k + 1)
          (a.set (d + k) (a.get (s + i) (by u64g)) (by u64g))
          (by u64g) (by u64g) (by u64g) hmid (by u64g) hj (by u64g) rfl (by omega)
        refine ⟨?_, fun x hx => ?_⟩
        · rw [castSize_val, ih1, ek, hend, ei, hsrc _ _ _ _ (by omega) (by omega),
            hsrc _ _ _ _ (by omega) (by omega)]
          rw [show hi.toNat - j.toNat = 0 by omega, slice_zero, merge_nil_right, merge_nil_right,
            show mid.toNat - i.toNat = (mid.toNat - (i.toNat + 1)) + 1 by omega, slice_cons]
          simp [Nat.add_assoc, get_eq_at', esi]
        · rw [castSize_val, ih2 x (by omega)]
          exact hfr _ _ x hx
    · -- left run exhausted: take from the right run
      rename_i hi''
      have hi'' : ¬ i.toNat < mid.toNat := hi''
      have ej : (j + 1).toNat = j.toNat + 1 := by u64g
      have esj : (s + j).toNat = s.toNat + j.toNat := by u64g
      dsimp only
      obtain ⟨ih1, ih2⟩ := ih (hi.toNat - (k + 1).toNat) (by omega) i (j + 1) (k + 1)
        (a.set (d + k) (a.get (s + j) (by u64g)) (by u64g))
        (by u64g) (by u64g) (by u64g) hmid hi' (by u64g) (by u64g) rfl (by omega)
      refine ⟨?_, fun x hx => ?_⟩
      · rw [castSize_val, ih1, ek, hend, ej, hsrc _ _ _ _ (by omega) (by omega),
          hsrc _ _ _ _ (by omega) (by omega)]
        rw [show mid.toNat - i.toNat = 0 by omega, slice_zero, merge_nil_left, merge_nil_left,
          show hi.toNat - j.toNat = (hi.toNat - (j.toNat + 1)) + 1 by omega, slice_cons]
        simp [Nat.add_assoc, get_eq_at', esj]
      · rw [castSize_val, ih2 x (by omega)]
        exact hfr _ _ x hx
  · -- k = hi: nothing to do
    rename_i hk
    have hk : ¬ k.toNat < hi.toNat := hk
    refine ⟨?_, fun x _ => rfl⟩
    have : hi.toNat - k.toNat = 0 := by omega
    have hi0 : mid.toNat - i.toNat = 0 := by omega
    have hj0 : hi.toNat - j.toNat = 0 := by omega
    rw [hi0, hj0, slice_zero, slice_zero, merge_nil_left, List.append_nil]
    congr 1
    omega

/-! ## The recursive structure -/

theorem mergeSort_of_length_le_one (l : List UInt64) (h : l.length ≤ 1) : mergeSort le64 l = l := by
  rw [mergeSort, dif_pos h]

/-- `mergeSort` always equals "merge the sorted halves", even for short lists. -/
theorem mergeSort_eq_merge (l : List UInt64) :
    mergeSort le64 l = merge le64 (mergeSort le64 (l.take (l.length / 2))) (mergeSort le64 (l.drop (l.length / 2))) := by
  by_cases h : l.length ≤ 1
  · have : l.length / 2 = 0 := by omega
    rw [this, List.take_zero, List.drop_zero, mergeSort_of_length_le_one l h,
      mergeSort_of_length_le_one [] (by simp), merge_nil_left]
  · rw [mergeSort, dif_neg h]

/-- Pure bookkeeping: combining the two sorted halves (in half `s`) and the merge (into half `d`). -/
theorem sortRange_combine (sN dN loN hiN midN : Nat) (a A₁ A₂ B : UInt64Array)
    (hmid : midN = loN + (hiN - loN) / 2) (hlo : loN ≤ hiN)
    (hdisj : sN + hiN ≤ dN ∨ dN + hiN ≤ sN)
    (hpre : a.slice (sN + loN) (hiN - loN) = a.slice (dN + loN) (hiN - loN))
    (H1a : A₁.slice (sN + loN) (midN - loN) = mergeSort le64 (a.slice (dN + loN) (midN - loN)))
    (H1b : ∀ x, ¬ (sN + loN ≤ x ∧ x < sN + midN) → ¬ (dN + loN ≤ x ∧ x < dN + midN) → A₁.at' x = a.at' x)
    (H2a : A₂.slice (sN + midN) (hiN - midN) = mergeSort le64 (A₁.slice (dN + midN) (hiN - midN)))
    (H2b : ∀ x, ¬ (sN + midN ≤ x ∧ x < sN + hiN) → ¬ (dN + midN ≤ x ∧ x < dN + hiN) → A₂.at' x = A₁.at' x)
    (HBa : B.slice (dN + loN) (hiN - loN) =
      A₂.slice (dN + loN) (loN - loN) ++ merge le64 (A₂.slice (sN + loN) (midN - loN)) (A₂.slice (sN + midN) (hiN - midN)))
    (HBb : ∀ x, (x < dN + loN ∨ dN + hiN ≤ x) → B.at' x = A₂.at' x) :
    B.slice (dN + loN) (hiN - loN) = mergeSort le64 (a.slice (sN + loN) (hiN - loN)) ∧
    ∀ x, ¬ (sN + loN ≤ x ∧ x < sN + hiN) → ¬ (dN + loN ≤ x ∧ x < dN + hiN) → B.at' x = a.at' x := by
  have hm1 : loN ≤ midN := by omega
  have hm2 : midN ≤ hiN := by omega
  constructor
  · -- the left run in `A₂` is untouched since `A₁`
    have e1 : A₂.slice (sN + loN) (midN - loN) = A₁.slice (sN + loN) (midN - loN) := by
      apply slice_congr; intro t ht; apply H2b <;> omega
    -- the right run's source in `A₁` is untouched since `a`
    have e2 : A₁.slice (dN + midN) (hiN - midN) = a.slice (dN + midN) (hiN - midN) := by
      apply slice_congr; intro t ht; apply H1b <;> omega
    rw [HBa, Nat.sub_self, slice_zero, List.nil_append, e1, H1a, H2a, e2, hpre,
      mergeSort_eq_merge (a.slice (dN + loN) (hiN - loN))]
    have hdiv : (midN - loN + (hiN - midN)) / 2 = midN - loN := by omega
    rw [show hiN - loN = (midN - loN) + (hiN - midN) by omega, length_slice, hdiv, take_slice, drop_slice,
      show dN + loN + (midN - loN) = dN + midN by omega]
  · intro x hx1 hx2
    rw [HBb x (by omega), H2b x (by omega) (by omega), H1b x (by omega) (by omega)]

/-- What `sortRange` does: the output range of half `d` becomes the merge sort of the input range
    (which lives in both halves, and is read from half `s`); nothing outside the two ranges changes. -/
theorem sortRange_spec :
    ∀ (n : Nat) (s d lo hi : UInt64) (a : UInt64Array) hsz hs hd hlo,
    n = hi.toNat - lo.toNat →
    (s.toNat + hi.toNat ≤ d.toNat ∨ d.toNat + hi.toNat ≤ s.toNat) →
    a.slice (s.toNat + lo.toNat) (hi.toNat - lo.toNat) = a.slice (d.toNat + lo.toNat) (hi.toNat - lo.toNat) →
    (sortRange s d lo hi a hsz hs hd hlo).1.slice (d.toNat + lo.toNat) (hi.toNat - lo.toNat) =
      mergeSort le64 (a.slice (s.toNat + lo.toNat) (hi.toNat - lo.toNat)) ∧
    ∀ x, ¬ (s.toNat + lo.toNat ≤ x ∧ x < s.toNat + hi.toNat) →
         ¬ (d.toNat + lo.toNat ≤ x ∧ x < d.toNat + hi.toNat) →
         (sortRange s d lo hi a hsz hs hd hlo).1.at' x = a.at' x := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro s d lo hi a hsz hs hd hlo hn hdisj hpre
  rw [sortRange]
  dsimp only
  -- name the midpoint (a local definition, so everything below stays definitionally equal)
  let M := lo + (hi - lo) / 2
  have hMN : M.toNat = lo.toNat + (hi.toNat - lo.toNat) / 2 := by
    show (lo + (hi - lo) / 2).toNat = _; u64g
  have hMlo : lo.toNat ≤ M.toNat := by omega
  have hMhi : M.toNat ≤ hi.toNat := by omega
  -- the prefix / suffix halves of the precondition
  have hpre1 : a.slice (s.toNat + lo.toNat) (M.toNat - lo.toNat) = a.slice (d.toNat + lo.toNat) (M.toNat - lo.toNat) := by
    have := congrArg (List.take (M.toNat - lo.toNat)) hpre
    rwa [show hi.toNat - lo.toNat = (M.toNat - lo.toNat) + (hi.toNat - M.toNat) by omega, take_slice, take_slice] at this
  have hpre2 : a.slice (s.toNat + M.toNat) (hi.toNat - M.toNat) = a.slice (d.toNat + M.toNat) (hi.toNat - M.toNat) := by
    have := congrArg (List.drop (M.toNat - lo.toNat)) hpre
    rwa [show hi.toNat - lo.toNat = (M.toNat - lo.toNat) + (hi.toNat - M.toNat) by omega, drop_slice, drop_slice,
      show s.toNat + lo.toNat + (M.toNat - lo.toNat) = s.toNat + M.toNat by omega,
      show d.toNat + lo.toNat + (M.toNat - lo.toNat) = d.toNat + M.toNat by omega] at this
  -- facts about the first half (whether or not we recursed)
  have H1 : ∀ (A₁ : UInt64Array), A₁.size = a.size →
      (∀ h : 2 ≤ M - lo, A₁ = (sortRange d s lo M a hsz (by omega) (by omega) hMlo).1) →
      (¬ 2 ≤ M - lo → A₁ = a) →
      A₁.slice (s.toNat + lo.toNat) (M.toNat - lo.toNat) = mergeSort le64 (a.slice (d.toNat + lo.toNat) (M.toNat - lo.toNat)) ∧
      ∀ x, ¬ (s.toNat + lo.toNat ≤ x ∧ x < s.toNat + M.toNat) → ¬ (d.toNat + lo.toNat ≤ x ∧ x < d.toNat + M.toNat) →
        A₁.at' x = a.at' x := by
    intro A₁ _ hrec hnorec
    by_cases h : 2 ≤ M - lo
    · have h' : 2 ≤ M.toNat - lo.toNat := by have := UInt64.le_iff_toNat_le.mp h; u64
      rw [hrec h]
      obtain ⟨ih1, ih2⟩ := ih (M.toNat - lo.toNat) (by omega) d s lo M a hsz (by omega) (by omega) hMlo rfl
        (by omega) hpre1.symm
      exact ⟨ih1, fun x hx1 hx2 => ih2 x hx2 hx1⟩
    · have h' : ¬ 2 ≤ M.toNat - lo.toNat := by
        intro c; apply h; rw [UInt64.le_iff_toNat_le]; u64g
      rw [hnorec h]
      refine ⟨?_, fun x _ _ => rfl⟩
      rw [mergeSort_of_length_le_one _ (by simp; omega), hpre1]
  -- facts about the second half (whether or not we recursed)
  have H2 : ∀ (A₁ A₂ : UInt64Array) (hA₁ : A₁.size = a.size), A₂.size = a.size →
      (∀ x, ¬ (s.toNat + lo.toNat ≤ x ∧ x < s.toNat + M.toNat) → ¬ (d.toNat + lo.toNat ≤ x ∧ x < d.toNat + M.toNat) →
        A₁.at' x = a.at' x) →
      (∀ h : 2 ≤ hi - M, A₂ = (sortRange d s M hi A₁ (by omega) (by omega) (by omega) hMhi).1) →
      (¬ 2 ≤ hi - M → A₂ = A₁) →
      A₂.slice (s.toNat + M.toNat) (hi.toNat - M.toNat) = mergeSort le64 (A₁.slice (d.toNat + M.toNat) (hi.toNat - M.toNat)) ∧
      ∀ x, ¬ (s.toNat + M.toNat ≤ x ∧ x < s.toNat + hi.toNat) → ¬ (d.toNat + M.toNat ≤ x ∧ x < d.toNat + hi.toNat) →
        A₂.at' x = A₁.at' x := by
    intro A₁ A₂ hA₁ _ H1b hrec hnorec
    -- the second range is still the input, in both halves
    have hpre' : A₁.slice (d.toNat + M.toNat) (hi.toNat - M.toNat) = A₁.slice (s.toNat + M.toNat) (hi.toNat - M.toNat) := by
      have e1 : A₁.slice (d.toNat + M.toNat) (hi.toNat - M.toNat) = a.slice (d.toNat + M.toNat) (hi.toNat - M.toNat) := by
        apply slice_congr; intro t ht; apply H1b <;> omega
      have e2 : A₁.slice (s.toNat + M.toNat) (hi.toNat - M.toNat) = a.slice (s.toNat + M.toNat) (hi.toNat - M.toNat) := by
        apply slice_congr; intro t ht; apply H1b <;> omega
      rw [e1, e2, hpre2]
    by_cases h : 2 ≤ hi - M
    · have h' : 2 ≤ hi.toNat - M.toNat := by have := UInt64.le_iff_toNat_le.mp h; u64
      rw [hrec h]
      obtain ⟨ih1, ih2⟩ := ih (hi.toNat - M.toNat) (by omega) d s M hi A₁ (by omega) (by omega) (by omega) hMhi rfl
        (by omega) hpre'
      exact ⟨ih1, fun x hx1 hx2 => ih2 x hx2 hx1⟩
    · have h' : ¬ 2 ≤ hi.toNat - M.toNat := by
        intro c; apply h; rw [UInt64.le_iff_toNat_le]; u64g
      rw [hnorec h]
      refine ⟨?_, fun x _ _ => rfl⟩
      rw [mergeSort_of_length_le_one _ (by simp; omega), hpre']
  -- name the two intermediate results (definitionally the ones in the goal)
  let X₁ : { b : UInt64Array // b.size = a.size } :=
    if h : 2 ≤ M - lo then sortRange d s lo M a hsz (by omega) (by omega) hMlo else ⟨a, rfl⟩
  let X₂ : { b : UInt64Array // b.size = a.size } :=
    if h : 2 ≤ hi - M then castSize (sortRange d s M hi X₁.1 (by omega) (by omega) (by omega) hMhi) X₁.2 else X₁
  have F1 := H1 X₁.1 X₁.2 (fun h => by simp only [X₁, dif_pos h]) (fun h => by simp only [X₁, dif_neg h])
  have F2 := H2 X₁.1 X₂.1 X₁.2 X₂.2 F1.2 (fun h => by simp only [X₂, dif_pos h, castSize_val])
    (fun h => by simp only [X₂, dif_neg h])
  have HB := mergeLoop_spec s d M hi lo.toNat hdisj (hi.toNat - lo.toNat) lo M lo X₂.1 (by omega) (by omega) (by omega)
    hMhi hMlo hMhi rfl rfl (Nat.le_refl _)
  simp only [castSize_val]
  exact sortRange_combine s.toNat d.toNat lo.toNat hi.toNat M.toNat a X₁.1 X₂.1 _ hMN hlo hdisj hpre
    F1.1 F1.2 F2.1 F2.2 HB.1 HB.2

/-! ## The copy loops -/

theorem copyIn_spec (src : UInt64Array) (n : UInt64) :
    ∀ (m : Nat) (k : UInt64) (a : UInt64Array) hn ha hsz hk, m = n.toNat - k.toNat →
    ∀ x, x < n.toNat →
      (k.toNat ≤ x → (copyIn src n k a hn ha hsz hk).1.at' x = src.at' x ∧
                     (copyIn src n k a hn ha hsz hk).1.at' (n.toNat + x) = src.at' x) ∧
      (x < k.toNat → (copyIn src n k a hn ha hsz hk).1.at' x = a.at' x ∧
                     (copyIn src n k a hn ha hsz hk).1.at' (n.toNat + x) = a.at' (n.toNat + x)) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro k a hn ha hsz hk hm x hx
  rw [copyIn]
  split
  · rename_i h
    have h : k.toNat < n.toNat := h
    have ek : (k + 1).toNat = k.toNat + 1 := by u64g
    have enk : (n + k).toNat = n.toNat + k.toNat := by u64g
    simp only [castSize_val]
    obtain ⟨ih1, ih2⟩ := ih (n.toNat - (k + 1).toNat) (by omega) (k + 1)
      ((a.set k (src.get k (by u64g)) (by u64g)).set (n + k) (src.get k (by u64g)) (by u64g))
      hn (by u64g) (by u64g) (by u64g) rfl x hx
    refine ⟨fun hkx => ?_, fun hxk => ?_⟩
    · by_cases hkx' : k.toNat + 1 ≤ x
      · exact ih1 (by omega)
      · have hx : x = k.toNat := by omega
        subst hx
        obtain ⟨e1, e2⟩ := ih2 (by omega)
        refine ⟨?_, ?_⟩
        · rw [e1, at'_set_ne _ _ _ _ _ (by omega), at'_set_self, get_eq_at']
        · rw [e2, at'_set_eq _ _ _ _ _ enk, get_eq_at']
    · obtain ⟨e1, e2⟩ := ih2 (by omega)
      refine ⟨?_, ?_⟩
      · rw [e1, at'_set_ne _ _ _ _ _ (by omega), at'_set_ne _ _ _ _ _ (by omega)]
      · rw [e2, at'_set_ne _ _ _ _ _ (by omega), at'_set_ne _ _ _ _ _ (by omega)]
  · rename_i h
    have h : ¬ k.toNat < n.toNat := h
    exact ⟨fun hkx => absurd hx (by omega), fun _ => ⟨rfl, rfl⟩⟩

theorem copyOut_spec (a : UInt64Array) (n : UInt64) :
    ∀ (m : Nat) (k : UInt64) (out : UInt64Array) ha hsz hout hk, m = n.toNat - k.toNat →
    ∀ x, x < n.toNat →
      (k.toNat ≤ x → (copyOut a n k out ha hsz hout hk).1.at' x = a.at' (n.toNat + x)) ∧
      (x < k.toNat → (copyOut a n k out ha hsz hout hk).1.at' x = out.at' x) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro k out ha hsz hout hk hm x hx
  rw [copyOut]
  split
  · rename_i h
    have h : k.toNat < n.toNat := h
    have ek : (k + 1).toNat = k.toNat + 1 := by u64g
    have enk : (n + k).toNat = n.toNat + k.toNat := by u64g
    simp only [castSize_val]
    obtain ⟨ih1, ih2⟩ := ih (n.toNat - (k + 1).toNat) (by omega) (k + 1)
      (out.set k (a.get (n + k) (by u64g)) (by u64g)) ha hsz (by u64g) (by u64g) rfl x hx
    refine ⟨fun hkx => ?_, fun hxk => ?_⟩
    · by_cases hkx' : k.toNat + 1 ≤ x
      · exact ih1 (by omega)
      · have hx : x = k.toNat := by omega
        subst hx
        rw [ih2 (by omega), at'_set_self, get_eq_at', enk]
    · rw [ih2 (by omega), at'_set_ne _ _ _ _ _ (by omega)]
  · rename_i h
    have h : ¬ k.toNat < n.toNat := h
    exact ⟨fun hkx => absurd hx (by omega), fun _ => rfl⟩

/-! ## The main theorem -/

/-- The fast sort computes exactly the simple sort. -/
theorem sort_toList (xs : UInt64Array) (hsz : xs.size < 2 ^ 63) :
    (sort xs hsz).data.toList = mergeSort le64 xs.data.toList := by
  rw [sort]
  dsimp only
  let n : UInt64 := xs.size.toUInt64
  have hn : n.toNat = xs.size := by simp [n]; omega
  let A : { b : UInt64Array // b.size = (zeros (2 * xs.size)).size } :=
    copyIn xs n 0 (zeros (2 * xs.size)) hn (by u64g) (by u64g) (by u64g)
  have hA : A.1.size = 2 * xs.size := by simpa using A.2
  let A' : { b : UInt64Array // b.size = A.1.size } :=
    sortRange 0 n 0 n A.1 (by omega) (by u64g) (by u64g) (by u64g)
  have hA' : A'.1.size = 2 * xs.size := by rw [A'.2, hA]
  let B : { b : UInt64Array // b.size = (zeros xs.size).size } :=
    copyOut A'.1 n 0 (zeros xs.size) (by omega) (by omega) (by u64g) (by u64g)
  have hB : B.1.size = xs.size := by simpa using B.2
  -- the input is in both halves of `A`
  have HA := copyIn_spec xs n (n.toNat - (0 : UInt64).toNat) 0 (zeros (2 * xs.size)) hn (by u64g) (by u64g)
    (by u64g) rfl
  have hxs : xs.slice 0 n.toNat = xs.data.toList := by rw [hn, slice_eq_toList]
  have HA1 : A.1.slice 0 n.toNat = xs.data.toList := by
    rw [← hxs]; apply slice_congr; intro t ht
    have := ((HA t ht).1 (by u64g)).1
    simpa using this
  have HA2 : A.1.slice n.toNat n.toNat = xs.data.toList := by
    rw [← hxs]; apply slice_congr'; intro t ht
    have := ((HA t ht).1 (by u64g)).2
    simpa using this
  -- sorting: the sorted output lands in the second half of `A'`
  have HS := (sortRange_spec (n.toNat - (0 : UInt64).toNat) 0 n 0 n A.1 (by omega) (by u64g) (by u64g)
    (by u64g) rfl (Or.inl (by u64g)) (by simpa using HA1.trans HA2.symm)).1
  simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.add_zero, Nat.sub_zero] at HS
  -- copying out
  have HB := copyOut_spec A'.1 n (n.toNat - (0 : UInt64).toNat) 0 (zeros xs.size) (by omega) (by omega) (by u64g)
    (by u64g) rfl
  have hBn : B.1.size = n.toNat := by rw [hB, hn]
  show B.1.data.toList = _
  rw [← slice_eq_toList, hBn]
  rw [show B.1.slice 0 n.toNat = A'.1.slice n.toNat n.toNat by
    apply slice_congr'; intro t ht
    have := (HB t ht).1 (by u64g)
    simpa using this]
  rw [HS, HA1]

/-- The fast sort produces a sorted list. -/
theorem sort_sorted (xs : UInt64Array) (hsz : xs.size < 2 ^ 63) :
    (sort xs hsz).data.toList.Pairwise (· ≤ ·) := by
  have := mergeSort_sorted le64 (fun a b c h1 h2 => by simpa using UInt64.le_trans (by simpa using h1) (by simpa using h2))
    (fun a b => by simpa using UInt64.le_total a b) xs.data.toList
  rw [sort_toList]
  simpa [Sorted] using this

/-- The fast sort produces a permutation of its input. -/
theorem sort_perm (xs : UInt64Array) (hsz : xs.size < 2 ^ 63) :
    (sort xs hsz).data.toList.Perm xs.data.toList := by
  rw [sort_toList]; exact mergeSort_perm le64 _

end MergeSort.Fast
