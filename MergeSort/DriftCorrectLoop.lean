import MergeSort.DriftCorrect
/-!
# Correctness of the run stack, the quicksort and the entry point of `DriftSort`
-/
namespace DriftSort
open UInt64Array MergeSort MergeSort.Fast MergeSort.BottomUp

/-- A permutation of a sub-slice, with everything else unchanged, is a permutation of any enclosing slice. -/
theorem perm_of_sub (a b : A) (lo len off n : Nat) (hsub1 : lo ≤ off) (hsub2 : off + n ≤ lo + len)
    (hp : (b.slice off n).Perm (a.slice off n)) (hf : ∀ x, (x < off ∨ off + n ≤ x) → b.at' x = a.at' x) :
    (b.slice lo len).Perm (a.slice lo len) := by
  have split : ∀ c : A, c.slice lo len = c.slice lo (off - lo) ++ (c.slice off n ++ c.slice (off + n) (lo + len - off - n)) := by
    intro c
    have h1 : c.slice lo len = c.slice lo ((off - lo) + (n + (lo + len - off - n))) := by congr 1; omega
    rw [h1, slice_add, slice_add, show lo + (off - lo) = off by omega]
  rw [split a, split b]
  refine List.Perm.append (by rw [slice_congr (fun t ht => hf _ (Or.inl (by omega)))]) (List.Perm.append hp ?_)
  rw [slice_congr (fun t ht => hf _ (Or.inr (by omega)))]

/-- The specification a range sorter must satisfy. -/
def QuickSpec (quick : Quick) : Prop :=
  ∀ (v s : A) (lo hi : UInt64) hv hs hvsz hssz hlo,
    Sorted le64 ((quick v s lo hi hv hs hvsz hssz hlo).1.1.slice lo.toNat (hi.toNat - lo.toNat)) ∧
    ((quick v s lo hi hv hs hvsz hssz hlo).1.1.slice lo.toNat (hi.toNat - lo.toNat)).Perm (v.slice lo.toNat (hi.toNat - lo.toNat)) ∧
    ∀ x, (x < lo.toNat ∨ hi.toNat ≤ x) → (quick v s lo hi hv hs hvsz hssz hlo).1.1.at' x = v.at' x

theorem insertionQuick_spec : QuickSpec insertionQuick := by
  intro v s lo hi hv hs hvsz hssz hlo
  unfold insertionQuick
  dsimp only
  obtain ⟨S, F⟩ := insertionSortRange_spec lo hi (hi.toNat - lo.toNat) lo v hvsz hv (by omega) rfl hlo
    (by simp only [Nat.sub_self, slice_zero]; simp [Sorted])
  refine ⟨?_, ?_, F⟩
  · rw [S]; exact insertAll_sorted _ _ (by simp only [Nat.sub_self, slice_zero]; simp [Sorted])
  · rw [S]; refine (insertAll_perm _ _).trans ?_; simp

/-! ## Runs -/

theorem createRunRest_spec (v s : A) (lo hi minGood : UInt64) (eager : Bool) hv hs hvsz hssz hlo hmg :
    ((createRunRest v s lo hi minGood eager hv hs hvsz hssz hlo hmg).1.1.sorted = true →
      Sorted le64 ((createRunRest v s lo hi minGood eager hv hs hvsz hssz hlo hmg).1.2.1.slice lo.toNat
        (createRunRest v s lo hi minGood eager hv hs hvsz hssz hlo hmg).1.1.len.toNat)) ∧
    ((createRunRest v s lo hi minGood eager hv hs hvsz hssz hlo hmg).1.2.1.slice lo.toNat (hi.toNat - lo.toNat)).Perm
      (v.slice lo.toNat (hi.toNat - lo.toNat)) ∧
    ∀ x, (x < lo.toNat ∨ hi.toNat ≤ x) → (createRunRest v s lo hi minGood eager hv hs hvsz hssz hlo hmg).1.2.1.at' x = v.at' x := by
  unfold createRunRest
  have hbnd := UInt64.toNat_lt hi
  have hlen : (hi - lo).toNat = hi.toNat - lo.toNat := UInt64.toNat_sub_of_le _ _ (by u64)
  dsimp only
  split
  · -- eager: a small sort of the first m elements
    have hm : 0 < (if smallSortThreshold ≤ hi - lo then smallSortThreshold else hi - lo).toNat ∧
        lo.toNat + (if smallSortThreshold ≤ hi - lo then smallSortThreshold else hi - lo).toNat ≤ hi.toNat := by
      split <;> (simp only [smallSortThreshold, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *; omega)
    have em : (lo + (if smallSortThreshold ≤ hi - lo then smallSortThreshold else hi - lo)).toNat =
        lo.toNat + (if smallSortThreshold ≤ hi - lo then smallSortThreshold else hi - lo).toNat := toNat_add_of_lt _ _ (by omega)
    have S := smallSort_spec v s lo (lo + (if smallSortThreshold ≤ hi - lo then smallSortThreshold else hi - lo))
      (by rw [em]; omega) (by rw [em]; omega) hvsz hssz (by rw [em]; omega)
    generalize hR : smallSort v s lo (lo + (if smallSortThreshold ≤ hi - lo then smallSortThreshold else hi - lo))
      (by rw [em]; omega) (by rw [em]; omega) hvsz hssz (by rw [em]; omega) = R at S
    rcases R with ⟨⟨v1, s1⟩, hv1, hs1⟩
    dsimp only at S ⊢
    obtain ⟨S1, S2, S3⟩ := S
    rw [em, Nat.add_sub_cancel_left] at S1 S2
    refine ⟨fun _ => S1, ?_, fun x hx => S3 x (by rw [em]; omega)⟩
    exact perm_of_sub v v1 lo.toNat (hi.toNat - lo.toNat) lo.toNat _ (Nat.le_refl _) (by omega) S2
      (fun x hx => S3 x (by rw [em]; omega))
  · -- unsorted: nothing happens
    exact ⟨fun h => by simp [mkUnsorted] at h, List.Perm.refl _, fun _ _ => rfl⟩

theorem createRun_spec (v s : A) (lo hi minGood : UInt64) (eager : Bool) hv hs hvsz hssz hlo hmg :
    ((createRun v s lo hi minGood eager hv hs hvsz hssz hlo hmg).1.1.sorted = true →
      Sorted le64 ((createRun v s lo hi minGood eager hv hs hvsz hssz hlo hmg).1.2.1.slice lo.toNat
        (createRun v s lo hi minGood eager hv hs hvsz hssz hlo hmg).1.1.len.toNat)) ∧
    ((createRun v s lo hi minGood eager hv hs hvsz hssz hlo hmg).1.2.1.slice lo.toNat (hi.toNat - lo.toNat)).Perm
      (v.slice lo.toNat (hi.toNat - lo.toNat)) ∧
    ∀ x, (x < lo.toNat ∨ hi.toNat ≤ x) → (createRun v s lo hi minGood eager hv hs hvsz hssz hlo hmg).1.2.1.at' x = v.at' x := by
  unfold createRun
  have hlen : (hi - lo).toNat = hi.toNat - lo.toNat := UInt64.toNat_sub_of_le _ _ (by u64)
  dsimp only
  split
  · -- run detection
    have F := findRun_spec lo hi v hvsz hv hlo
    generalize hF : findRun lo hi v hvsz hv hlo = R at F
    rcases R with ⟨⟨e, v1⟩, he1, he2, hv1⟩
    dsimp only at F he1 he2 hv1 ⊢
    obtain ⟨F1, F2, F3⟩ := F
    have ee : (e - lo).toNat = e.toNat - lo.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))
    have gp : (v1.slice lo.toNat (hi.toNat - lo.toNat)).Perm (v.slice lo.toNat (hi.toNat - lo.toNat)) :=
      perm_of_sub v v1 lo.toNat (hi.toNat - lo.toNat) lo.toNat (e.toNat - lo.toNat) (Nat.le_refl _) (by omega) F2 (fun x hx => F3 x (by omega))
    split
    · -- accepted as a sorted run
      dsimp only
      refine ⟨fun _ => ?_, gp, fun x hx => F3 x (by omega)⟩
      simp only [mkSorted]; rw [ee]; exact F1
    · -- too short: the rest, on the array after the (harmless) reversal
      have R := createRunRest_spec v1 s lo hi minGood eager (by rw [hv1]; exact hv) hs (by rw [hv1]; exact hvsz) hssz hlo hmg
      generalize hR : createRunRest v1 s lo hi minGood eager (by rw [hv1]; exact hv) hs (by rw [hv1]; exact hvsz) hssz hlo hmg = R' at R
      rcases R' with ⟨⟨r, v2, s2⟩, hv2, hs2, h3, h4⟩
      dsimp only at R ⊢
      exact ⟨R.1, R.2.1.trans gp, fun x hx => (R.2.2 x hx).trans (F3 x (by omega))⟩
  · exact createRunRest_spec v s lo hi minGood eager hv hs hvsz hssz hlo hmg

end DriftSort
