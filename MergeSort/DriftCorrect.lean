import MergeSort.DriftSort
/-!
# Correctness of the bounds-safe driftsort (`DriftSort.lean`)

Specs are lists (`slice`), every theorem has a frame clause, proofs compose the specs of the kernels.
-/
namespace DriftSort
open UInt64Array MergeSort MergeSort.Fast MergeSort.BottomUp

/-! ## The physical merge -/

theorem mergeRuns_spec (v s : A) (lo mid hi : UInt64) hv hs hvsz hssz hlo hmid
    (hL : Sorted le64 (v.slice lo.toNat (mid.toNat - lo.toNat)))
    (hR : Sorted le64 (v.slice mid.toNat (hi.toNat - mid.toNat))) :
    (mergeRuns v s lo mid hi hv hs hvsz hssz hlo hmid).1.1.slice lo.toNat (hi.toNat - lo.toNat) =
      merge le64 (v.slice lo.toNat (mid.toNat - lo.toNat)) (v.slice mid.toNat (hi.toNat - mid.toNat)) ∧
    ∀ x, (x < lo.toNat ∨ hi.toNat ≤ x) → (mergeRuns v s lo mid hi hv hs hvsz hssz hlo hmid).1.1.at' x = v.at' x := by
  unfold mergeRuns
  dsimp only
  obtain ⟨M, _⟩ := mergeKernelS_spec lo mid hi v s hssz hv hs hlo hmid hL hR
  obtain ⟨C1, C2⟩ := copyRange_spec hi (mergeKernelS lo mid hi v s hssz hv hs hlo hmid).1 (hi.toNat - lo.toNat) lo v hvsz
    (by rw [(mergeKernelS lo mid hi v s hssz hv hs hlo hmid).2]; exact hs) hv rfl
  refine ⟨?_, fun x hx => C2 x hx⟩
  rw [← M]
  apply slice_congr
  intro t ht
  exact C1 _ (by omega) (by omega)

/-! ## The small sort -/

/-- After copying `v[a, b)` into `s` at the same positions: the slice agrees with `v`. -/
theorem copyRange_slice (a b : UInt64) (src dst : A) hsz hs hd :
    (copyRange a b src dst hsz hs hd).1.slice a.toNat (b.toNat - a.toNat) = src.slice a.toNat (b.toNat - a.toNat) := by
  obtain ⟨C1, _⟩ := copyRange_spec b src (b.toNat - a.toNat) a dst hsz hs hd rfl
  apply slice_congr; intro t ht; exact C1 _ (by omega) (by omega)

theorem copyRange_frame (a b : UInt64) (src dst : A) hsz hs hd (off len : Nat) (h : off + len ≤ a.toNat ∨ b.toNat ≤ off) :
    (copyRange a b src dst hsz hs hd).1.slice off len = dst.slice off len := by
  obtain ⟨_, C2⟩ := copyRange_spec b src (b.toNat - a.toNat) a dst hsz hs hd rfl
  apply slice_congr; intro t ht; exact C2 _ (by omega)

theorem insertionSortRange_frame (lo hi k : UInt64) (a : A) hsz hhi hlo (off len : Nat) (h : off + len ≤ lo.toNat ∨ hi.toNat ≤ off)
    (hk : k.toNat ≤ hi.toNat) (hsorted : Sorted le64 (a.slice lo.toNat (k.toNat - lo.toNat))) :
    (insertionSortRange lo hi k a hsz hhi hlo).1.slice off len = a.slice off len := by
  obtain ⟨_, F⟩ := insertionSortRange_spec lo hi (hi.toNat - k.toNat) k a hsz hhi hlo rfl hk hsorted
  apply slice_congr; intro t ht; exact F _ (by omega)

theorem smallSortRest_spec (v s : A) (lo mid hi pre : UInt64) hv hs hvsz hssz h1 h2
    (hL : Sorted le64 (s.slice lo.toNat pre.toNat)) (hR : Sorted le64 (s.slice mid.toNat pre.toNat)) :
    Sorted le64 ((smallSortRest v s lo mid hi pre hv hs hvsz hssz h1 h2).1.1.slice lo.toNat (hi.toNat - lo.toNat)) ∧
    ((smallSortRest v s lo mid hi pre hv hs hvsz hssz h1 h2).1.1.slice lo.toNat (hi.toNat - lo.toNat)).Perm
      (s.slice lo.toNat pre.toNat ++ v.slice (lo.toNat + pre.toNat) (mid.toNat - lo.toNat - pre.toNat) ++
       (s.slice mid.toNat pre.toNat ++ v.slice (mid.toNat + pre.toNat) (hi.toNat - mid.toNat - pre.toNat))) ∧
    ∀ x, (x < lo.toNat ∨ hi.toNat ≤ x) → (smallSortRest v s lo mid hi pre hv hs hvsz hssz h1 h2).1.1.at' x = v.at' x := by
  unfold smallSortRest
  dsimp only
  have e1 : (lo + pre).toNat = lo.toNat + pre.toNat := toNat_add_of_lt _ _ (by omega)
  have e2 : (mid + pre).toNat = mid.toNat + pre.toNat := toNat_add_of_lt _ _ (by omega)
  -- stage 1: copy v[lo+pre, mid) into s
  have F1 := copyRange_slice (lo + pre) mid v s hssz (by omega) (by omega)
  have Fr1a := copyRange_frame (lo + pre) mid v s hssz (by omega) (by omega) lo.toNat pre.toNat (Or.inl (by omega))
  have Fr1b := copyRange_frame (lo + pre) mid v s hssz (by omega) (by omega) mid.toNat pre.toNat (Or.inr (by omega))
  generalize hS1 : copyRange (lo + pre) mid v s hssz (by omega) (by omega) = S1 at *
  rcases S1 with ⟨S1, hS1s⟩
  dsimp only at F1 Fr1a Fr1b ⊢
  rw [e1] at F1
  have hS1L : Sorted le64 (S1.slice lo.toNat ((lo + pre).toNat - lo.toNat)) := by
    rw [e1, show lo.toNat + pre.toNat - lo.toNat = pre.toNat by omega, Fr1a]; exact hL
  -- stage 2: insert v's part of the left half
  have F2 := insertionSortRange_spec lo mid (mid.toNat - (lo + pre).toNat) (lo + pre) S1 (by rw [hS1s]; exact hssz) (by rw [hS1s]; omega)
    (by omega) rfl (by omega) hS1L
  have Fr2 := insertionSortRange_frame lo mid (lo + pre) S1 (by rw [hS1s]; exact hssz) (by rw [hS1s]; omega) (by omega)
    mid.toNat pre.toNat (Or.inr (by omega)) (by omega) hS1L
  generalize hS2 : insertionSortRange lo mid (lo + pre) S1 (by rw [hS1s]; exact hssz) (by rw [hS1s]; omega) (by omega) = S2 at *
  rcases S2 with ⟨S2, hS2s⟩
  dsimp only at F2 Fr2 ⊢
  obtain ⟨F2, _⟩ := F2
  rw [e1, show lo.toNat + pre.toNat - lo.toNat = pre.toNat by omega, Fr1a, F1] at F2
  -- stage 3: copy v[mid+pre, hi) into s
  have F3 := copyRange_slice (mid + pre) hi v S2 (by rw [hS2s, hS1s]; exact hssz) hv (by rw [hS2s, hS1s]; exact hs)
  have Fr3a := copyRange_frame (mid + pre) hi v S2 (by rw [hS2s, hS1s]; exact hssz) hv (by rw [hS2s, hS1s]; exact hs)
    lo.toNat (mid.toNat - lo.toNat) (Or.inl (by omega))
  have Fr3b := copyRange_frame (mid + pre) hi v S2 (by rw [hS2s, hS1s]; exact hssz) hv (by rw [hS2s, hS1s]; exact hs)
    mid.toNat pre.toNat (Or.inl (by omega))
  generalize hS3 : copyRange (mid + pre) hi v S2 (by rw [hS2s, hS1s]; exact hssz) hv (by rw [hS2s, hS1s]; exact hs) = S3 at *
  rcases S3 with ⟨S3, hS3s⟩
  dsimp only at F3 Fr3a Fr3b ⊢
  rw [e2] at F3
  have hS3R : Sorted le64 (S3.slice mid.toNat ((mid + pre).toNat - mid.toNat)) := by
    rw [e2, show mid.toNat + pre.toNat - mid.toNat = pre.toNat by omega, Fr3b, Fr2, Fr1b]; exact hR
  -- stage 4: insert v's part of the right half
  have F4 := insertionSortRange_spec mid hi (hi.toNat - (mid + pre).toNat) (mid + pre) S3 (by rw [hS3s, hS2s, hS1s]; exact hssz)
    (by rw [hS3s, hS2s, hS1s]; exact hs) (by omega) rfl (by omega) hS3R
  have Fr4 := insertionSortRange_frame mid hi (mid + pre) S3 (by rw [hS3s, hS2s, hS1s]; exact hssz) (by rw [hS3s, hS2s, hS1s]; exact hs)
    (by omega) lo.toNat (mid.toNat - lo.toNat) (Or.inl (by omega)) (by omega) hS3R
  generalize hS4 : insertionSortRange mid hi (mid + pre) S3 (by rw [hS3s, hS2s, hS1s]; exact hssz) (by rw [hS3s, hS2s, hS1s]; exact hs)
    (by omega) = S4 at *
  rcases S4 with ⟨S4, hS4s⟩
  dsimp only at F4 Fr4 ⊢
  obtain ⟨F4, _⟩ := F4
  rw [e2, show mid.toNat + pre.toNat - mid.toNat = pre.toNat by omega, Fr3b, Fr2, Fr1b, F3] at F4
  rw [Fr3a, F2] at Fr4
  -- the two halves of S4 are sorted permutations
  have hL' : Sorted le64 (S4.slice lo.toNat (mid.toNat - lo.toNat)) := by rw [Fr4]; exact insertAll_sorted _ _ hL
  have hR' : Sorted le64 (S4.slice mid.toNat (hi.toNat - mid.toNat)) := by rw [F4]; exact insertAll_sorted _ _ hR
  -- stage 5: merge into v
  have M := mergeKernel_spec lo mid hi S4 v hvsz (by rw [hS4s, hS3s, hS2s, hS1s]; exact hs) hv (by omega) (by omega) hL' hR'
  generalize hV : mergeKernel lo mid hi S4 v hvsz (by rw [hS4s, hS3s, hS2s, hS1s]; exact hs) hv (by omega) (by omega) = V at *
  rcases V with ⟨V, hVs⟩
  dsimp only at M ⊢
  obtain ⟨M, Fm⟩ := M
  refine ⟨?_, ?_, fun x hx => Fm x hx⟩
  · rw [M]; exact merge_sorted le64 le64_trans le64_total hL' hR'
  · rw [M]
    refine (merge_perm le64 _ _).trans (List.Perm.append ?_ ?_)
    · rw [Fr4]
      refine (insertAll_perm _ _).trans ?_
      rw [show mid.toNat - (lo.toNat + pre.toNat) = mid.toNat - lo.toNat - pre.toNat by omega]
    · rw [F4]
      refine (insertAll_perm _ _).trans ?_
      rw [show hi.toNat - (mid.toNat + pre.toNat) = hi.toNat - mid.toNat - pre.toNat by omega]

/-- A slice split into the four pieces the small sort works with. -/
theorem slice_split4 (a : A) (lo mid hi pre : Nat) (h1 : lo + pre ≤ mid) (h2 : mid + pre ≤ hi) :
    a.slice lo (hi - lo) = a.slice lo pre ++ a.slice (lo + pre) (mid - lo - pre) ++
      (a.slice mid pre ++ a.slice (mid + pre) (hi - mid - pre)) := by
  rw [show hi - lo = (pre + (mid - lo - pre)) + (pre + (hi - mid - pre)) by omega, slice_add, slice_add, slice_add,
    show lo + (pre + (mid - lo - pre)) = mid by omega]

/-- `sort4` as a sorted permutation of the four elements. -/
theorem sort4_sorted_perm (lo : UInt64) (a : A) hsz h :
    Sorted le64 ((sort4 lo a hsz h).1.slice lo.toNat 4) ∧ ((sort4 lo a hsz h).1.slice lo.toNat 4).Perm (a.slice lo.toNat 4) := by
  obtain ⟨S, _⟩ := sort4_spec lo a hsz h
  rw [S, slice_four a]
  exact ⟨net4_sorted _ _ _ _, net4_perm _ _ _ _⟩

theorem sort4_frame (lo : UInt64) (a : A) hsz h (off len : Nat) (hd : off + len ≤ lo.toNat ∨ lo.toNat + 4 ≤ off) :
    (sort4 lo a hsz h).1.slice off len = a.slice off len := by
  obtain ⟨_, F⟩ := sort4_spec lo a hsz h
  apply slice_congr; intro t ht; exact F _ (by omega)

theorem mergeKernel_frame (lo mid hi : UInt64) (src dst : A) hsz hs hd hlo hmid (off len : Nat)
    (h : off + len ≤ lo.toNat ∨ hi.toNat ≤ off)
    (hL : Sorted le64 (src.slice lo.toNat (mid.toNat - lo.toNat))) (hR : Sorted le64 (src.slice mid.toNat (hi.toNat - mid.toNat))) :
    (mergeKernel lo mid hi src dst hsz hs hd hlo hmid).1.slice off len = dst.slice off len := by
  obtain ⟨_, F⟩ := mergeKernel_spec lo mid hi src dst hsz hs hd hlo hmid hL hR
  apply slice_congr; intro t ht; exact F _ (by omega)

set_option maxHeartbeats 2000000 in
theorem smallSort_spec (v s : A) (lo hi : UInt64) hv hs hvsz hssz hlo :
    Sorted le64 ((smallSort v s lo hi hv hs hvsz hssz hlo).1.1.slice lo.toNat (hi.toNat - lo.toNat)) ∧
    ((smallSort v s lo hi hv hs hvsz hssz hlo).1.1.slice lo.toNat (hi.toNat - lo.toNat)).Perm (v.slice lo.toNat (hi.toNat - lo.toNat)) ∧
    ∀ x, (x < lo.toNat ∨ hi.toNat ≤ x) → (smallSort v s lo hi hv hs hvsz hssz hlo).1.1.at' x = v.at' x := by
  unfold smallSort
  have hlen : (hi - lo).toNat = hi.toNat - lo.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hlo)
  dsimp only
  split
  · rename_i h2
    have h2 : (hi - lo).toNat < 2 := by have := UInt64.lt_iff_toNat_lt.mp h2; simpa using this
    dsimp only
    exact ⟨sorted_of_length_le_one _ (by simp; omega), List.Perm.refl _, fun _ _ => rfl⟩
  · rename_i h2
    have h2 : 2 ≤ (hi - lo).toNat := by
      have := UInt64.not_lt.mp h2; have := UInt64.le_iff_toNat_le.mp this; simpa using this
    have hhalf : ((hi - lo) / 2).toNat = (hi.toNat - lo.toNat) / 2 := by simp [hlen]
    have hmid : (lo + (hi - lo) / 2).toNat = lo.toNat + (hi.toNat - lo.toNat) / 2 := by
      rw [toNat_add_of_lt _ _ (by rw [hhalf]; omega), hhalf]
    split
    · -- len ≥ 16: two sort8 = four sort4 in place + two merges of 4+4 into s
      rename_i h16
      have h16 : 16 ≤ (hi - lo).toNat := by have := UInt64.le_iff_toNat_le.mp h16; simpa using this
      have e4 : (lo + 4).toNat = lo.toNat + 4 := toNat_add_of_lt _ _ (by simp; omega)
      have e8 : (lo + 8).toNat = lo.toNat + 8 := toNat_add_of_lt _ _ (by simp; omega)
      have m4 : (lo + (hi - lo) / 2 + 4).toNat = (lo + (hi - lo) / 2).toNat + 4 := toNat_add_of_lt _ _ (by simp; omega)
      have m8 : (lo + (hi - lo) / 2 + 8).toNat = (lo + (hi - lo) / 2).toNat + 8 := toNat_add_of_lt _ _ (by simp; omega)
      simp only [castVS_val]
      -- V1 := sort4 lo v
      generalize hV1 : sort4 lo v hvsz (by omega) = V1
      rcases V1 with ⟨V1, hV1s⟩
      have P1 := sort4_sorted_perm lo v hvsz (by omega)
      have F1 := sort4_frame lo v hvsz (by omega)
      rw [hV1] at P1 F1
      dsimp only at P1 F1 ⊢
      -- V2 := sort4 (lo+4) V1
      generalize hV2 : sort4 (lo + 4) V1 (by rw [hV1s]; exact hvsz) (by rw [hV1s]; omega) = V2
      rcases V2 with ⟨V2, hV2s⟩
      have P2 := sort4_sorted_perm (lo + 4) V1 (by rw [hV1s]; exact hvsz) (by rw [hV1s]; omega)
      have F2 := sort4_frame (lo + 4) V1 (by rw [hV1s]; exact hvsz) (by rw [hV1s]; omega)
      rw [hV2] at P2 F2
      dsimp only at P2 F2 ⊢
      rw [e4] at P2 F2
      have V2lo : V2.slice lo.toNat 4 = V1.slice lo.toNat 4 := F2 _ _ (Or.inl (by omega))
      have V1lo4 : V1.slice (lo.toNat + 4) 4 = v.slice (lo.toNat + 4) 4 := F1 _ _ (Or.inr (by omega))
      -- S1 := merge V2[lo, lo+4) and V2[lo+4, lo+8) into s
      have hS1L : Sorted le64 (V2.slice lo.toNat ((lo + 4).toNat - lo.toNat)) := by
        rw [e4, show lo.toNat + 4 - lo.toNat = 4 by omega, V2lo]; exact P1.1
      have hS1R : Sorted le64 (V2.slice (lo + 4).toNat ((lo + 8).toNat - (lo + 4).toNat)) := by
        rw [e4, e8, show lo.toNat + 8 - (lo.toNat + 4) = 4 by omega]; exact P2.1
      generalize hS1 : mergeKernel lo (lo + 4) (lo + 8) V2 s hssz (by rw [hV2s, hV1s]; omega) (by omega) (by omega) (by omega) = S1
      rcases S1 with ⟨S1, hS1s⟩
      have M1 := mergeKernel_spec lo (lo + 4) (lo + 8) V2 s hssz (by rw [hV2s, hV1s]; omega) (by omega) (by omega) (by omega) hS1L hS1R
      rw [hS1] at M1
      dsimp only at M1 ⊢
      obtain ⟨M1, FM1⟩ := M1
      rw [e4, e8, show lo.toNat + 8 - lo.toNat = 8 by omega, show lo.toNat + 4 - lo.toNat = 4 by omega,
        show lo.toNat + 8 - (lo.toNat + 4) = 4 by omega] at M1
      have S1sorted : Sorted le64 (S1.slice lo.toNat 8) := by
        rw [M1]; exact merge_sorted le64 le64_trans le64_total (by rw [V2lo]; exact P1.1) P2.1
      have S1perm : (S1.slice lo.toNat 8).Perm (v.slice lo.toNat 8) := by
        rw [M1, show (8 : Nat) = 4 + 4 from rfl, slice_add v]
        exact (merge_perm le64 _ _).trans (List.Perm.append (by rw [V2lo]; exact P1.2) (P2.2.trans (by rw [V1lo4])))
      -- V2 agrees with v from lo+8 on
      have V2rest : ∀ off len, lo.toNat + 8 ≤ off → V2.slice off len = v.slice off len := fun off len h => by
        rw [F2 _ _ (Or.inr (by omega)), F1 _ _ (Or.inr (by omega))]
      -- V3 := sort4 mid V2, V4 := sort4 (mid+4) V3
      generalize hV3 : sort4 (lo + (hi - lo) / 2) V2 (by rw [hV2s, hV1s]; exact hvsz) (by rw [hV2s, hV1s]; omega) = V3
      rcases V3 with ⟨V3, hV3s⟩
      have P3 := sort4_sorted_perm (lo + (hi - lo) / 2) V2 (by rw [hV2s, hV1s]; exact hvsz) (by rw [hV2s, hV1s]; omega)
      have F3 := sort4_frame (lo + (hi - lo) / 2) V2 (by rw [hV2s, hV1s]; exact hvsz) (by rw [hV2s, hV1s]; omega)
      rw [hV3] at P3 F3
      dsimp only at P3 F3 ⊢
      generalize hV4 : sort4 (lo + (hi - lo) / 2 + 4) V3 (by rw [hV3s, hV2s, hV1s]; exact hvsz) (by rw [hV3s, hV2s, hV1s]; omega) = V4
      rcases V4 with ⟨V4, hV4s⟩
      have P4 := sort4_sorted_perm (lo + (hi - lo) / 2 + 4) V3 (by rw [hV3s, hV2s, hV1s]; exact hvsz) (by rw [hV3s, hV2s, hV1s]; omega)
      have F4 := sort4_frame (lo + (hi - lo) / 2 + 4) V3 (by rw [hV3s, hV2s, hV1s]; exact hvsz) (by rw [hV3s, hV2s, hV1s]; omega)
      rw [hV4] at P4 F4
      dsimp only at P4 F4 ⊢
      rw [m4] at P4 F4
      have V4mid : V4.slice (lo + (hi - lo) / 2).toNat 4 = V3.slice (lo + (hi - lo) / 2).toNat 4 := F4 _ _ (Or.inl (by omega))
      have V3mid4 : V3.slice ((lo + (hi - lo) / 2).toNat + 4) 4 = v.slice ((lo + (hi - lo) / 2).toNat + 4) 4 := by
        rw [F3 _ _ (Or.inr (by omega)), V2rest _ _ (by omega)]
      have V2mid : V2.slice (lo + (hi - lo) / 2).toNat 4 = v.slice (lo + (hi - lo) / 2).toNat 4 := V2rest _ _ (by omega)
      -- S2 := merge V4[mid, mid+4) and V4[mid+4, mid+8) into S1
      have hS2L : Sorted le64 (V4.slice (lo + (hi - lo) / 2).toNat ((lo + (hi - lo) / 2 + 4).toNat - (lo + (hi - lo) / 2).toNat)) := by
        rw [m4, Nat.add_sub_cancel_left, V4mid]; exact P3.1
      have hS2R : Sorted le64 (V4.slice (lo + (hi - lo) / 2 + 4).toNat ((lo + (hi - lo) / 2 + 8).toNat - (lo + (hi - lo) / 2 + 4).toNat)) := by
        rw [m4, m8, show (lo + (hi - lo) / 2).toNat + 8 - ((lo + (hi - lo) / 2).toNat + 4) = 4 by omega]; exact P4.1
      generalize hS2 : mergeKernel (lo + (hi - lo) / 2) (lo + (hi - lo) / 2 + 4) (lo + (hi - lo) / 2 + 8) V4 S1 (by rw [hS1s]; exact hssz)
        (by rw [hV4s, hV3s, hV2s, hV1s]; omega) (by rw [hS1s]; omega) (by omega) (by omega) = S2
      rcases S2 with ⟨S2, hS2s⟩
      have M2 := mergeKernel_spec (lo + (hi - lo) / 2) (lo + (hi - lo) / 2 + 4) (lo + (hi - lo) / 2 + 8) V4 S1 (by rw [hS1s]; exact hssz)
        (by rw [hV4s, hV3s, hV2s, hV1s]; omega) (by rw [hS1s]; omega) (by omega) (by omega) hS2L hS2R
      rw [hS2] at M2
      dsimp only at M2 ⊢
      obtain ⟨M2, FM2⟩ := M2
      rw [m4, m8, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left,
        show (lo + (hi - lo) / 2).toNat + 8 - ((lo + (hi - lo) / 2).toNat + 4) = 4 by omega] at M2
      have S2sorted : Sorted le64 (S2.slice (lo + (hi - lo) / 2).toNat 8) := by
        rw [M2]; exact merge_sorted le64 le64_trans le64_total (by rw [V4mid]; exact P3.1) P4.1
      have S2perm : (S2.slice (lo + (hi - lo) / 2).toNat 8).Perm (v.slice (lo + (hi - lo) / 2).toNat 8) := by
        rw [M2, show (8 : Nat) = 4 + 4 from rfl, slice_add v]
        exact (merge_perm le64 _ _).trans (List.Perm.append (by rw [V4mid]; exact P3.2.trans (by rw [V2mid]))
          (P4.2.trans (by rw [V3mid4])))
      have S2lo : S2.slice lo.toNat 8 = S1.slice lo.toNat 8 := by
        apply slice_congr; intro t ht; exact FM2 _ (Or.inl (by omega))
      -- V4 agrees with v outside the two 8-windows
      have V4rest : ∀ x, ¬ (lo.toNat ≤ x ∧ x < lo.toNat + 8) → ¬ ((lo + (hi - lo) / 2).toNat ≤ x ∧ x < (lo + (hi - lo) / 2).toNat + 8) →
          V4.at' x = v.at' x := by
        intro x hx1 hx2
        have := sort4_spec (lo + (hi - lo) / 2 + 4) V3 (by rw [hV3s, hV2s, hV1s]; exact hvsz) (by rw [hV3s, hV2s, hV1s]; omega)
        rw [hV4] at this
        have h4 := this.2 x (by rw [m4]; omega)
        have := sort4_spec (lo + (hi - lo) / 2) V2 (by rw [hV2s, hV1s]; exact hvsz) (by rw [hV2s, hV1s]; omega)
        rw [hV3] at this
        have h3 := this.2 x (by omega)
        have := sort4_spec (lo + 4) V1 (by rw [hV1s]; exact hvsz) (by rw [hV1s]; omega)
        rw [hV2] at this
        have h2' := this.2 x (by rw [e4]; omega)
        have := sort4_spec lo v hvsz (by omega)
        rw [hV1] at this
        have h1' := this.2 x (by omega)
        dsimp only at h4 h3 h2' h1'
        rw [h4, h3, h2', h1']
      -- the rest of the small sort
      have R := smallSortRest_spec V4 S2 lo (lo + (hi - lo) / 2) hi 8 (by rw [hV4s, hV3s, hV2s, hV1s]; exact hv)
        (by rw [hS2s, hS1s]; exact hs) (by rw [hV4s, hV3s, hV2s, hV1s]; exact hvsz) (by rw [hS2s, hS1s]; exact hssz)
        (by simp; omega) (by simp; omega) (by simpa [S2lo] using S1sorted) (by simpa using S2sorted)
      obtain ⟨RS, RP, RF⟩ := R
      refine ⟨RS, ?_, fun x hx => ?_⟩
      · refine RP.trans ?_
        rw [slice_split4 v lo.toNat (lo + (hi - lo) / 2).toNat hi.toNat 8 (by omega) (by omega)]
        simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
        refine List.Perm.append (List.Perm.append (by rw [S2lo]; exact S1perm) ?_) (List.Perm.append S2perm ?_)
        · rw [slice_congr (a := V4) (b := v) (fun t ht => V4rest _ (by omega) (by omega))]
        · rw [slice_congr (a := V4) (b := v) (fun t ht => V4rest _ (by omega) (by omega))]
      · rw [RF x hx]; exact V4rest x (by omega) (by omega)
    · split
      · -- 8 ≤ len < 16: sort4 on each half in place, copied into s
        rename_i h8
        have h8 : 8 ≤ (hi - lo).toNat := by have := UInt64.le_iff_toNat_le.mp h8; simpa using this
        have e4 : (lo + 4).toNat = lo.toNat + 4 := toNat_add_of_lt _ _ (by simp; omega)
        have m4 : (lo + (hi - lo) / 2 + 4).toNat = (lo + (hi - lo) / 2).toNat + 4 := toNat_add_of_lt _ _ (by simp; omega)
        simp only [castVS_val]
        generalize hV1 : sort4 lo v hvsz (by omega) = V1
        rcases V1 with ⟨V1, hV1s⟩
        have P1 := sort4_sorted_perm lo v hvsz (by omega)
        have F1 := sort4_frame lo v hvsz (by omega)
        rw [hV1] at P1 F1
        dsimp only at P1 F1 ⊢
        generalize hS1 : copyRange lo (lo + 4) V1 s hssz (by rw [hV1s]; omega) (by omega) = S1
        rcases S1 with ⟨S1, hS1s⟩
        have C1 := copyRange_slice lo (lo + 4) V1 s hssz (by rw [hV1s]; omega) (by omega)
        rw [hS1] at C1
        dsimp only at C1 ⊢
        rw [e4, Nat.add_sub_cancel_left] at C1
        generalize hV2 : sort4 (lo + (hi - lo) / 2) V1 (by rw [hV1s]; exact hvsz) (by rw [hV1s]; omega) = V2
        rcases V2 with ⟨V2, hV2s⟩
        have P2 := sort4_sorted_perm (lo + (hi - lo) / 2) V1 (by rw [hV1s]; exact hvsz) (by rw [hV1s]; omega)
        have F2 := sort4_frame (lo + (hi - lo) / 2) V1 (by rw [hV1s]; exact hvsz) (by rw [hV1s]; omega)
        have SP2 := sort4_spec (lo + (hi - lo) / 2) V1 (by rw [hV1s]; exact hvsz) (by rw [hV1s]; omega)
        rw [hV2] at P2 F2 SP2
        dsimp only at P2 F2 SP2 ⊢
        have V1mid : V1.slice (lo + (hi - lo) / 2).toNat 4 = v.slice (lo + (hi - lo) / 2).toNat 4 := F1 _ _ (Or.inr (by omega))
        generalize hS2 : copyRange (lo + (hi - lo) / 2) (lo + (hi - lo) / 2 + 4) V2 S1 (by rw [hS1s]; exact hssz)
          (by rw [hV2s, hV1s]; omega) (by rw [hS1s]; omega) = S2
        rcases S2 with ⟨S2, hS2s⟩
        have C2 := copyRange_slice (lo + (hi - lo) / 2) (lo + (hi - lo) / 2 + 4) V2 S1 (by rw [hS1s]; exact hssz)
          (by rw [hV2s, hV1s]; omega) (by rw [hS1s]; omega)
        have C2f := copyRange_frame (lo + (hi - lo) / 2) (lo + (hi - lo) / 2 + 4) V2 S1 (by rw [hS1s]; exact hssz)
          (by rw [hV2s, hV1s]; omega) (by rw [hS1s]; omega) lo.toNat 4 (Or.inl (by omega))
        rw [hS2] at C2 C2f
        dsimp only at C2 C2f ⊢
        rw [m4, Nat.add_sub_cancel_left] at C2
        have V2rest : ∀ x, ¬ (lo.toNat ≤ x ∧ x < lo.toNat + 4) → ¬ ((lo + (hi - lo) / 2).toNat ≤ x ∧ x < (lo + (hi - lo) / 2).toNat + 4) →
            V2.at' x = v.at' x := by
          intro x hx1 hx2
          have := sort4_spec lo v hvsz (by omega)
          rw [hV1] at this
          dsimp only at this
          rw [SP2.2 x (by omega), this.2 x (by omega)]
        have R := smallSortRest_spec V2 S2 lo (lo + (hi - lo) / 2) hi 4 (by rw [hV2s, hV1s]; exact hv)
          (by rw [hS2s, hS1s]; exact hs) (by rw [hV2s, hV1s]; exact hvsz) (by rw [hS2s, hS1s]; exact hssz)
          (by simp; omega) (by simp; omega) (by simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; rw [C2f, C1]; exact P1.1)
          (by simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; rw [C2]; exact P2.1)
        obtain ⟨RS, RP, RF⟩ := R
        refine ⟨RS, ?_, fun x hx => ?_⟩
        · refine RP.trans ?_
          rw [slice_split4 v lo.toNat (lo + (hi - lo) / 2).toNat hi.toNat 4 (by omega) (by omega)]
          simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
          refine List.Perm.append (List.Perm.append (by rw [C2f, C1]; exact P1.2) ?_)
            (List.Perm.append (by rw [C2]; exact P2.2.trans (by rw [V1mid])) ?_)
          · rw [slice_congr (a := V2) (b := v) (fun t ht => V2rest _ (by omega) (by omega))]
          · rw [slice_congr (a := V2) (b := v) (fun t ht => V2rest _ (by omega) (by omega))]
        · rw [RF x hx]; exact V2rest x (by omega) (by omega)
      · -- 2 ≤ len < 8: one element of each half copied into s
        have e1 : (lo + 1).toNat = lo.toNat + 1 := toNat_add_of_lt _ _ (by simp; omega)
        have m1 : (lo + (hi - lo) / 2 + 1).toNat = (lo + (hi - lo) / 2).toNat + 1 := toNat_add_of_lt _ _ (by simp; omega)
        simp only [castVS_val]
        generalize hS1 : copyRange lo (lo + 1) v s hssz (by omega) (by omega) = S1
        rcases S1 with ⟨S1, hS1s⟩
        have C1 := copyRange_slice lo (lo + 1) v s hssz (by omega) (by omega)
        rw [hS1] at C1
        dsimp only at C1 ⊢
        rw [e1, Nat.add_sub_cancel_left] at C1
        generalize hS2 : copyRange (lo + (hi - lo) / 2) (lo + (hi - lo) / 2 + 1) v S1 (by rw [hS1s]; exact hssz) (by omega)
          (by rw [hS1s]; omega) = S2
        rcases S2 with ⟨S2, hS2s⟩
        have C2 := copyRange_slice (lo + (hi - lo) / 2) (lo + (hi - lo) / 2 + 1) v S1 (by rw [hS1s]; exact hssz) (by omega)
          (by rw [hS1s]; omega)
        have C2f := copyRange_frame (lo + (hi - lo) / 2) (lo + (hi - lo) / 2 + 1) v S1 (by rw [hS1s]; exact hssz) (by omega)
          (by rw [hS1s]; omega) lo.toNat 1 (Or.inl (by omega))
        rw [hS2] at C2 C2f
        dsimp only at C2 C2f ⊢
        rw [m1, Nat.add_sub_cancel_left] at C2
        have R := smallSortRest_spec v S2 lo (lo + (hi - lo) / 2) hi 1 hv (by rw [hS2s, hS1s]; exact hs) hvsz
          (by rw [hS2s, hS1s]; exact hssz) (by simp; omega) (by simp; omega)
          (by simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; exact sorted_of_length_le_one _ (by simp))
          (by simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; exact sorted_of_length_le_one _ (by simp))
        obtain ⟨RS, RP, RF⟩ := R
        refine ⟨RS, ?_, fun x hx => RF x hx⟩
        refine RP.trans ?_
        rw [slice_split4 v lo.toNat (lo + (hi - lo) / 2).toNat hi.toNat 1 (by omega) (by omega)]
        simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
        rw [C2f, C1, C2]

/-! ## The stable partition -/

/-- `copyRev`: `dst[k + j] = src[last - j]` for `j ∈ [j0, n)`, everything else unchanged. -/
theorem copyRev_spec (src : A) (k last n : UInt64) :
    ∀ (m : Nat) (j : UInt64) (dst : A) hdsz hk hl hls hj, m = n.toNat - j.toNat →
    (∀ x, j.toNat ≤ x → x < n.toNat → (copyRev src dst k last j n hdsz hk hl hls hj).1.at' (k.toNat + x) = src.at' (last.toNat - x)) ∧
    (∀ x, (x < k.toNat + j.toNat ∨ k.toNat + n.toNat ≤ x) → (copyRev src dst k last j n hdsz hk hl hls hj).1.at' x = dst.at' x) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro j dst hdsz hk hl hls hj hm
  rw [copyRev]
  split
  · rename_i h
    have h : j.toNat < n.toNat := h
    have hb := UInt64.toNat_lt last
    have ekj : (k + j).toNat = k.toNat + j.toNat := toNat_add_of_lt _ _ (by omega)
    have elj : (last - j).toNat = last.toNat - j.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))
    have ej1 : (j + 1).toNat = j.toNat + 1 := toNat_add_of_lt _ _ (by simp; omega)
    dsimp only
    simp only [castSize_val]
    obtain ⟨A1, B1⟩ := ih (n.toNat - (j + 1).toNat) (by omega) (j + 1)
      (dst.set (k + j) (src.get (last - j) (by rw [elj]; omega)) (by rw [ekj]; omega))
      (by simp; exact hdsz) (by simp; exact hk) hl hls (by omega) rfl
    refine ⟨fun x hx1 hx2 => ?_, fun x hx => ?_⟩
    · by_cases hxj : x = j.toNat
      · subst hxj
        rw [B1 _ (Or.inl (by omega)), at'_set, if_pos ekj, get_eq_at', elj]
      · rw [A1 x (by omega) hx2]
    · rw [B1 x (by omega)]
      exact at'_set_ne _ _ _ _ _ (by omega)
  · rename_i h
    have h : ¬ j.toNat < n.toNat := h
    exact ⟨fun x hx1 hx2 => by omega, fun _ _ => rfl⟩

/-- Reading a slice through `copyRev`: the reversed source slice. -/
theorem copyRev_slice (src dst : A) (k last n : UInt64) hdsz hk hl hls hj :
    (copyRev src dst k last 0 n hdsz hk hl hls hj).1.slice k.toNat n.toNat = (src.slice (last.toNat + 1 - n.toNat) n.toNat).reverse := by
  obtain ⟨A1, _⟩ := copyRev_spec src k last n n.toNat 0 dst hdsz hk hl hls hj rfl
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [slice, List.getElem_map, List.getElem_range, List.getElem_reverse, List.length_map, List.length_range]
    have hi : i < n.toNat := by simpa using h1
    rw [A1 i (Nat.zero_le _) hi]
    congr 1; omega

theorem copyRev_frame (src dst : A) (k last n : UInt64) hdsz hk hl hls hj (off len : Nat)
    (h : off + len ≤ k.toNat ∨ k.toNat + n.toNat ≤ off) :
    (copyRev src dst k last 0 n hdsz hk hl hls hj).1.slice off len = dst.slice off len := by
  obtain ⟨_, B1⟩ := copyRev_spec src k last n n.toNat 0 dst hdsz hk hl hls hj rfl
  apply slice_congr; intro t ht; exact B1 _ (by simp; omega)

/-- The two parts of a partition, as list filters. -/
def leftPart (eq : Bool) (pivot : UInt64) (l : List UInt64) : List UInt64 := l.filter (goesLeft eq pivot)
def rightPart (eq : Bool) (pivot : UInt64) (l : List UInt64) : List UInt64 := l.filter (fun x => !goesLeft eq pivot x)

theorem leftPart_append (eq : Bool) (pivot : UInt64) (l₁ l₂ : List UInt64) :
    leftPart eq pivot (l₁ ++ l₂) = leftPart eq pivot l₁ ++ leftPart eq pivot l₂ := List.filter_append _ _
theorem rightPart_append (eq : Bool) (pivot : UInt64) (l₁ l₂ : List UInt64) :
    rightPart eq pivot (l₁ ++ l₂) = rightPart eq pivot l₁ ++ rightPart eq pivot l₂ := List.filter_append _ _
theorem leftPart_singleton_pos (eq : Bool) (pivot x : UInt64) (h : goesLeft eq pivot x = true) : leftPart eq pivot [x] = [x] := by
  simp [leftPart, h]
theorem leftPart_singleton_neg (eq : Bool) (pivot x : UInt64) (h : goesLeft eq pivot x = false) : leftPart eq pivot [x] = [] := by
  simp [leftPart, h]
theorem rightPart_singleton_pos (eq : Bool) (pivot x : UInt64) (h : goesLeft eq pivot x = true) : rightPart eq pivot [x] = [] := by
  simp [rightPart, h]
theorem rightPart_singleton_neg (eq : Bool) (pivot x : UInt64) (h : goesLeft eq pivot x = false) : rightPart eq pivot [x] = [x] := by
  simp [rightPart, h]
theorem leftPart_append_rightPart_perm (eq : Bool) (pivot : UInt64) (l : List UInt64) :
    (leftPart eq pivot l ++ rightPart eq pivot l).Perm l := List.filter_append_perm _ _

/-- The scan invariant: the left part so far at the front of `s[lo, ..)`, the right part so far at the
    back of `s[.., hi)` in reverse. -/
theorem partScan_spec (v : A) (lo hi pivot : UInt64) (eq : Bool) :
    ∀ (m : Nat) (s : A) (i nl : UInt64) hv hs hssz hi1 hi2 hnl, m = hi.toNat - i.toNat →
    s.slice lo.toNat nl.toNat = leftPart eq pivot (v.slice lo.toNat (i.toNat - lo.toNat)) →
    (s.slice (hi.toNat - (i.toNat - lo.toNat - nl.toNat)) (i.toNat - lo.toNat - nl.toNat)).reverse
        = rightPart eq pivot (v.slice lo.toNat (i.toNat - lo.toNat)) →
    (partScan v s lo hi i nl pivot eq hv hs hssz hi1 hi2 hnl).1.1.slice lo.toNat
        (partScan v s lo hi i nl pivot eq hv hs hssz hi1 hi2 hnl).1.2.toNat
      = leftPart eq pivot (v.slice lo.toNat (hi.toNat - lo.toNat)) ∧
    ((partScan v s lo hi i nl pivot eq hv hs hssz hi1 hi2 hnl).1.1.slice
        (lo.toNat + (partScan v s lo hi i nl pivot eq hv hs hssz hi1 hi2 hnl).1.2.toNat)
        (hi.toNat - lo.toNat - (partScan v s lo hi i nl pivot eq hv hs hssz hi1 hi2 hnl).1.2.toNat)).reverse
      = rightPart eq pivot (v.slice lo.toNat (hi.toNat - lo.toNat)) ∧
    ∀ x, (x < lo.toNat ∨ hi.toNat ≤ x) → (partScan v s lo hi i nl pivot eq hv hs hssz hi1 hi2 hnl).1.1.at' x = s.at' x := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro s i nl hv hs hssz hi1 hi2 hnl hm HL HR
  rw [partScan]
  split
  · rename_i h
    have hlt : i.toNat < hi.toNat := UInt64.lt_iff_toNat_lt.mp h
    have hb := UInt64.toNat_lt hi
    dsimp only
    -- the element and where it goes
    have er : (i - lo - nl).toNat = i.toNat - lo.toNat - nl.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hi1)]; omega)),
        UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hi1)]
    have e1 : (lo + nl).toNat = lo.toNat + nl.toNat := toNat_add_of_lt _ _ (by omega)
    have e0 : (hi - 1).toNat = hi.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
    have e2 : (hi - 1 - (i - lo - nl)).toNat = hi.toNat - 1 - (i.toNat - lo.toNat - nl.toNat) := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [e0, er]; omega)), e0, er]
    have ei : (i + 1).toNat = i.toNat + 1 := toNat_add_of_lt _ _ (by simp; omega)
    have hx : v.get i (by omega) = v.at' i.toNat := get_eq_at' _ _ _
    have hsl : v.slice lo.toNat (i.toNat + 1 - lo.toNat) = v.slice lo.toNat (i.toNat - lo.toNat) ++ [v.at' i.toNat] := by
      rw [show i.toNat + 1 - lo.toNat = (i.toNat - lo.toNat) + 1 by omega, slice_succ,
        show lo.toNat + (i.toNat - lo.toNat) = i.toNat by omega]
    -- the recursive call, on either destination (the conditionals stay inside the terms; they are
    -- evaluated only in the proof-free side conditions)
    have hg : v.get i (by omega) = v.at' i.toNat := hx
    by_cases hgl : goesLeft eq pivot (v.at' i.toNat) = true
    · have hgl' : goesLeft eq pivot (v.get i (by omega)) = true := by rw [hg]; exact hgl
      have en : (nl + (if goesLeft eq pivot (v.get i (by omega)) = true then (1 : UInt64) else 0)).toNat = nl.toNat + 1 := by
        rw [if_pos hgl']; exact toNat_add_of_lt _ _ (by simp; omega)
      have eidx : (if goesLeft eq pivot (v.get i (by omega)) = true then lo + nl else hi - 1 - (i - lo - nl)).toNat = lo.toNat + nl.toNat := by
        rw [if_pos hgl', e1]
      have H := ih (hi.toNat - (i + 1).toNat) (by omega)
        (s.set (if goesLeft eq pivot (v.get i (by omega)) = true then lo + nl else hi - 1 - (i - lo - nl)) (v.get i (by omega))
          (by rw [eidx]; omega))
        (i + 1) (nl + (if goesLeft eq pivot (v.get i (by omega)) = true then (1 : UInt64) else 0)) hv (by simp; exact hs)
        (by simp; exact hssz) (by omega) (by omega) (by rw [en, ei]; omega) rfl
        (by -- left part grows by x
          rw [en, ei, slice_succ, at'_set, if_pos eidx, slice_set_of_not_mem _ _ _ _ _ _ (Or.inr (by rw [eidx]; omega)), HL, hsl,
            leftPart_append, leftPart_singleton_pos _ _ _ hgl, hg])
        (by -- right part unchanged
          rw [en, ei, hsl, rightPart_append, rightPart_singleton_pos _ _ _ hgl, List.append_nil, ← HR,
            show i.toNat + 1 - lo.toNat - (nl.toNat + 1) = i.toNat - lo.toNat - nl.toNat by omega,
            slice_set_of_not_mem _ _ _ _ _ _ (Or.inl (by rw [eidx]; omega))])
      exact ⟨H.1, H.2.1, fun x hx => (H.2.2 x hx).trans (at'_set_ne _ _ _ _ _ (by rw [eidx]; omega))⟩
    · have hglf : goesLeft eq pivot (v.at' i.toNat) = false := by simpa using hgl
      have hgl' : ¬ goesLeft eq pivot (v.get i (by omega)) = true := by rw [hg]; simp [hglf]
      have en : (nl + (if goesLeft eq pivot (v.get i (by omega)) = true then (1 : UInt64) else 0)).toNat = nl.toNat := by
        rw [if_neg hgl']; simp
      have eidx : (if goesLeft eq pivot (v.get i (by omega)) = true then lo + nl else hi - 1 - (i - lo - nl)).toNat =
          hi.toNat - 1 - (i.toNat - lo.toNat - nl.toNat) := by
        rw [if_neg hgl', e2]
      have H := ih (hi.toNat - (i + 1).toNat) (by omega)
        (s.set (if goesLeft eq pivot (v.get i (by omega)) = true then lo + nl else hi - 1 - (i - lo - nl)) (v.get i (by omega))
          (by rw [eidx]; omega))
        (i + 1) (nl + (if goesLeft eq pivot (v.get i (by omega)) = true then (1 : UInt64) else 0)) hv (by simp; exact hs)
        (by simp; exact hssz) (by omega) (by omega) (by rw [en, ei]; omega) rfl
        (by -- left part unchanged
          rw [en, ei, hsl, leftPart_append, leftPart_singleton_neg _ _ _ hglf, List.append_nil, ← HL,
            slice_set_of_not_mem _ _ _ _ _ _ (Or.inr (by rw [eidx]; omega))])
        (by -- right part grows by x at the front (reversed: at the end)
          rw [en, ei, hsl, rightPart_append, rightPart_singleton_neg _ _ _ hglf,
            show i.toNat + 1 - lo.toNat - nl.toNat = (i.toNat - lo.toNat - nl.toNat) + 1 by omega,
            show hi.toNat - (i.toNat - lo.toNat - nl.toNat + 1) = (hi.toNat - 1 - (i.toNat - lo.toNat - nl.toNat)) by omega,
            slice_cons, List.reverse_cons,
            show hi.toNat - 1 - (i.toNat - lo.toNat - nl.toNat) + 1 = hi.toNat - (i.toNat - lo.toNat - nl.toNat) by omega,
            slice_set_of_not_mem _ _ _ _ _ _ (Or.inl (by rw [eidx]; omega)), HR, at'_set, if_pos eidx, hg])
      exact ⟨H.1, H.2.1, fun x hx => (H.2.2 x hx).trans (at'_set_ne _ _ _ _ _ (by rw [eidx]; omega))⟩
  · rename_i h
    have h : ¬ i.toNat < hi.toNat := h
    have hi' : i.toNat = hi.toNat := by omega
    dsimp only
    rw [hi'] at HL HR
    refine ⟨HL, ?_, fun _ _ => rfl⟩
    rw [← HR]
    congr 2; omega

theorem stablePartition_spec (v s : A) (lo hi pivot : UInt64) (eq : Bool) hv hs hvsz hssz hlt :
    (stablePartition v s lo hi pivot eq hv hs hvsz hssz hlt).1.2.1.slice lo.toNat (hi.toNat - lo.toNat) =
      leftPart eq pivot (v.slice lo.toNat (hi.toNat - lo.toNat)) ++ rightPart eq pivot (v.slice lo.toNat (hi.toNat - lo.toNat)) ∧
    (stablePartition v s lo hi pivot eq hv hs hvsz hssz hlt).1.1.toNat = (leftPart eq pivot (v.slice lo.toNat (hi.toNat - lo.toNat))).length ∧
    ∀ x, (x < lo.toNat ∨ hi.toNat ≤ x) → (stablePartition v s lo hi pivot eq hv hs hvsz hssz hlt).1.2.1.at' x = v.at' x := by
  unfold stablePartition
  have hlo : lo.toNat ≤ hi.toNat := by omega
  dsimp only
  -- the scan
  have P := partScan_spec v lo hi pivot eq (hi.toNat - lo.toNat) s lo 0 hv hs hssz (by omega) hlo (by simp) rfl
    (by simp [leftPart]) (by simp [rightPart])
  generalize hP : partScan v s lo hi lo 0 pivot eq hv hs hssz (by omega) hlo (by simp) = R at P
  rcases R with ⟨⟨S1, nl⟩, hS1s, _, hnl⟩
  dsimp only at P hS1s hnl ⊢
  obtain ⟨A, B, _⟩ := P
  have hnl' : nl.toNat ≤ hi.toNat - lo.toNat := by simpa using hnl
  have e : (lo + nl).toNat = lo.toNat + nl.toNat := toNat_add_of_lt _ _ (by omega)
  -- copy the left part back
  have C1 := copyRange_slice lo (lo + nl) S1 v hvsz (by rw [hS1s, e]; omega) (by rw [e]; omega)
  have C1f := copyRange_spec (lo + nl) S1 ((lo + nl).toNat - lo.toNat) lo v hvsz (by rw [hS1s, e]; omega) (by rw [e]; omega) rfl
  generalize hV1 : copyRange lo (lo + nl) S1 v hvsz (by rw [hS1s, e]; omega) (by rw [e]; omega) = V1 at C1 C1f
  rcases V1 with ⟨V1, hV1s⟩
  dsimp only at C1 C1f ⊢
  rw [e, Nat.add_sub_cancel_left] at C1
  obtain ⟨_, C1f⟩ := C1f
  -- copy the right part back, reversed
  have ehi1 : (hi - 1).toNat = hi.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
  have e1 : (hi - lo).toNat = hi.toNat - lo.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hlo)
  have erest : (hi - lo - nl).toNat = hi.toNat - lo.toNat - nl.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [e1]; omega)), e1]
  have C2 := copyRev_slice S1 V1 (lo + nl) (hi - 1) (hi - lo - nl) (by rw [hV1s]; exact hvsz) (by rw [hV1s, e, erest]; omega)
    (by rw [erest, ehi1]; omega) (by rw [hS1s, ehi1]; omega) (by simp)
  have C2f := copyRev_spec S1 (lo + nl) (hi - 1) (hi - lo - nl) (hi - lo - nl).toNat 0 V1 (by rw [hV1s]; exact hvsz)
    (by rw [hV1s, e, erest]; omega) (by rw [erest, ehi1]; omega) (by rw [hS1s, ehi1]; omega) (by simp) rfl
  generalize hV2 : copyRev S1 V1 (lo + nl) (hi - 1) 0 (hi - lo - nl) (by rw [hV1s]; exact hvsz) (by rw [hV1s, e, erest]; omega)
    (by rw [erest, ehi1]; omega) (by rw [hS1s, ehi1]; omega) (by simp) = V2 at C2 C2f
  rcases V2 with ⟨V2, hV2s⟩
  dsimp only at C2 C2f ⊢
  obtain ⟨_, C2f⟩ := C2f
  rw [e, erest, ehi1, show hi.toNat - 1 + 1 - (hi.toNat - lo.toNat - nl.toNat) = lo.toNat + nl.toNat by omega, B] at C2
  have V2lo : V2.slice lo.toNat nl.toNat = V1.slice lo.toNat nl.toNat := by
    apply slice_congr; intro t ht; exact C2f _ (Or.inl (by simp; omega))
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · have hsplit : V2.slice lo.toNat (hi.toNat - lo.toNat) = V2.slice lo.toNat nl.toNat ++ V2.slice (lo.toNat + nl.toNat) (hi.toNat - lo.toNat - nl.toNat) := by
      rw [← slice_add]; congr 1; omega
    rw [hsplit, V2lo, C1, A, C2]
  · rw [← A, length_slice]
  · rw [C2f x (by rw [e, erest]; omega), C1f x (by rw [e]; omega)]

end DriftSort
