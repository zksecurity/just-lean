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

/-! ## Logical merge -/

theorem logicalMerge_spec (quick : Quick) (HQ : QuickSpec quick) (v s : A) (lo mid hi scratchLen : UInt64) (lsorted rsorted : Bool)
    hv hs hvsz hssz hlo hmid
    (hL : lsorted = true → Sorted le64 (v.slice lo.toNat (mid.toNat - lo.toNat)))
    (hR : rsorted = true → Sorted le64 (v.slice mid.toNat (hi.toNat - mid.toNat))) :
    ((logicalMerge quick v s lo mid hi scratchLen lsorted rsorted hv hs hvsz hssz hlo hmid).1.1 = true →
      Sorted le64 ((logicalMerge quick v s lo mid hi scratchLen lsorted rsorted hv hs hvsz hssz hlo hmid).1.2.1.slice lo.toNat (hi.toNat - lo.toNat))) ∧
    ((logicalMerge quick v s lo mid hi scratchLen lsorted rsorted hv hs hvsz hssz hlo hmid).1.2.1.slice lo.toNat (hi.toNat - lo.toNat)).Perm
      (v.slice lo.toNat (hi.toNat - lo.toNat)) ∧
    ∀ x, (x < lo.toNat ∨ hi.toNat ≤ x) → (logicalMerge quick v s lo mid hi scratchLen lsorted rsorted hv hs hvsz hssz hlo hmid).1.2.1.at' x = v.at' x := by
  unfold logicalMerge
  dsimp only
  split
  · -- physical merge: sort the unsorted sides, then merge
    -- stage 1: the left run
    have S1 : ∀ (r : VS v s), (r = if lsorted then ⟨(v, s), rfl, rfl⟩ else quick v s lo mid (by omega) (by omega) hvsz hssz hlo) →
        Sorted le64 (r.1.1.slice lo.toNat (mid.toNat - lo.toNat)) ∧
        (r.1.1.slice lo.toNat (mid.toNat - lo.toNat)).Perm (v.slice lo.toNat (mid.toNat - lo.toNat)) ∧
        ∀ x, (x < lo.toNat ∨ mid.toNat ≤ x) → r.1.1.at' x = v.at' x := by
      intro r hr
      rw [hr]
      split
      · rename_i h; exact ⟨hL h, List.Perm.refl _, fun _ _ => rfl⟩
      · exact HQ v s lo mid (by omega) (by omega) hvsz hssz hlo
    generalize hR1 : (if lsorted then ⟨(v, s), rfl, rfl⟩ else quick v s lo mid (by omega) (by omega) hvsz hssz hlo : VS v s) = R1
    have S1 := S1 R1 hR1.symm
    rcases R1 with ⟨⟨v1, s1⟩, hv1, hs1⟩
    dsimp only at S1 ⊢
    obtain ⟨S1a, S1b, S1c⟩ := S1
    -- stage 2: the right run
    have S2 : ∀ (r : VS v1 s1), (r = if rsorted then ⟨(v1, s1), rfl, rfl⟩ else
          quick v1 s1 mid hi (by rw [hv1]; exact hv) (by rw [hs1]; exact hs) (by rw [hv1]; exact hvsz) (by rw [hs1]; exact hssz) hmid) →
        Sorted le64 (r.1.1.slice mid.toNat (hi.toNat - mid.toNat)) ∧
        (r.1.1.slice mid.toNat (hi.toNat - mid.toNat)).Perm (v1.slice mid.toNat (hi.toNat - mid.toNat)) ∧
        ∀ x, (x < mid.toNat ∨ hi.toNat ≤ x) → r.1.1.at' x = v1.at' x := by
      intro r hr
      rw [hr]
      split
      · rename_i h
        refine ⟨?_, List.Perm.refl _, fun _ _ => rfl⟩
        rw [slice_congr (fun t ht => S1c _ (Or.inr (by omega)))]; exact hR h
      · exact HQ v1 s1 mid hi _ _ _ _ hmid
    generalize hR2 : (if rsorted then ⟨(v1, s1), rfl, rfl⟩ else
        quick v1 s1 mid hi (by rw [hv1]; exact hv) (by rw [hs1]; exact hs) (by rw [hv1]; exact hvsz) (by rw [hs1]; exact hssz) hmid : VS v1 s1) = R2
    have S2 := S2 R2 hR2.symm
    rcases R2 with ⟨⟨v2, s2⟩, hv2, hs2⟩
    dsimp only at S2 ⊢
    obtain ⟨S2a, S2b, S2c⟩ := S2
    have v2lo : v2.slice lo.toNat (mid.toNat - lo.toNat) = v1.slice lo.toNat (mid.toNat - lo.toNat) := by
      apply slice_congr; intro t ht; exact S2c _ (Or.inl (by omega))
    -- stage 3: the merge
    have M := mergeRuns_spec v2 s2 lo mid hi (by rw [hv2, hv1]; exact hv) (by rw [hs2, hs1]; exact hs) (by rw [hv2, hv1]; exact hvsz)
      (by rw [hs2, hs1]; exact hssz) hlo hmid (by rw [v2lo]; exact S1a) S2a
    generalize hR3 : mergeRuns v2 s2 lo mid hi (by rw [hv2, hv1]; exact hv) (by rw [hs2, hs1]; exact hs) (by rw [hv2, hv1]; exact hvsz)
      (by rw [hs2, hs1]; exact hssz) hlo hmid = R3 at M
    rcases R3 with ⟨⟨v3, s3⟩, hv3, hs3⟩
    dsimp only at M ⊢
    obtain ⟨M1, M2⟩ := M
    have hsplit : ∀ c : A, c.slice lo.toNat (hi.toNat - lo.toNat) = c.slice lo.toNat (mid.toNat - lo.toNat) ++ c.slice mid.toNat (hi.toNat - mid.toNat) := by
      intro c
      have h1 : c.slice lo.toNat (hi.toNat - lo.toNat) = c.slice lo.toNat ((mid.toNat - lo.toNat) + (hi.toNat - mid.toNat)) := by congr 1; omega
      rw [h1, slice_add, show lo.toNat + (mid.toNat - lo.toNat) = mid.toNat by omega]
    refine ⟨fun _ => ?_, ?_, fun x hx => ?_⟩
    · rw [M1]; exact merge_sorted le64 le64_trans le64_total (by rw [v2lo]; exact S1a) S2a
    · rw [M1]
      refine (merge_perm le64 _ _).trans ?_
      rw [hsplit v]
      refine List.Perm.append (by rw [v2lo]; exact S1b) (S2b.trans ?_)
      rw [slice_congr (fun t ht => S1c _ (Or.inr (by omega)))]
    · rw [M2 x hx, S2c x (by omega), S1c x (by omega)]
  · exact ⟨fun h => by simp at h, List.Perm.refl _, fun _ _ => rfl⟩

/-! ## The run stack -/

/-- `RunsOK rs e a`: the runs `rs` (top first) tile `a` downward from position `e`; the sorted ones are sorted. -/
def RunsOK : List Run → Nat → A → Prop
  | [], _, _ => True
  | r :: rs, e, a => r.len.toNat ≤ e ∧ (r.sorted = true → Sorted le64 (a.slice (e - r.len.toNat) r.len.toNat)) ∧ RunsOK rs (e - r.len.toNat) a

def runsSum (rs : List Run) : Nat := (rs.map (fun r => r.len.toNat)).sum
@[simp] theorem runsSum_nil : runsSum [] = 0 := rfl
@[simp] theorem runsSum_cons (r : Run) (rs : List Run) : runsSum (r :: rs) = r.len.toNat + runsSum rs := by simp [runsSum]

theorem stackSum_eq_runsSum (st : Stack) : stackSum st = runsSum (st.map Prod.fst) := by
  induction st with
  | nil => rfl
  | cons e st ih => simp [stackSum_cons, runsSum_cons, ih]

/-- `RunsOK` only looks at the positions `[e - runsSum rs, e)`. -/
theorem RunsOK_congr (rs : List Run) (e : Nat) (a b : A) (h : ∀ x, e - runsSum rs ≤ x → x < e → b.at' x = a.at' x)
    (hok : RunsOK rs e a) : RunsOK rs e b := by
  induction rs generalizing e with
  | nil => trivial
  | cons r rs ih =>
    obtain ⟨h1, h2, h3⟩ := hok
    refine ⟨h1, fun hs => ?_, ih (e - r.len.toNat) (fun x hx1 hx2 => h x (by simp at hx1 ⊢; omega) (by omega)) h3⟩
    rw [slice_congr (fun t ht => h _ (by simp; omega) (by omega))]
    exact h2 hs

theorem RunsOK_sum_le (rs : List Run) (e : Nat) (a : A) (hok : RunsOK rs e a) : runsSum rs ≤ e := by
  induction rs generalizing e with
  | nil => simp
  | cons r rs ih =>
    obtain ⟨h1, _, h3⟩ := hok
    have := ih _ h3
    simp; omega

theorem collapse_spec (quick : Quick) (HQ : QuickSpec quick) (lo scanIdx scratchLen desired : UInt64) :
    ∀ (st : Stack) (prevRun : Run) (v s : A) hv hs hvsz hssz hsum,
    RunsOK (prevRun :: st.map Prod.fst) (lo.toNat + scanIdx.toNat) v →
    RunsOK ((collapse quick lo scanIdx scratchLen desired prevRun st v s hv hs hvsz hssz hsum).1.1 ::
        (collapse quick lo scanIdx scratchLen desired prevRun st v s hv hs hvsz hssz hsum).1.2.1.map Prod.fst)
      (lo.toNat + scanIdx.toNat) (collapse quick lo scanIdx scratchLen desired prevRun st v s hv hs hvsz hssz hsum).1.2.2.1 ∧
    ((collapse quick lo scanIdx scratchLen desired prevRun st v s hv hs hvsz hssz hsum).1.2.2.1.slice lo.toNat scanIdx.toNat).Perm
      (v.slice lo.toNat scanIdx.toNat) ∧
    ∀ x, (x < lo.toNat ∨ lo.toNat + scanIdx.toNat ≤ x) →
      (collapse quick lo scanIdx scratchLen desired prevRun st v s hv hs hvsz hssz hsum).1.2.2.1.at' x = v.at' x := by
  intro st
  induction st with
  | nil =>
    intro prevRun v s hv hs hvsz hssz hsum hok
    rw [collapse]
    exact ⟨hok, List.Perm.refl _, fun _ _ => rfl⟩
  | cons e rest ih =>
    intro prevRun v s hv hs hvsz hssz hsum hok
    obtain ⟨left, depth⟩ := e
    rw [collapse]
    dsimp only
    split
    · rename_i hc
      have hbnd := UInt64.toNat_lt scanIdx
      have hsum' : left.len.toNat + stackSum rest + prevRun.len.toNat = scanIdx.toNat := by simpa [Nat.add_assoc] using hsum
      obtain ⟨h1, h2, h3, h4, h5⟩ := hok
      have hml : (left.len + prevRun.len).toNat = left.len.toNat + prevRun.len.toNat := toNat_add_of_lt _ _ (by omega)
      have hen : (lo + scanIdx).toNat = lo.toNat + scanIdx.toNat := toNat_add_of_lt _ _ (by omega)
      have hst : (lo + scanIdx - (left.len + prevRun.len)).toNat = lo.toNat + scanIdx.toNat - (left.len + prevRun.len).toNat := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hen]; omega)), hen]
      have hmi : (lo + scanIdx - (left.len + prevRun.len) + left.len).toNat = (lo + scanIdx - (left.len + prevRun.len)).toNat + left.len.toNat :=
        toNat_add_of_lt _ _ (by omega)
      -- the physical / logical merge of `left` and `prevRun`
      have L := logicalMerge_spec quick HQ v s (lo + scanIdx - (left.len + prevRun.len)) (lo + scanIdx - (left.len + prevRun.len) + left.len)
        (lo + scanIdx) scratchLen left.sorted prevRun.sorted (by omega) (by omega) hvsz hssz (by omega) (by omega)
        (by intro hs'; rw [hmi, hst, hml, Nat.add_sub_cancel_left]
            have := h4 hs'
            rwa [show lo.toNat + scanIdx.toNat - prevRun.len.toNat - left.len.toNat = lo.toNat + scanIdx.toNat - (left.len.toNat + prevRun.len.toNat) by omega] at this)
        (by intro hs'; rw [hen, hmi, hst, hml,
              show lo.toNat + scanIdx.toNat - (left.len.toNat + prevRun.len.toNat) + left.len.toNat = lo.toNat + scanIdx.toNat - prevRun.len.toNat by omega,
              show lo.toNat + scanIdx.toNat - (lo.toNat + scanIdx.toNat - prevRun.len.toNat) = prevRun.len.toNat by omega]
            exact h2 hs')
      generalize hM : logicalMerge quick v s (lo + scanIdx - (left.len + prevRun.len)) (lo + scanIdx - (left.len + prevRun.len) + left.len)
        (lo + scanIdx) scratchLen left.sorted prevRun.sorted (by omega) (by omega) hvsz hssz (by omega) (by omega) = M at L
      rcases M with ⟨⟨flag, v1, s1⟩, hv1, hs1⟩
      dsimp only at L ⊢
      obtain ⟨L1, L2, L3⟩ := L
      rw [hen, hst, hml] at L1 L2 L3
      -- the merged run is fine, the rest of the stack is untouched
      have hok' : RunsOK (⟨left.len + prevRun.len, flag⟩ :: rest.map Prod.fst) (lo.toNat + scanIdx.toNat) v1 := by
        refine ⟨by simp only [hml]; omega, fun hf => ?_, ?_⟩
        · simp only [hml]
          have := L1 hf
          rwa [show lo.toNat + scanIdx.toNat - (lo.toNat + scanIdx.toNat - (left.len.toNat + prevRun.len.toNat)) = left.len.toNat + prevRun.len.toNat by omega] at this
        · simp only [hml]
          refine RunsOK_congr _ _ v v1 (fun x hx1 hx2 => L3 x (Or.inl (by omega))) ?_
          rwa [show lo.toNat + scanIdx.toNat - (left.len.toNat + prevRun.len.toNat) = lo.toNat + scanIdx.toNat - prevRun.len.toNat - left.len.toNat by omega]
      have IH := ih ⟨left.len + prevRun.len, flag⟩ v1 s1 (by rw [hv1]; exact hv) (by rw [hs1]; exact hs) (by rw [hv1]; exact hvsz)
        (by rw [hs1]; exact hssz) (by simp only [hml]; omega) hok'
      generalize hC : collapse quick lo scanIdx scratchLen desired ⟨left.len + prevRun.len, flag⟩ rest v1 s1 (by rw [hv1]; exact hv)
        (by rw [hs1]; exact hs) (by rw [hv1]; exact hvsz) (by rw [hs1]; exact hssz) (by simp only [hml]; omega) = C at IH
      rcases C with ⟨⟨r1, st1, v2, s2⟩, hv2, hs2, hsum2⟩
      dsimp only at IH ⊢
      obtain ⟨IH1, IH2, IH3⟩ := IH
      refine ⟨IH1, IH2.trans ?_, fun x hx => (IH3 x hx).trans (L3 x (by omega))⟩
      exact perm_of_sub v v1 lo.toNat scanIdx.toNat (lo.toNat + scanIdx.toNat - (left.len.toNat + prevRun.len.toNat))
        (lo.toNat + scanIdx.toNat - (lo.toNat + scanIdx.toNat - (left.len.toNat + prevRun.len.toNat))) (by omega) (by omega) L2
        (fun x hx => L3 x (by omega))
    · exact ⟨hok, List.Perm.refl _, fun _ _ => rfl⟩

theorem driftLoop_spec (quick : Quick) (HQ : QuickSpec quick) (lo len scratchLen minGood scale : UInt64) (eager : Bool) :
    ∀ (m : Nat) (scanIdx : UInt64) (prevRun : Run) (st : Stack) (v s : A) hv hs hvsz hssz hmg hscan hsum, m = len.toNat - scanIdx.toNat →
    RunsOK (prevRun :: st.map Prod.fst) (lo.toNat + scanIdx.toNat) v →
    Sorted le64 ((driftLoop quick lo len scratchLen minGood scale eager scanIdx prevRun st v s hv hs hvsz hssz hmg hscan hsum).1.1.slice lo.toNat len.toNat) ∧
    ((driftLoop quick lo len scratchLen minGood scale eager scanIdx prevRun st v s hv hs hvsz hssz hmg hscan hsum).1.1.slice lo.toNat len.toNat).Perm
      (v.slice lo.toNat len.toNat) ∧
    ∀ x, (x < lo.toNat ∨ lo.toNat + len.toNat ≤ x) →
      (driftLoop quick lo len scratchLen minGood scale eager scanIdx prevRun st v s hv hs hvsz hssz hmg hscan hsum).1.1.at' x = v.at' x := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro scanIdx prevRun st v s hv hs hvsz hssz hmg hscan hsum hm hok
  have hbnd := UInt64.toNat_lt len
  rw [driftLoop]
  split
  · rename_i h
    have h : scanIdx.toNat < len.toNat := h
    have es : (lo + scanIdx).toNat = lo.toNat + scanIdx.toNat := toNat_add_of_lt _ _ (by omega)
    have el : (lo + len).toNat = lo.toNat + len.toNat := toNat_add_of_lt _ _ (by omega)
    dsimp only
    -- the next run
    have C := createRun_spec v s (lo + scanIdx) (lo + len) minGood eager (by rw [el]; exact hv) (by rw [el]; exact hs) hvsz hssz (by omega) hmg
    generalize hR : createRun v s (lo + scanIdx) (lo + len) minGood eager (by rw [el]; exact hv) (by rw [el]; exact hs) hvsz hssz (by omega) hmg = R at C
    rcases R with ⟨⟨nextRun, v1, s1⟩, hv1, hs1, hpos, hle⟩
    dsimp only at C hv1 hs1 hpos hle ⊢
    obtain ⟨C1, C2, C3⟩ := C
    rw [es] at C1
    rw [es, el] at C2 C3 hle
    -- the old runs are untouched
    have hok1 : RunsOK (prevRun :: st.map Prod.fst) (lo.toNat + scanIdx.toNat) v1 :=
      RunsOK_congr _ _ v v1 (fun x _ hx2 => C3 x (Or.inl hx2)) hok
    -- collapse
    have K := collapse_spec quick HQ lo scanIdx scratchLen (mergeTreeDepth (scanIdx - prevRun.len) scanIdx (scanIdx + nextRun.len) scale)
      st prevRun v1 s1 (by rw [hv1]; omega) (by rw [hs1]; omega) (by rw [hv1]; exact hvsz) (by rw [hs1]; exact hssz) hsum hok1
    generalize hK : collapse quick lo scanIdx scratchLen (mergeTreeDepth (scanIdx - prevRun.len) scanIdx (scanIdx + nextRun.len) scale)
      prevRun st v1 s1 (by rw [hv1]; omega) (by rw [hs1]; omega) (by rw [hv1]; exact hvsz) (by rw [hs1]; exact hssz) hsum = K' at K
    rcases K' with ⟨⟨prevRun', st', v2, s2⟩, hv2, hs2, hsum'⟩
    dsimp only at K hv2 hs2 hsum' ⊢
    simp only [castVS_val]
    obtain ⟨K1, K2, K3⟩ := K
    have esn : (scanIdx + nextRun.len).toNat = scanIdx.toNat + nextRun.len.toNat := toNat_add_of_lt _ _ (by omega)
    -- the invariant for the next iteration
    have hok2 : RunsOK (nextRun :: ((prevRun', mergeTreeDepth (scanIdx - prevRun.len) scanIdx (scanIdx + nextRun.len) scale) :: st').map Prod.fst)
        (lo.toNat + (scanIdx + nextRun.len).toNat) v2 := by
      refine ⟨by rw [esn]; omega, fun hs' => ?_, ?_⟩
      · rw [esn, show lo.toNat + (scanIdx.toNat + nextRun.len.toNat) - nextRun.len.toNat = lo.toNat + scanIdx.toNat by omega,
          slice_congr (fun t ht => K3 _ (Or.inr (by omega)))]
        exact C1 hs'
      · rw [esn, show lo.toNat + (scanIdx.toNat + nextRun.len.toNat) - nextRun.len.toNat = lo.toNat + scanIdx.toNat by omega]
        exact K1
    have IH := ih (len.toNat - (scanIdx + nextRun.len).toNat) (by rw [esn]; omega) (scanIdx + nextRun.len) nextRun
      ((prevRun', mergeTreeDepth (scanIdx - prevRun.len) scanIdx (scanIdx + nextRun.len) scale) :: st') v2 s2
      (by rw [hv2, hv1]; exact hv) (by rw [hs2, hs1]; exact hs) (by rw [hv2, hv1]; exact hvsz) (by rw [hs2, hs1]; exact hssz) hmg
      (by rw [esn]; omega) (by simp only [stackSum_cons, esn]; omega) rfl hok2
    generalize hD : driftLoop quick lo len scratchLen minGood scale eager (scanIdx + nextRun.len) nextRun
      ((prevRun', mergeTreeDepth (scanIdx - prevRun.len) scanIdx (scanIdx + nextRun.len) scale) :: st') v2 s2
      (by rw [hv2, hv1]; exact hv) (by rw [hs2, hs1]; exact hs) (by rw [hv2, hv1]; exact hvsz) (by rw [hs2, hs1]; exact hssz) hmg
      (by rw [esn]; omega) (by simp only [stackSum_cons, esn]; omega) = D at IH
    rcases D with ⟨⟨v3, s3⟩, hv3, hs3⟩
    dsimp only at IH ⊢
    obtain ⟨IH1, IH2, IH3⟩ := IH
    refine ⟨IH1, IH2.trans ?_, fun x hx => (IH3 x hx).trans ((K3 x (by omega)).trans (C3 x (by omega)))⟩
    -- v2 ~ v1 on the prefix, v1 ~ v on the suffix
    refine (perm_of_sub v1 v2 lo.toNat len.toNat lo.toNat scanIdx.toNat (Nat.le_refl _) (by omega) K2 K3).trans ?_
    exact perm_of_sub v v1 lo.toNat len.toNat (lo.toNat + scanIdx.toNat) (lo.toNat + len.toNat - (lo.toNat + scanIdx.toNat)) (by omega) (by omega) C2
      (fun x hx => C3 x (by omega))
  · rename_i h
    have h : ¬ scanIdx.toNat < len.toNat := h
    have hsl : scanIdx.toNat = len.toNat := by omega
    dsimp only
    have K := collapse_spec quick HQ lo scanIdx scratchLen 0 st prevRun v s (by omega) (by omega) hvsz hssz hsum hok
    generalize hK : collapse quick lo scanIdx scratchLen 0 prevRun st v s (by omega) (by omega) hvsz hssz hsum = K' at K
    rcases K' with ⟨⟨prevRun', st', v2, s2⟩, hv2, hs2, hsum'⟩
    dsimp only at K hv2 hs2 hsum' ⊢
    obtain ⟨K1, K2, K3⟩ := K
    rw [hsl] at K2 K3
    split
    · rename_i hfin
      obtain ⟨hsorted, hlen⟩ := hfin
      refine ⟨?_, K2, K3⟩
      have := K1.2.1 hsorted
      rwa [hlen, hsl, Nat.add_sub_cancel] at this
    · have el : (lo + len).toNat = lo.toNat + len.toNat := toNat_add_of_lt _ _ (by omega)
      simp only [castVS_val]
      have Q := HQ v2 s2 lo (lo + len) (by rw [hv2, el]; exact hv) (by rw [hs2, el]; exact hs) (by rw [hv2]; exact hvsz)
        (by rw [hs2]; exact hssz) (by omega)
      generalize hQ : quick v2 s2 lo (lo + len) (by rw [hv2, el]; exact hv) (by rw [hs2, el]; exact hs) (by rw [hv2]; exact hvsz)
        (by rw [hs2]; exact hssz) (by omega) = Qr at Q
      rcases Qr with ⟨⟨v3, s3⟩, hv3, hs3⟩
      dsimp only at Q ⊢
      rw [el, Nat.add_sub_cancel_left] at Q
      exact ⟨Q.1, Q.2.1.trans K2, fun x hx => (Q.2.2 x hx).trans (K3 x hx)⟩

theorem driftSort_spec (quick : Quick) (HQ : QuickSpec quick) (v s : A) (lo hi scratchLen : UInt64) (eager : Bool) hv hs hvsz hssz hlo :
    Sorted le64 ((driftSort quick v s lo hi scratchLen eager hv hs hvsz hssz hlo).1.1.slice lo.toNat (hi.toNat - lo.toNat)) ∧
    ((driftSort quick v s lo hi scratchLen eager hv hs hvsz hssz hlo).1.1.slice lo.toNat (hi.toNat - lo.toNat)).Perm
      (v.slice lo.toNat (hi.toNat - lo.toNat)) ∧
    ∀ x, (x < lo.toNat ∨ hi.toNat ≤ x) → (driftSort quick v s lo hi scratchLen eager hv hs hvsz hssz hlo).1.1.at' x = v.at' x := by
  unfold driftSort
  have hlen : (hi - lo).toNat = hi.toNat - lo.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hlo)
  dsimp only
  split
  · rename_i h2
    have h2 : (hi - lo).toNat < 2 := by have := UInt64.lt_iff_toNat_lt.mp h2; simpa using this
    exact ⟨sorted_of_length_le_one _ (by simp; omega), List.Perm.refl _, fun _ _ => rfl⟩
  · -- the minimum good run length, spelled out as in the definition
    have hmg : 0 < (if (if hi - lo ≤ minSqrtRunLen * minSqrtRunLen then min (hi - lo - (hi - lo) / 2) minSqrtRunLen else sqrtApprox (hi - lo)) == 0
        then 1 else (if hi - lo ≤ minSqrtRunLen * minSqrtRunLen then min (hi - lo - (hi - lo) / 2) minSqrtRunLen else sqrtApprox (hi - lo))).toNat := by
      generalize (if hi - lo ≤ minSqrtRunLen * minSqrtRunLen then min (hi - lo - (hi - lo) / 2) minSqrtRunLen else sqrtApprox (hi - lo)) = mg0
      split
      · decide
      · rename_i h; have : mg0 ≠ 0 := by simpa using h
        have : mg0.toNat ≠ 0 := fun c => this (UInt64.toNat.inj (by simpa using c))
        omega
    have D := driftLoop_spec quick HQ lo (hi - lo) scratchLen
      (if (if hi - lo ≤ minSqrtRunLen * minSqrtRunLen then min (hi - lo - (hi - lo) / 2) minSqrtRunLen else sqrtApprox (hi - lo)) == 0
        then 1 else (if hi - lo ≤ minSqrtRunLen * minSqrtRunLen then min (hi - lo - (hi - lo) / 2) minSqrtRunLen else sqrtApprox (hi - lo)))
      (mergeTreeScaleFactor (hi - lo)) eager ((hi - lo).toNat - (0 : UInt64).toNat) 0
      ⟨0, true⟩ [] v s (by omega) (by omega) hvsz hssz hmg (Nat.zero_le _) rfl rfl (by simp [RunsOK, Sorted])
    simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.add_zero, hlen] at D
    exact ⟨D.1, D.2.1, fun x hx => D.2.2 x (by omega)⟩

theorem driftSortEager_spec (v s : A) (lo hi scratchLen : UInt64) hv hs hvsz hssz hlo :
    Sorted le64 ((driftSortEager v s lo hi scratchLen hv hs hvsz hssz hlo).1.1.slice lo.toNat (hi.toNat - lo.toNat)) ∧
    ((driftSortEager v s lo hi scratchLen hv hs hvsz hssz hlo).1.1.slice lo.toNat (hi.toNat - lo.toNat)).Perm
      (v.slice lo.toNat (hi.toNat - lo.toNat)) ∧
    ∀ x, (x < lo.toNat ∨ hi.toNat ≤ x) → (driftSortEager v s lo hi scratchLen hv hs hvsz hssz hlo).1.1.at' x = v.at' x :=
  driftSort_spec insertionQuick insertionQuick_spec v s lo hi scratchLen true hv hs hvsz hssz hlo

/-! ## The quicksort -/

theorem mem_slice_of_lt (a : A) (off len i : Nat) (h1 : off ≤ i) (h2 : i < off + len) : a.at' i ∈ a.slice off len := by
  simp only [slice, List.mem_map, List.mem_range]
  exact ⟨i - off, by omega, by congr 1; omega⟩

theorem sorted_of_const (p : UInt64) : ∀ (l : List UInt64), (∀ x ∈ l, x = p) → Sorted le64 l := by
  intro l
  induction l with
  | nil => intro _; simp [Sorted]
  | cons x l ih =>
    intro h
    refine List.pairwise_cons.mpr ⟨fun y hy => ?_, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))⟩
    rw [h x (List.mem_cons_self ..), h y (List.mem_cons_of_mem _ hy)]
    simp [le64]

theorem mem_leftPart {eq : Bool} {p x : UInt64} {l : List UInt64} : x ∈ leftPart eq p l ↔ x ∈ l ∧ goesLeft eq p x = true := List.mem_filter
theorem mem_rightPart {eq : Bool} {p x : UInt64} {l : List UInt64} : x ∈ rightPart eq p l ↔ x ∈ l ∧ goesLeft eq p x = false := by
  simp [rightPart, List.mem_filter]

theorem goesLeft_false (p x : UInt64) : goesLeft false p x = decide (x < p) := rfl
theorem goesLeft_true (p x : UInt64) : goesLeft true p x = decide (x ≤ p) := rfl

set_option maxHeartbeats 4000000 in
theorem quicksort_spec (scratchLen : UInt64) :
    ∀ (m : Nat) (v s : A) (lo hi limit : UInt64) (hasLA : Bool) (la : UInt64) hv hs hvsz hssz hlo, m = hi.toNat - lo.toNat →
    (hasLA = true → ∀ x ∈ v.slice lo.toNat (hi.toNat - lo.toNat), la ≤ x) →
    Sorted le64 ((quicksort v s lo hi scratchLen limit hasLA la hv hs hvsz hssz hlo).1.1.slice lo.toNat (hi.toNat - lo.toNat)) ∧
    ((quicksort v s lo hi scratchLen limit hasLA la hv hs hvsz hssz hlo).1.1.slice lo.toNat (hi.toNat - lo.toNat)).Perm
      (v.slice lo.toNat (hi.toNat - lo.toNat)) ∧
    ∀ x, (x < lo.toNat ∨ hi.toNat ≤ x) → (quicksort v s lo hi scratchLen limit hasLA la hv hs hvsz hssz hlo).1.1.at' x = v.at' x := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro v s lo hi limit hasLA la hv hs hvsz hssz hlo hm hpre
  have hbnd := UInt64.toNat_lt hi
  have hlen : (hi - lo).toNat = hi.toNat - lo.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hlo)
  rw [quicksort]
  dsimp only
  split
  · exact smallSort_spec v s lo hi hv hs hvsz hssz hlo
  · rename_i h32
    have h32 : 32 < (hi - lo).toNat := by
      have := UInt64.not_le.mp h32; have := UInt64.lt_iff_toNat_lt.mp this; simpa [smallSortThreshold] using this
    split
    · exact driftSortEager_spec v s lo hi scratchLen hv hs hvsz hssz hlo
    · -- the pivot
      generalize hPP : choosePivot v lo hi hvsz hv (by omega) = PP
      rcases PP with ⟨pp, hpp1, hpp2⟩
      dsimp only
      have hpiv : v.get pp (by omega) = v.at' pp.toNat := get_eq_at' _ _ _
      have hpmem : v.at' pp.toNat ∈ v.slice lo.toNat (hi.toNat - lo.toNat) := mem_slice_of_lt v _ _ _ hpp1 (by omega)
      generalize hpv : v.get pp (by omega) = pivot at hpiv
      -- the first partition (skipped when the pivot equals the left ancestor)
      have P1 : ∀ (r : { r : UInt64 × A × A // r.2.1.size = v.size ∧ r.2.2.size = s.size ∧ r.1.toNat ≤ hi.toNat - lo.toNat }),
          (r = if (hasLA && decide (pivot ≤ la)) = true then ⟨(0, v, s), rfl, rfl, by simp⟩
            else stablePartition v s lo hi pivot false hv hs hvsz hssz (by omega)) →
          (r.1.2.1.slice lo.toNat (hi.toNat - lo.toNat)).Perm (v.slice lo.toNat (hi.toNat - lo.toNat)) ∧
          (∀ x, (x < lo.toNat ∨ hi.toNat ≤ x) → r.1.2.1.at' x = v.at' x) ∧
          ((hasLA && decide (pivot ≤ la)) = true → r.1.2.1 = v ∧ r.1.1 = 0) ∧
          ((hasLA && decide (pivot ≤ la)) = false →
            r.1.2.1.slice lo.toNat (hi.toNat - lo.toNat) =
              leftPart false pivot (v.slice lo.toNat (hi.toNat - lo.toNat)) ++ rightPart false pivot (v.slice lo.toNat (hi.toNat - lo.toNat)) ∧
            r.1.1.toNat = (leftPart false pivot (v.slice lo.toNat (hi.toNat - lo.toNat))).length) := by
        intro r hr
        rw [hr]
        split
        · rename_i hc
          exact ⟨List.Perm.refl _, fun _ _ => rfl, fun _ => ⟨rfl, rfl⟩, fun hf => by rw [hc] at hf; cases hf⟩
        · rename_i hc
          obtain ⟨S1, S2, S3⟩ := stablePartition_spec v s lo hi pivot false hv hs hvsz hssz (by omega)
          refine ⟨?_, S3, fun ht => absurd ht hc, fun _ => ⟨S1, S2⟩⟩
          rw [S1]; exact leftPart_append_rightPart_perm _ _ _
      generalize hP1 : (if (hasLA && decide (pivot ≤ la)) = true then ⟨(0, v, s), rfl, rfl, by simp⟩
        else stablePartition v s lo hi pivot false hv hs hvsz hssz (by omega) :
        { r : UInt64 × A × A // r.2.1.size = v.size ∧ r.2.2.size = s.size ∧ r.1.toNat ≤ hi.toNat - lo.toNat }) = R1
      have P1 := P1 R1 hP1.symm
      rcases R1 with ⟨⟨nl, v1, s1⟩, hv1, hs1, hnl⟩
      dsimp only at P1 hv1 hs1 hnl ⊢
      obtain ⟨P1a, P1b, P1c, P1d⟩ := P1
      have hpmem1 : pivot ∈ v1.slice lo.toNat (hi.toNat - lo.toNat) := P1a.mem_iff.mpr (hpiv ▸ hpmem)
      have hsplit1 : v1.slice lo.toNat (hi.toNat - lo.toNat) = v1.slice lo.toNat nl.toNat ++ v1.slice (lo.toNat + nl.toNat) (hi.toNat - lo.toNat - nl.toNat) := by
        rw [← slice_add]; congr 1; omega
      split
      · -- equal-element partition: everything ≤ pivot in this range equals the pivot
        rename_i heq
        have Hall : ∀ x ∈ v1.slice lo.toNat (hi.toNat - lo.toNat), pivot ≤ x := by
          intro x hx
          by_cases hpe : (hasLA && decide (pivot ≤ la)) = true
          · obtain ⟨hvv, _⟩ := P1c hpe
            rw [hvv] at hx
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hpe
            exact UInt64.le_trans hpe.2 (hpre hpe.1 x hx)
          · have hpe' : (hasLA && decide (pivot ≤ la)) = false := by simpa using hpe
            obtain ⟨E1, E2⟩ := P1d hpe'
            have hnl0 : nl = 0 := by
              simp only [Bool.or_eq_true, hpe', Bool.false_eq_true, false_or, beq_iff_eq] at heq; exact heq
            rw [hnl0] at E2
            have hL : leftPart false pivot (v.slice lo.toNat (hi.toNat - lo.toNat)) = [] := List.eq_nil_of_length_eq_zero (by simpa using E2.symm)
            rw [E1, hL, List.nil_append] at hx
            have := (mem_rightPart.mp hx).2
            rw [goesLeft_false] at this
            simpa using this
        -- the second partition
        have P2 := stablePartition_spec v1 s1 lo hi pivot true (by rw [hv1]; exact hv) (by rw [hs1]; exact hs) (by rw [hv1]; exact hvsz)
          (by rw [hs1]; exact hssz) (by omega)
        generalize hP2 : stablePartition v1 s1 lo hi pivot true (by rw [hv1]; exact hv) (by rw [hs1]; exact hs) (by rw [hv1]; exact hvsz)
          (by rw [hs1]; exact hssz) (by omega) = R2 at P2
        rcases R2 with ⟨⟨midEq, v2, s2⟩, hv2, hs2, hme⟩
        dsimp only at P2 hv2 hs2 hme ⊢
        obtain ⟨Q1, Q2, Q3⟩ := P2
        have hpmem2 : pivot ∈ leftPart true pivot (v1.slice lo.toNat (hi.toNat - lo.toNat)) :=
          mem_leftPart.mpr ⟨hpmem1, by rw [goesLeft_true]; simp⟩
        split
        · rename_i hpos
          have em : (lo + midEq).toNat = lo.toNat + midEq.toNat := toNat_add_of_lt _ _ (by omega)
          have IH := ih (hi.toNat - (lo + midEq).toNat) (by rw [em]; omega) v2 s2 (lo + midEq) hi (limit - 1) false 0
            (by rw [hv2, hv1]; exact hv) (by rw [hs2, hs1]; exact hs) (by rw [hv2, hv1]; exact hvsz) (by rw [hs2, hs1]; exact hssz)
            (by rw [em]; omega) rfl (fun h => by simp at h)
          generalize hQ : quicksort v2 s2 (lo + midEq) hi scratchLen (limit - 1) false 0 (by rw [hv2, hv1]; exact hv) (by rw [hs2, hs1]; exact hs)
            (by rw [hv2, hv1]; exact hvsz) (by rw [hs2, hs1]; exact hssz) (by rw [em]; omega) = Q at IH
          rcases Q with ⟨⟨v3, s3⟩, hv3, hs3⟩
          dsimp only at IH ⊢
          simp only [castVS_val]
          obtain ⟨I1, I2, I3⟩ := IH
          rw [em] at I1 I2 I3
          rw [show hi.toNat - (lo.toNat + midEq.toNat) = hi.toNat - lo.toNat - midEq.toNat by omega] at I1 I2
          -- the left part of v2 (all equal to the pivot) is untouched by the recursion
          have hsplit2 : v2.slice lo.toNat (hi.toNat - lo.toNat) =
              v2.slice lo.toNat midEq.toNat ++ v2.slice (lo.toNat + midEq.toNat) (hi.toNat - lo.toNat - midEq.toNat) := by
            rw [← slice_add]; congr 1; omega
          have hLR := Q1
          rw [hsplit2] at hLR
          have hLen : (v2.slice lo.toNat midEq.toNat).length = (leftPart true pivot (v1.slice lo.toNat (hi.toNat - lo.toNat))).length := by
            rw [length_slice, Q2]
          obtain ⟨hLeq, hReq⟩ := List.append_inj hLR hLen
          have v3lo : v3.slice lo.toNat midEq.toNat = v2.slice lo.toNat midEq.toNat := by
            apply slice_congr; intro t ht; exact I3 _ (Or.inl (by omega))
          have hsplit3 : v3.slice lo.toNat (hi.toNat - lo.toNat) =
              v3.slice lo.toNat midEq.toNat ++ v3.slice (lo.toNat + midEq.toNat) (hi.toNat - lo.toNat - midEq.toNat) := by
            rw [← slice_add]; congr 1; omega
          have hconst : ∀ x ∈ v2.slice lo.toNat midEq.toNat, x = pivot := by
            intro x hx
            rw [hLeq] at hx
            obtain ⟨hx1, hx2⟩ := mem_leftPart.mp hx
            rw [goesLeft_true] at hx2
            exact UInt64.le_antisymm (by simpa using hx2) (Hall x hx1)
          refine ⟨?_, ?_, fun x hx => (I3 x (by omega)).trans ((Q3 x hx).trans (P1b x hx))⟩
          · rw [hsplit3, Sorted, List.pairwise_append]
            refine ⟨by rw [v3lo]; exact sorted_of_const pivot _ hconst, I1, fun x hx y hy => ?_⟩
            rw [v3lo] at hx
            rw [hconst x hx]
            have hy' := I2.mem_iff.mp hy
            rw [hReq] at hy'
            have := (mem_rightPart.mp hy').2
            rw [goesLeft_true] at this
            simp only [le64, decide_eq_true_eq]
            exact UInt64.le_of_lt (by simpa using this)
          · refine (perm_of_sub v2 v3 lo.toNat (hi.toNat - lo.toNat) (lo.toNat + midEq.toNat) (hi.toNat - lo.toNat - midEq.toNat)
              (by omega) (by omega) I2 (fun x hx => I3 x (by omega))).trans ?_
            rw [Q1]
            exact (leftPart_append_rightPart_perm _ _ _).trans P1a
        · -- dead branch: the pivot itself is in the left part
          rename_i hpos
          exfalso
          apply hpos
          rw [Q2]
          exact List.length_pos_of_mem hpmem2
      · -- the pivot is neither the left ancestor nor the minimum: two-sided recursion
        rename_i hne
        have hpe' : (hasLA && decide (pivot ≤ la)) = false := by
          simp only [Bool.or_eq_true, not_or] at hne; simpa using hne.1
        have hnl0 : nl ≠ 0 := by
          simp only [Bool.or_eq_true, not_or, beq_iff_eq] at hne; exact hne.2
        obtain ⟨E1, E2⟩ := P1d hpe'
        have hLen : (v1.slice lo.toNat nl.toNat).length = (leftPart false pivot (v.slice lo.toNat (hi.toNat - lo.toNat))).length := by
          rw [length_slice, E2]
        rw [hsplit1] at E1
        obtain ⟨hLeq, hReq⟩ := List.append_inj E1 hLen
        have hpmemR : pivot ∈ rightPart false pivot (v.slice lo.toNat (hi.toNat - lo.toNat)) :=
          mem_rightPart.mpr ⟨hpiv ▸ hpmem, by rw [goesLeft_false]; simp⟩
        split
        · rename_i hok
          have en : (lo + nl).toNat = lo.toNat + nl.toNat := toNat_add_of_lt _ _ (by omega)
          -- right part first
          have IH1 := ih (hi.toNat - (lo + nl).toNat) (by rw [en]; omega) v1 s1 (lo + nl) hi (limit - 1) true pivot
            (by rw [hv1]; exact hv) (by rw [hs1]; exact hs) (by rw [hv1]; exact hvsz) (by rw [hs1]; exact hssz) (by rw [en]; omega) rfl
            (by intro _ x hx
                rw [en, show hi.toNat - (lo.toNat + nl.toNat) = hi.toNat - lo.toNat - nl.toNat by omega, hReq] at hx
                have := (mem_rightPart.mp hx).2
                rw [goesLeft_false] at this
                simpa using this)
          generalize hQ1 : quicksort v1 s1 (lo + nl) hi scratchLen (limit - 1) true pivot (by rw [hv1]; exact hv) (by rw [hs1]; exact hs)
            (by rw [hv1]; exact hvsz) (by rw [hs1]; exact hssz) (by rw [en]; omega) = Q1 at IH1
          rcases Q1 with ⟨⟨v2, s2⟩, hv2, hs2⟩
          dsimp only at IH1 ⊢
          obtain ⟨I1, I2, I3⟩ := IH1
          rw [en] at I1 I2 I3
          have v2lo : v2.slice lo.toNat nl.toNat = v1.slice lo.toNat nl.toNat := by
            apply slice_congr; intro t ht; exact I3 _ (Or.inl (by omega))
          -- then the left part, with the original ancestor
          have IH2 := ih ((lo + nl).toNat - lo.toNat) (by rw [en]; omega) v2 s2 lo (lo + nl) (limit - 1) hasLA la
            (by rw [hv2, hv1, en]; omega) (by rw [hs2, hs1, en]; omega) (by rw [hv2, hv1]; exact hvsz) (by rw [hs2, hs1]; exact hssz)
            (by rw [en]; omega) rfl
            (by intro hla x hx
                have hx2 : x ∈ v2.slice lo.toNat nl.toNat := by simpa [en] using hx
                rw [v2lo, hLeq] at hx2
                exact hpre hla x (mem_leftPart.mp hx2).1)
          generalize hQ2 : quicksort v2 s2 lo (lo + nl) scratchLen (limit - 1) hasLA la (by rw [hv2, hv1, en]; omega) (by rw [hs2, hs1, en]; omega)
            (by rw [hv2, hv1]; exact hvsz) (by rw [hs2, hs1]; exact hssz) (by rw [en]; omega) = Q2 at IH2
          rcases Q2 with ⟨⟨v3, s3⟩, hv3, hs3⟩
          dsimp only at IH2 ⊢
          simp only [castVS_val]
          obtain ⟨J1, J2, J3⟩ := IH2
          rw [en] at J1 J2 J3
          rw [Nat.add_sub_cancel_left] at J1 J2
          have v3hi : v3.slice (lo.toNat + nl.toNat) (hi.toNat - lo.toNat - nl.toNat) = v2.slice (lo.toNat + nl.toNat) (hi.toNat - lo.toNat - nl.toNat) := by
            apply slice_congr; intro t ht; exact J3 _ (Or.inr (by omega))
          have hsplit3 : v3.slice lo.toNat (hi.toNat - lo.toNat) =
              v3.slice lo.toNat nl.toNat ++ v3.slice (lo.toNat + nl.toNat) (hi.toNat - lo.toNat - nl.toNat) := by
            rw [← slice_add]; congr 1; omega
          have I2' : (v2.slice (lo.toNat + nl.toNat) (hi.toNat - lo.toNat - nl.toNat)).Perm (v1.slice (lo.toNat + nl.toNat) (hi.toNat - lo.toNat - nl.toNat)) := by
            have := I2
            rwa [show hi.toNat - (lo.toNat + nl.toNat) = hi.toNat - lo.toNat - nl.toNat by omega] at this
          refine ⟨?_, ?_, fun x hx => (J3 x (by omega)).trans ((I3 x (by omega)).trans (P1b x hx))⟩
          · rw [hsplit3, Sorted, List.pairwise_append, v3hi]
            refine ⟨J1, by have := I1; rwa [show hi.toNat - (lo.toNat + nl.toNat) = hi.toNat - lo.toNat - nl.toNat by omega] at this,
              fun x hx y hy => ?_⟩
            have hx' := J2.mem_iff.mp hx
            rw [v2lo, hLeq] at hx'
            have hxl := (mem_leftPart.mp hx').2
            rw [goesLeft_false] at hxl
            have hy' := I2'.mem_iff.mp hy
            rw [hReq] at hy'
            have hyr := (mem_rightPart.mp hy').2
            rw [goesLeft_false] at hyr
            simp only [le64, decide_eq_true_eq]
            exact UInt64.le_of_lt (UInt64.lt_of_lt_of_le (by simpa using hxl) (by simpa using hyr))
          · refine (perm_of_sub v2 v3 lo.toNat (hi.toNat - lo.toNat) lo.toNat nl.toNat (Nat.le_refl _) (by omega) J2 J3).trans ?_
            refine (perm_of_sub v1 v2 lo.toNat (hi.toNat - lo.toNat) (lo.toNat + nl.toNat) (hi.toNat - lo.toNat - nl.toNat) (by omega) (by omega) I2'
              (fun x hx => I3 x (by omega))).trans P1a
        · -- dead branch: 0 < nl (the pivot is not the minimum) and nl < len (the pivot is on the right)
          rename_i hok
          exfalso
          apply hok
          have hpos : 0 < nl.toNat := by
            rcases Nat.eq_zero_or_pos nl.toNat with h0 | h0
            · exact absurd (UInt64.toNat.inj (by simpa using h0)) hnl0
            · exact h0
          refine ⟨hpos, ?_⟩
          have hlenR : 0 < (rightPart false pivot (v.slice lo.toNat (hi.toNat - lo.toNat))).length := List.length_pos_of_mem hpmemR
          have hlenLR := congrArg List.length E1
          simp only [List.length_append, length_slice] at hlenLR
          rw [hlen]; omega

theorem stableQuicksort_spec (scratchLen : UInt64) :
    QuickSpec (fun v s lo hi hv hs hvsz hssz hlo => stableQuicksort v s lo hi scratchLen hv hs hvsz hssz hlo) := by
  intro v s lo hi hv hs hvsz hssz hlo
  unfold stableQuicksort
  exact quicksort_spec scratchLen (hi.toNat - lo.toNat) v s lo hi _ false 0 hv hs hvsz hssz hlo rfl (fun h => by simp at h)

theorem driftSortFull_spec (v s : A) (lo hi scratchLen : UInt64) hv hs hvsz hssz hlo :
    Sorted le64 ((driftSortFull v s lo hi scratchLen hv hs hvsz hssz hlo).1.1.slice lo.toNat (hi.toNat - lo.toNat)) ∧
    ((driftSortFull v s lo hi scratchLen hv hs hvsz hssz hlo).1.1.slice lo.toNat (hi.toNat - lo.toNat)).Perm
      (v.slice lo.toNat (hi.toNat - lo.toNat)) ∧
    ∀ x, (x < lo.toNat ∨ hi.toNat ≤ x) → (driftSortFull v s lo hi scratchLen hv hs hvsz hssz hlo).1.1.at' x = v.at' x :=
  driftSort_spec _ (stableQuicksort_spec scratchLen) v s lo hi scratchLen false hv hs hvsz hssz hlo

/-! ## The headline theorems -/

/-- The bounds-safe driftsort returns a sorted array. -/
theorem sort_sorted (xs : A) (hsz : xs.size < 2 ^ 62) : Sorted le64 (sort xs hsz).data.toList := by
  unfold sort
  have hn : (xs.size.toUInt64).toNat = xs.size := by simp; omega
  dsimp only
  split
  · rename_i h
    have h : (xs.size.toUInt64).toNat < 2 := by have := UInt64.lt_iff_toNat_lt.mp h; simpa using this
    rw [← slice_eq_toList]
    exact sorted_of_length_le_one _ (by simp; omega)
  · split
    · obtain ⟨S, _⟩ := insertionSortRange_spec 0 xs.size.toUInt64 ((xs.size.toUInt64).toNat - (0 : UInt64).toNat) 0 xs (by omega) (by omega)
        (by simp) rfl (by simp) (by simp [Sorted])
      have hs' : (insertionSortRange 0 xs.size.toUInt64 0 xs (by omega) (by omega) (by simp)).1.size = (xs.size.toUInt64).toNat := by
        rw [(insertionSortRange _ _ _ _ _ _ _).2, hn]
      simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.sub_zero] at S
      rw [← slice_eq_toList, hs', S]
      exact insertAll_sorted _ _ (by simp [Sorted])
    · split
      · have D := driftSortEager_spec xs (zeros xs.size) 0 xs.size.toUInt64 xs.size.toUInt64 (by omega) (by rw [size_zeros]; omega) (by omega)
          (by rw [size_zeros]; omega) (by simp)
        have hs' : (driftSortEager xs (zeros xs.size) 0 xs.size.toUInt64 xs.size.toUInt64 (by omega) (by rw [size_zeros]; omega) (by omega)
            (by rw [size_zeros]; omega) (by simp)).1.1.size = (xs.size.toUInt64).toNat := by
          rw [(driftSortEager _ _ _ _ _ _ _ _ _ _).2.1, hn]
        rw [← slice_eq_toList, hs']
        simpa using D.1
      · have D := driftSortFull_spec xs (zeros xs.size) 0 xs.size.toUInt64 xs.size.toUInt64 (by omega) (by rw [size_zeros]; omega) (by omega)
          (by rw [size_zeros]; omega) (by simp)
        have hs' : (driftSortFull xs (zeros xs.size) 0 xs.size.toUInt64 xs.size.toUInt64 (by omega) (by rw [size_zeros]; omega) (by omega)
            (by rw [size_zeros]; omega) (by simp)).1.1.size = (xs.size.toUInt64).toNat := by
          rw [(driftSortFull _ _ _ _ _ _ _ _ _ _).2.1, hn]
        rw [← slice_eq_toList, hs']
        simpa using D.1

/-- The bounds-safe driftsort returns a permutation of its input. -/
theorem sort_perm (xs : A) (hsz : xs.size < 2 ^ 62) : (sort xs hsz).data.toList.Perm xs.data.toList := by
  unfold sort
  have hn : (xs.size.toUInt64).toNat = xs.size := by simp; omega
  have exs : xs.slice 0 (xs.size.toUInt64).toNat = xs.data.toList := by rw [hn, slice_eq_toList]
  dsimp only
  split
  · exact List.Perm.refl _
  · split
    · obtain ⟨S, _⟩ := insertionSortRange_spec 0 xs.size.toUInt64 ((xs.size.toUInt64).toNat - (0 : UInt64).toNat) 0 xs (by omega) (by omega)
        (by simp) rfl (by simp) (by simp [Sorted])
      have hs' : (insertionSortRange 0 xs.size.toUInt64 0 xs (by omega) (by omega) (by simp)).1.size = (xs.size.toUInt64).toNat := by
        rw [(insertionSortRange _ _ _ _ _ _ _).2, hn]
      simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.sub_zero] at S
      rw [← slice_eq_toList, hs', S, ← exs]
      simpa using insertAll_perm ([] : List UInt64) (xs.slice 0 (xs.size.toUInt64).toNat)
    · split
      · have D := driftSortEager_spec xs (zeros xs.size) 0 xs.size.toUInt64 xs.size.toUInt64 (by omega) (by rw [size_zeros]; omega) (by omega)
          (by rw [size_zeros]; omega) (by simp)
        have hs' : (driftSortEager xs (zeros xs.size) 0 xs.size.toUInt64 xs.size.toUInt64 (by omega) (by rw [size_zeros]; omega) (by omega)
            (by rw [size_zeros]; omega) (by simp)).1.1.size = (xs.size.toUInt64).toNat := by
          rw [(driftSortEager _ _ _ _ _ _ _ _ _ _).2.1, hn]
        rw [← slice_eq_toList, hs', ← exs]
        simpa using D.2.1
      · have D := driftSortFull_spec xs (zeros xs.size) 0 xs.size.toUInt64 xs.size.toUInt64 (by omega) (by rw [size_zeros]; omega) (by omega)
          (by rw [size_zeros]; omega) (by simp)
        have hs' : (driftSortFull xs (zeros xs.size) 0 xs.size.toUInt64 xs.size.toUInt64 (by omega) (by rw [size_zeros]; omega) (by omega)
            (by rw [size_zeros]; omega) (by simp)).1.1.size = (xs.size.toUInt64).toNat := by
          rw [(driftSortFull _ _ _ _ _ _ _ _ _ _).2.1, hn]
        rw [← slice_eq_toList, hs', ← exs]
        simpa using D.2.1

end DriftSort
