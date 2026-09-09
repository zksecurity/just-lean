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

end DriftSort
