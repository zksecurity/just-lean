import MergeSort.BidiSort
import MergeSort.SmallRunsCorrect
/-!
# Part 3 building block: a merge kernel that skips runs already in order

If `src[mid-1] ≤ src[mid]` the two sorted runs are already in order and merging them is a copy.
`mergeKernelS` has exactly the specification of `mergeKernel`, so it can replace it in any of the
verified sorts (it pays off for merges between long natural runs; see `PLAN.md`).
-/
namespace MergeSort.BottomUp
open UInt64Array MergeSort.Fast

/-- Copy `src[k, hi)` into `dst[k, hi)`. -/
def copyRange (k hi : UInt64) (src dst : UInt64Array)
    (hsz : dst.size < 2 ^ 64 := by u64) (hs : hi.toNat ≤ src.size := by u64) (hd : hi.toNat ≤ dst.size := by u64) :
    { b : UInt64Array // b.size = dst.size } :=
  if h : k < hi then
    have h : k.toNat < hi.toNat := h
    castSize (copyRange (k + 1) hi src (dst.set k (src.get k))) (by simp)
  else ⟨dst, rfl⟩
termination_by hi.toNat - k.toNat
decreasing_by u64

theorem copyRange_spec (hi : UInt64) (src : UInt64Array) :
    ∀ (m : Nat) (k : UInt64) (dst : UInt64Array) hsz hs hd, m = hi.toNat - k.toNat →
    (∀ x, k.toNat ≤ x → x < hi.toNat → (copyRange k hi src dst hsz hs hd).1.at' x = src.at' x) ∧
    (∀ x, (x < k.toNat ∨ hi.toNat ≤ x) → (copyRange k hi src dst hsz hs hd).1.at' x = dst.at' x) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro k dst hsz hs hd hm
  rw [copyRange]
  split
  · rename_i h
    have h : k.toNat < hi.toNat := h
    have ek : (k + 1).toNat = k.toNat + 1 := by u64g
    simp only [castSize_val]
    obtain ⟨A, B⟩ := ih (hi.toNat - (k + 1).toNat) (by omega) (k + 1) (dst.set k (src.get k)) (by simp; omega) hs (by simp; omega) rfl
    refine ⟨fun x hx1 hx2 => ?_, fun x hx => ?_⟩
    · by_cases hxk : x = k.toNat
      · subst hxk; rw [B _ (Or.inl (by omega)), at'_set_self, get_eq_at']
      · rw [A x (by omega) hx2]
    · rw [B x (by omega)]; exact at'_set_ne _ _ _ _ _ (by omega)
  · refine ⟨fun x hx1 hx2 => ?_, fun _ _ => rfl⟩
    rename_i h
    have : ¬ k.toNat < hi.toNat := h
    omega

/-- Merging two sorted lists that are already in order is concatenation. -/
theorem merge_eq_append (L R : List UInt64) (h : ∀ l ∈ L, ∀ r ∈ R, l ≤ r) :
    merge le64 L R = L ++ R := by
  induction L with
  | nil => simp [merge_nil_left]
  | cons l L ih =>
    cases R with
    | nil => simp [merge_nil_right]
    | cons r R =>
      have hlr : le64 l r = true := by
        simp only [le64, decide_eq_true_eq]; exact h l (by simp) r (by simp)
      simp only [merge, hlr, if_true, List.cons_append]
      rw [ih (fun l' hl' r' hr' => h l' (by simp [hl']) r' hr')]

/-- All elements of the left sorted run are `≤` all elements of the right sorted run when the
    boundary elements are in order. -/
theorem runs_in_order (L R : List UInt64) (x y : UInt64) (hL : Sorted le64 (L ++ [x])) (hR : Sorted le64 (y :: R))
    (hxy : x ≤ y) : ∀ l ∈ L ++ [x], ∀ r ∈ y :: R, l ≤ r := by
  intro l hl r hr
  have h1 : l ≤ x := by
    rcases List.mem_append.mp hl with hl | hl
    · exact sorted_last_le L x hL l hl
    · simp at hl; subst hl; exact UInt64.le_refl _
  have h2 : y ≤ r := by
    rcases List.mem_cons.mp hr with hr | hr
    · subst hr; exact UInt64.le_refl _
    · have := (List.pairwise_cons.mp hR).1 r hr; simpa using this
  exact UInt64.le_trans h1 (UInt64.le_trans hxy h2)

/-- `mergeKernel` with the in-order fast path. -/
def mergeKernelS (lo mid hi : UInt64) (src dst : UInt64Array)
    (hsz : dst.size < 2 ^ 64 := by u64) (hs : hi.toNat ≤ src.size := by u64) (hd : hi.toNat ≤ dst.size := by u64)
    (hlo : lo.toNat ≤ mid.toNat := by u64) (hmid : mid.toNat ≤ hi.toNat := by u64) :
    { b : UInt64Array // b.size = dst.size } :=
  if h : lo < mid ∧ mid < hi then
    have h1 : lo.toNat < mid.toNat := h.1
    have h2 : mid.toNat < hi.toNat := h.2
    if src.get (mid - 1) ≤ src.get mid then copyRange lo hi src dst
    else mergeKernel lo mid hi src dst
  else mergeKernel lo mid hi src dst

theorem mergeKernelS_spec (lo mid hi : UInt64) (src dst : UInt64Array) hsz hs hd hlo hmid
    (hL : Sorted le64 (src.slice lo.toNat (mid.toNat - lo.toNat)))
    (hR : Sorted le64 (src.slice mid.toNat (hi.toNat - mid.toNat))) :
    (mergeKernelS lo mid hi src dst hsz hs hd hlo hmid).1.slice lo.toNat (hi.toNat - lo.toNat) =
      merge le64 (src.slice lo.toNat (mid.toNat - lo.toNat)) (src.slice mid.toNat (hi.toNat - mid.toNat)) ∧
    ∀ x, (x < lo.toNat ∨ hi.toNat ≤ x) → (mergeKernelS lo mid hi src dst hsz hs hd hlo hmid).1.at' x = dst.at' x := by
  rw [mergeKernelS]
  split
  · rename_i h
    have h1 : lo.toNat < mid.toNat := h.1
    have h2 : mid.toNat < hi.toNat := h.2
    dsimp only
    split
    · rename_i hle
      have em : (mid - 1).toNat = mid.toNat - 1 := by u64g
      obtain ⟨A, B⟩ := copyRange_spec hi src (hi.toNat - lo.toNat) lo dst hsz hs hd rfl
      -- decompose the runs to expose the boundary elements
      have eL : src.slice lo.toNat (mid.toNat - lo.toNat) =
          src.slice lo.toNat (mid.toNat - 1 - lo.toNat) ++ [src.at' (mid.toNat - 1)] := by
        rw [show mid.toNat - lo.toNat = (mid.toNat - 1 - lo.toNat) + 1 by omega, slice_succ,
          show lo.toNat + (mid.toNat - 1 - lo.toNat) = mid.toNat - 1 by omega]
      have eR : src.slice mid.toNat (hi.toNat - mid.toNat) =
          src.at' mid.toNat :: src.slice (mid.toNat + 1) (hi.toNat - mid.toNat - 1) := by
        rw [show hi.toNat - mid.toNat = (hi.toNat - mid.toNat - 1) + 1 by omega, slice_cons, Nat.add_sub_cancel]
      have hxy : src.at' (mid.toNat - 1) ≤ src.at' mid.toNat := by
        simpa [get_eq_at', em] using hle
      rw [eL] at hL; rw [eR] at hR
      have hord := runs_in_order _ _ _ _ hL hR hxy
      rw [← eL] at hord hL; rw [← eR] at hord hR
      refine ⟨?_, fun x hx => B x hx⟩
      rw [merge_eq_append _ _ hord, show hi.toNat - lo.toNat = (mid.toNat - lo.toNat) + (hi.toNat - mid.toNat) by omega,
        slice_add, show lo.toNat + (mid.toNat - lo.toNat) = mid.toNat by omega]
      congr 1
      · apply slice_congr; intro t ht; exact A _ (by omega) (by omega)
      · apply slice_congr; intro t ht; exact A _ (by omega) (by omega)
    · exact mergeKernel_spec lo mid hi src dst hsz hs hd hlo hmid hL hR
  · exact mergeKernel_spec lo mid hi src dst hsz hs hd hlo hmid hL hR

end MergeSort.BottomUp
