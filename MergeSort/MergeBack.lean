import MergeSort.Correct
/-!
Groundwork for verifying the bidirectional merge: merging two sorted runs *from the back* (largest
first, ties taken from the right run) produces the reverse of the ordinary stable merge.
-/
namespace MergeSort.Fast

/-- Merge two runs given largest-first (i.e. reversed sorted runs), producing largest-first output.
    Ties take the right run's element, mirroring `merge`, which takes the left run's element on ties. -/
def mergeBack : List UInt64 → List UInt64 → List UInt64
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => if x ≤ y then y :: mergeBack (x :: xs) ys else x :: mergeBack xs (y :: ys)

theorem mergeBack_nil_left (ys : List UInt64) : mergeBack [] ys = ys := by simp [mergeBack]
theorem mergeBack_nil_right (xs : List UInt64) : mergeBack xs [] = xs := by cases xs <;> simp [mergeBack]

/-- If every element of both runs is `≤ y`, the stable merge puts a trailing `y` of the right run last. -/
theorem merge_append_right (L R : List UInt64) (y : UInt64) (hL : ∀ l ∈ L, l ≤ y) (hR : ∀ r ∈ R, r ≤ y) :
    merge le64 L (R ++ [y]) = merge le64 L R ++ [y] := by
  induction L generalizing R with
  | nil => simp [merge_nil_left]
  | cons l L ihL =>
    induction R with
    | nil =>
      simp only [List.nil_append, merge_nil_right, merge_cons_cons, hL l (List.mem_cons_self ..), ite_true]
      have := ihL [] (fun l' hl' => hL l' (List.mem_cons_of_mem l hl')) (by simp)
      simp only [List.nil_append, merge_nil_right] at this
      rw [this]; simp
    | cons r R ihR =>
      simp only [List.cons_append, merge_cons_cons]
      split
      · have := ihL (r :: R) (fun l' hl' => hL l' (List.mem_cons_of_mem l hl')) hR
        simp only [List.cons_append] at this
        rw [this]; rfl
      · rw [ihR (fun r' hr' => hR r' (List.mem_cons_of_mem r hr'))]; rfl

/-- If every element of the right run is `< x` and of the left run `≤ x`, a trailing `x` of the
    left run comes last. -/
theorem merge_append_left (L R : List UInt64) (x : UInt64) (hL : ∀ l ∈ L, l ≤ x) (hR : ∀ r ∈ R, r < x) :
    merge le64 (L ++ [x]) R = merge le64 L R ++ [x] := by
  induction L generalizing R with
  | nil =>
    induction R with
    | nil => simp [merge_nil_right]
    | cons r R ihR =>
      have hrx : ¬ x ≤ r := UInt64.not_le.mpr (hR r (List.mem_cons_self ..))
      simp only [List.nil_append, merge_nil_left, merge_cons_cons, hrx, ite_false]
      have := ihR (fun r' hr' => hR r' (List.mem_cons_of_mem r hr'))
      simp only [List.nil_append, merge_nil_left] at this
      rw [this]; rfl
  | cons l L ihL =>
    induction R with
    | nil => simp [merge_nil_right]
    | cons r R ihR =>
      simp only [List.cons_append, merge_cons_cons]
      split
      · rw [ihL (r :: R) (fun l' hl' => hL l' (List.mem_cons_of_mem l hl')) hR]; rfl
      · have := ihR (fun r' hr' => hR r' (List.mem_cons_of_mem r hr'))
        simp only [List.cons_append] at this
        rw [this]; rfl

/-- Descending runs: every element is `≥` every later one. -/
def Desc (l : List UInt64) : Prop := l.Pairwise (fun a b => b ≤ a)

/-- The stable merge of two sorted runs is the reverse of `mergeBack` on the reversed runs. -/
theorem merge_reverse_eq_reverse_mergeBack (L' R' : List UInt64) (hL : Desc L') (hR : Desc R') :
    merge le64 L'.reverse R'.reverse = (mergeBack L' R').reverse := by
  induction L', R' using mergeBack.induct with
  | case1 R' => simp [merge_nil_left, mergeBack_nil_left]
  | case2 L' h => simp [merge_nil_right, mergeBack_nil_right]
  | case3 x xs y ys hle ih =>
    simp only [mergeBack, hle, ite_true, List.reverse_cons]
    have hxs := List.pairwise_cons.mp hL
    have hys := List.pairwise_cons.mp hR
    rw [merge_append_right _ _ _ (by
        intro l hl
        rcases List.mem_append.mp hl with hl | hl
        · exact UInt64.le_trans (hxs.1 l (List.mem_reverse.mp hl)) hle
        · simp at hl; subst hl; exact hle)
      (fun r hr => hys.1 r (List.mem_reverse.mp hr))]
    rw [← List.reverse_cons, ih hL hys.2]
  | case4 x xs y ys hle ih =>
    simp only [mergeBack, hle, ite_false, List.reverse_cons]
    have hxs := List.pairwise_cons.mp hL
    have hys := List.pairwise_cons.mp hR
    have hyx : y < x := UInt64.not_le.mp hle
    rw [merge_append_left _ _ _ (fun l hl => hxs.1 l (List.mem_reverse.mp hl)) (by
        intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact UInt64.lt_of_le_of_lt (hys.1 r (List.mem_reverse.mp hr)) hyx
        · simp at hr; subst hr; exact hyx)]
    rw [← List.reverse_cons, ih hxs.2 hR]

/-- The back half of a merge is what a merge from the back produces (reversed). -/
theorem drop_merge_eq (L R : List UInt64) (hL : Sorted le64 L) (hR : Sorted le64 R) (w : Nat) :
    (merge le64 L R).drop w = ((mergeBack L.reverse R.reverse).take ((merge le64 L R).length - w)).reverse := by
  have hL' : Desc L.reverse := by
    simp only [Desc]; rw [List.pairwise_reverse]; simpa [Sorted] using hL
  have hR' : Desc R.reverse := by
    simp only [Desc]; rw [List.pairwise_reverse]; simpa [Sorted] using hR
  have e := merge_reverse_eq_reverse_mergeBack L.reverse R.reverse hL' hR'
  simp only [List.reverse_reverse] at e
  rw [e, List.length_reverse, List.drop_reverse]

end MergeSort.Fast
