/-!
# Part 1: a readable merge sort on lists, and a readable proof that it sorts.
-/
namespace MergeSort

variable {α : Type} (le : α → α → Bool)

/-- The specification: every element is `le` every later element. -/
def Sorted (l : List α) : Prop := l.Pairwise (fun a b => le a b = true)

/-- Merge two sorted lists into one sorted list. -/
def merge : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if le x y then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys

/-- Split in half, sort both halves, merge. -/
def mergeSort (l : List α) : List α :=
  if h : l.length ≤ 1 then l
  else
    let half := l.length / 2
    merge le (mergeSort (l.take half)) (mergeSort (l.drop half))
termination_by l.length
decreasing_by all_goals simp; omega

/-! ## The output is a permutation of the input -/

theorem merge_perm (xs ys : List α) : (merge le xs ys).Perm (xs ++ ys) := by
  induction xs, ys using merge.induct le with
  | case1 ys => simp [merge]
  | case2 xs h => simp [merge]
  | case3 x xs y ys hle ih => simpa [merge, hle] using ih
  | case4 x xs y ys hle ih =>
    simp [merge, hle]
    exact (ih.cons y).trans List.perm_middle.symm

theorem mergeSort_perm (l : List α) : (mergeSort le l).Perm l := by
  induction l using mergeSort.induct with
  | case1 l h => simp [mergeSort, h]
  | case2 l h half ih1 ih2 =>
    rw [mergeSort, dif_neg h]
    exact (merge_perm le _ _).trans ((ih1.append ih2).trans (by simp))

/-! ## The output is sorted -/

theorem mem_merge {a : α} {xs ys : List α} : a ∈ merge le xs ys ↔ a ∈ xs ∨ a ∈ ys := by
  rw [(merge_perm le xs ys).mem_iff, List.mem_append]

/-- Merging sorted lists gives a sorted list, provided `le` is transitive and total. -/
theorem merge_sorted
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, le a b = true ∨ le b a = true)
    {xs ys : List α} (hx : Sorted le xs) (hy : Sorted le ys) :
    Sorted le (merge le xs ys) := by
  induction xs, ys using merge.induct le with
  | case1 ys => simpa [merge]
  | case2 xs h => simpa [merge]
  | case3 x xs y ys hle ih =>
    simp only [merge, hle, ↓reduceIte]
    have hx' := List.pairwise_cons.mp hx
    refine List.pairwise_cons.mpr ⟨?_, ih hx'.2 hy⟩
    intro b hb
    rcases (mem_merge le).mp hb with hb | hb
    · exact hx'.1 b hb
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact hle
      · exact trans _ _ _ hle ((List.pairwise_cons.mp hy).1 b hb)
  | case4 x xs y ys hle ih =>
    simp only [merge, hle, Bool.false_eq_true, ↓reduceIte]
    have hy' := List.pairwise_cons.mp hy
    have hyx : le y x = true := by
      rcases total x y with h | h
      · exact absurd h (by simpa using hle)
      · exact h
    refine List.pairwise_cons.mpr ⟨?_, ih hx hy'.2⟩
    intro b hb
    rcases (mem_merge le).mp hb with hb | hb
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact hyx
      · exact trans _ _ _ hyx ((List.pairwise_cons.mp hx).1 b hb)
    · exact hy'.1 b hb

theorem mergeSort_sorted
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, le a b = true ∨ le b a = true)
    (l : List α) : Sorted le (mergeSort le l) := by
  induction l using mergeSort.induct with
  | case1 l h =>
    rw [mergeSort, dif_pos h]
    match l, h with
    | [], _ => simp [Sorted]
    | [x], _ => simp [Sorted]
  | case2 l h half ih1 ih2 =>
    rw [mergeSort, dif_neg h]
    exact merge_sorted le trans total ih1 ih2

/-- The headline theorem. -/
theorem mergeSort_correct
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, le a b = true ∨ le b a = true)
    (l : List α) : Sorted le (mergeSort le l) ∧ (mergeSort le l).Perm l :=
  ⟨mergeSort_sorted le trans total l, mergeSort_perm le l⟩

end MergeSort
