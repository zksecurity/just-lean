/-!
# Part 1: a readable merge sort on lists, and a readable proof that it sorts.

The same file as `MergeSort/Simple.lean` in the library, plus a `main`, as a standalone project:
`lake build && echo 5 3 9 1 1 7 | lake exe part1`.
-/
namespace MergeSort

/-- The specification: every element is `≤` every later element. -/
def Sorted {α : Type} [LE α] (l : List α) : Prop := l.Pairwise (· ≤ ·)

/-- Merge two sorted lists into one sorted list. -/
def merge {α : Type} [LE α] [DecidableLE α] : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x ≤ y then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys

/-- Split in half, sort both halves, merge. -/
def mergeSort {α : Type} [LE α] [DecidableLE α] (l : List α) : List α :=
  if h : l.length ≤ 1 then l
  else
    let half := l.length / 2
    merge (mergeSort (l.take half)) (mergeSort (l.drop half))
termination_by l.length
decreasing_by all_goals simp; omega

/-! ## The output is a permutation of the input -/

theorem merge_perm {α : Type} [LE α] [DecidableLE α] (xs ys : List α) :
    (merge xs ys).Perm (xs ++ ys) := by
  induction xs, ys using merge.induct with
  | case1 ys => simp [merge]
  | case2 xs h => simp [merge]
  | case3 x xs y ys hle ih => simpa [merge, hle] using ih
  | case4 x xs y ys hle ih =>
    simp [merge, hle]
    exact (ih.cons y).trans List.perm_middle.symm

theorem mergeSort_perm {α : Type} [LE α] [DecidableLE α] (l : List α) :
    (mergeSort l).Perm l := by
  induction l using mergeSort.induct with
  | case1 l h => simp [mergeSort, h]
  | case2 l h half ih1 ih2 =>
    rw [mergeSort, dif_neg h]
    exact (merge_perm _ _).trans ((ih1.append ih2).trans (by simp))

/-! ## The output is sorted -/

theorem mem_merge {α : Type} [LE α] [DecidableLE α] {a : α} {xs ys : List α} :
    a ∈ merge xs ys ↔ a ∈ xs ∨ a ∈ ys := by
  rw [(merge_perm xs ys).mem_iff, List.mem_append]

/-- Merging sorted lists gives a sorted list, provided `≤` is transitive and total. -/
theorem merge_sorted {α : Type} [LE α] [DecidableLE α]
    (trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c)
    (total : ∀ a b : α, a ≤ b ∨ b ≤ a)
    {xs ys : List α} (hx : Sorted xs) (hy : Sorted ys) :
    Sorted (merge xs ys) := by
  induction xs, ys using merge.induct with
  | case1 ys => simpa [merge]
  | case2 xs h => simpa [merge]
  | case3 x xs y ys hle ih =>
    simp only [merge, hle, ↓reduceIte]
    have hx' := List.pairwise_cons.mp hx
    refine List.pairwise_cons.mpr ⟨?_, ih hx'.2 hy⟩
    intro b hb
    rcases mem_merge.mp hb with hb | hb
    · exact hx'.1 b hb
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact hle
      · exact trans _ _ _ hle ((List.pairwise_cons.mp hy).1 b hb)
  | case4 x xs y ys hle ih =>
    simp only [merge, hle, ↓reduceIte]
    have hy' := List.pairwise_cons.mp hy
    have hyx : y ≤ x := by
      rcases total x y with h | h
      · exact absurd h hle
      · exact h
    refine List.pairwise_cons.mpr ⟨?_, ih hx hy'.2⟩
    intro b hb
    rcases mem_merge.mp hb with hb | hb
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact hyx
      · exact trans _ _ _ hyx ((List.pairwise_cons.mp hx).1 b hb)
    · exact hy'.1 b hb

theorem mergeSort_sorted {α : Type} [LE α] [DecidableLE α]
    (trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c)
    (total : ∀ a b : α, a ≤ b ∨ b ≤ a)
    (l : List α) : Sorted (mergeSort l) := by
  induction l using mergeSort.induct with
  | case1 l h =>
    rw [mergeSort, dif_pos h]
    match l, h with
    | [], _ => simp [Sorted]
    | [x], _ => simp [Sorted]
  | case2 l h half ih1 ih2 =>
    rw [mergeSort, dif_neg h]
    exact merge_sorted trans total ih1 ih2

/-- The headline theorem. -/
theorem mergeSort_correct {α : Type} [LE α] [DecidableLE α]
    (trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c)
    (total : ∀ a b : α, a ≤ b ∨ b ≤ a)
    (l : List α) : Sorted (mergeSort l) ∧ (mergeSort l).Perm l :=
  ⟨mergeSort_sorted trans total l, mergeSort_perm l⟩

end MergeSort

open MergeSort

def main : IO Unit := do
  let line ← (← IO.getStdin).getLine
  let xs := (line.trimAscii.copy.splitOn " ").filterMap String.toNat?
  IO.println (mergeSort xs)
