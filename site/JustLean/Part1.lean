import VersoManual
import MergeSort.Simple

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open MergeSort

set_option pp.rawOnError true
set_option maxHeartbeats 2000000
set_option verso.code.warnLineLength 0
set_option verso.exampleProject ".."
set_option verso.exampleModule "MergeSort.Simple"

#doc (Manual) "Part 1: merge sort, and a proof that it sorts" =>

%%%
file := "part-1"
tag := "part-1"
%%%

The code on this page is `MergeSort/Simple.lean` in the repository, shown here piece by piece and
checked against the file when the page is built. Hover over a name to see its type, and over a
tactic to see the proof state at that point.

# The specification
%%%
tag := "spec"
%%%

A list is sorted when every element is `≤` every later element. Lean's `List.Pairwise` says exactly
that, so the specification is one line:

```anchor Sorted (module := MergeSort.Simple)
/-- The specification: every element is `≤` every later element. -/
def Sorted {α : Type} [LE α] (l : List α) : Prop := l.Pairwise (· ≤ ·)
```

The other half of the specification is that the output must be a rearrangement of the input.
`List.Perm` from the standard library is that relation, so we do not have to define anything.

The order comes from an `LE` instance on the element type, which is how `≤` is written in Lean. To
_run_ the sort we also need to decide `≤`; that is the `DecidableLE` instance the functions below
ask for. Proofs about `≤` need nothing more than the two facts stated as hypotheses later.

# The algorithm
%%%
tag := "algorithm"
%%%

`merge` walks two lists and takes the smaller head at each step. Lean checks that it terminates by
itself, because each recursive call is on a structurally smaller argument.

```anchor merge (module := MergeSort.Simple)
/-- Merge two sorted lists into one sorted list. -/
def merge {α : Type} [LE α] [DecidableLE α] : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x ≤ y then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys
```

`mergeSort` splits the list in half, sorts both halves and merges. The recursion is on `take` and
`drop`, which are not structurally smaller, so we say what decreases (`l.length`) and give a one-line
proof that it does.

```anchor mergeSort (module := MergeSort.Simple)
/-- Split in half, sort both halves, merge. -/
def mergeSort {α : Type} [LE α] [DecidableLE α] (l : List α) : List α :=
  if h : l.length ≤ 1 then l
  else
    let half := l.length / 2
    merge (mergeSort (l.take half)) (mergeSort (l.drop half))
termination_by l.length
decreasing_by all_goals simp; omega
```

That is the program. It runs as it stands:

```lean (name := demo)
#eval mergeSort [5, 3, 9, 1, 1, 7]
```
```leanOutput demo
[1, 1, 3, 5, 7, 9]
```

# The proof: permutation
%%%
tag := "proof-permutation"
%%%

Because `merge` and `mergeSort` are recursive definitions, Lean derives an induction principle for
each one (`merge.induct`, `mergeSort.induct`) whose cases are exactly the cases of the definition.
Proofs follow the shape of the code.

The output of `merge` is a permutation of the two inputs appended:

```anchor merge_perm (module := MergeSort.Simple)
theorem merge_perm {α : Type} [LE α] [DecidableLE α] (xs ys : List α) :
    (merge xs ys).Perm (xs ++ ys) := by
  induction xs, ys using merge.induct with
  | case1 ys => simp [merge]
  | case2 xs h => simp [merge]
  | case3 x xs y ys hle ih => simpa [merge, hle] using ih
  | case4 x xs y ys hle ih =>
    simp [merge, hle]
    exact (ih.cons y).trans List.perm_middle.symm
```

The first three cases are what `simp` can see on its own once it unfolds `merge`. In the fourth case
the output starts with `y`, which came from the middle of `xs ++ y :: ys`; `List.perm_middle` is the
library lemma for that.

The same for `mergeSort`, using that `take` and `drop` together give the list back:

```anchor mergeSort_perm (module := MergeSort.Simple)
theorem mergeSort_perm {α : Type} [LE α] [DecidableLE α] (l : List α) :
    (mergeSort l).Perm l := by
  induction l using mergeSort.induct with
  | case1 l h => simp [mergeSort, h]
  | case2 l h half ih1 ih2 =>
    rw [mergeSort, dif_neg h]
    exact (merge_perm _ _).trans ((ih1.append ih2).trans (by simp))
```

# The proof: sortedness
%%%
tag := "proof-sortedness"
%%%

A merge of two sorted lists is sorted, provided `≤` is transitive and total. These two facts are all
the proof needs, and they are stated as hypotheses rather than assumed from a class, so the theorem
says exactly which orders it sorts by.

One small lemma first: an element of the merge came from one of the inputs.

```anchor mem_merge (module := MergeSort.Simple)
theorem mem_merge {α : Type} [LE α] [DecidableLE α] {a : α} {xs ys : List α} :
    a ∈ merge xs ys ↔ a ∈ xs ∨ a ∈ ys := by
  rw [(merge_perm xs ys).mem_iff, List.mem_append]
```

Now the merge lemma. Case 3 is where `x ≤ y` and `x` goes first: `x` is below everything in `xs` by
the hypothesis, below `y` by the test, and below the rest of `ys` by transitivity through `y`. Case 4
is symmetric, except that `y ≤ x` has to come from totality, since the test only told us `¬ x ≤ y`.

```anchor merge_sorted (module := MergeSort.Simple)
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
```

Sortedness of `mergeSort` is then induction again. Lists of length at most one are sorted, and the
other case is the merge lemma applied to the two induction hypotheses.

```anchor mergeSort_sorted (module := MergeSort.Simple)
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
```

Both halves together:

```anchor mergeSort_correct (module := MergeSort.Simple)
/-- The headline theorem. -/
theorem mergeSort_correct {α : Type} [LE α] [DecidableLE α]
    (trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c)
    (total : ∀ a b : α, a ≤ b ∨ b ≤ a)
    (l : List α) : Sorted (mergeSort l) ∧ (mergeSort l).Perm l :=
  ⟨mergeSort_sorted trans total l, mergeSort_perm l⟩
```

Lean can report what a proof rests on. The axioms below are standard ones; there is no `sorry` and
nothing else was assumed.

```lean (name := axioms)
#print axioms mergeSort_correct
```
```leanOutput axioms
'MergeSort.mergeSort_correct' depends on axioms: [propext, Quot.sound]
```

# Compile and run
%%%
tag := "compile-and-run"
%%%

A `main` that reads numbers from standard input and prints them sorted:

```lean -keep
def main : IO Unit := do
  let line ← (← IO.getStdin).getLine
  let xs := (line.trimAscii.copy.splitOn " ").filterMap String.toNat?
  IO.println (mergeSort xs)
```

The program below was compiled and run while this page was built, with the input shown, and its
output is what it printed.

:::ioExample
```ioLean -show
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

def main : IO Unit := do
  let line ← (← IO.getStdin).getLine
  let xs := (line.trimAscii.copy.splitOn " ").filterMap String.toNat?
  IO.println (mergeSort xs)
```
```stdin
5 3 9 1 1 7
```
```stdout
[1, 1, 3, 5, 7, 9]
```
:::

To do the same on your machine, put the code of this page into a fresh Lake project:

```
lake new sortdemo
cd sortdemo
# paste the definitions, theorems and main into Main.lean
lake build
echo 5 3 9 1 1 7 | ./.lake/build/bin/sortdemo
```

`lake build` compiles Lean to C (`.lake/build/ir/Main.c`, if you want to look) and the C to a
native executable with the clang that ships with Lean. The proofs are checked in the same step; they
cost nothing at runtime, since a theorem compiles to nothing.

On a million pseudo-random numbers this sort takes about 770 ms (`lake exe listbench 1000000` in the
repository). That is a linked list of boxed numbers being taken apart and rebuilt twenty times over.
The next part changes the data representation and keeps the proof.
