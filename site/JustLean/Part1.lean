import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option verso.code.warnLineLength 0

#doc (Manual) "Part 1: merge sort, and a proof that it sorts" =>

This part is self-contained: the code on this page is the whole of `MergeSort/Simple.lean` in the
repository, and it is checked when this page is built. Hover over any name to see its type.

# The specification

A list is sorted when every element is `le` every later element. Lean's `List.Pairwise` says exactly
that, so the specification is one line:

```lean
/-- The specification: every element is `le` every later element. -/
def Sorted {α : Type} (le : α → α → Bool) (l : List α) : Prop :=
  l.Pairwise (fun a b => le a b = true)
```

The other half of the specification is that the output must be a rearrangement of the input.
`List.Perm` from the standard library is that relation, so we do not have to define anything.

The comparison `le` is a `Bool`-valued function rather than a `Prop`, so that the same function can
be run and reasoned about.

# The algorithm

`merge` walks two lists and takes the smaller head at each step. Lean checks that it terminates by
itself, because each recursive call is on a structurally smaller argument.

```lean
/-- Merge two sorted lists into one sorted list. -/
def merge {α : Type} (le : α → α → Bool) : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if le x y then x :: merge le xs (y :: ys) else y :: merge le (x :: xs) ys
```

`mergeSort` splits the list in half, sorts both halves and merges. The recursion is on `take` and
`drop`, which are not structurally smaller, so we say what decreases (`l.length`) and give a one-line
proof that it does.

```lean
/-- Split in half, sort both halves, merge. -/
def mergeSort {α : Type} (le : α → α → Bool) (l : List α) : List α :=
  if h : l.length ≤ 1 then l
  else
    let half := l.length / 2
    merge le (mergeSort le (l.take half)) (mergeSort le (l.drop half))
termination_by l.length
decreasing_by all_goals simp; omega
```

That is the program. It runs as it stands:

```lean (name := demo)
#eval mergeSort (fun a b => decide (a ≤ b)) [5, 3, 9, 1, 1, 7]
```
```leanOutput demo
[1, 1, 3, 5, 7, 9]
```

# The proof: permutation

Because `merge` and `mergeSort` are recursive definitions, Lean derives an induction principle for
each one (`merge.induct`, `mergeSort.induct`) whose cases are exactly the cases of the definition.
Proofs follow the shape of the code.

The output of `merge` is a permutation of the two inputs appended:

```lean
theorem merge_perm {α : Type} (le : α → α → Bool) (xs ys : List α) :
    (merge le xs ys).Perm (xs ++ ys) := by
  induction xs, ys using merge.induct le with
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

```lean
theorem mergeSort_perm {α : Type} (le : α → α → Bool) (l : List α) :
    (mergeSort le l).Perm l := by
  induction l using mergeSort.induct with
  | case1 l h => simp [mergeSort, h]
  | case2 l h half ih1 ih2 =>
    rw [mergeSort, dif_neg h]
    exact (merge_perm le _ _).trans ((ih1.append ih2).trans (by simp))
```

# The proof: sortedness

A merge of two sorted lists is sorted, provided `le` is transitive and total. These two facts about
`le` are all the proof needs, and they are stated as hypotheses rather than assumed, so `mergeSort`
works for any comparison, and the theorem says which ones it sorts by.

One small lemma first: an element of the merge came from one of the inputs.

```lean
theorem mem_merge {α : Type} (le : α → α → Bool) {a : α} {xs ys : List α} :
    a ∈ merge le xs ys ↔ a ∈ xs ∨ a ∈ ys := by
  rw [(merge_perm le xs ys).mem_iff, List.mem_append]
```

Now the merge lemma. Case 3 is where `x ≤ y` and `x` goes first: `x` is below everything in `xs` by
the hypothesis, below `y` by the test, and below the rest of `ys` by transitivity through `y`. Case 4
is symmetric, except that `y ≤ x` has to come from totality, since the test only told us `¬ x ≤ y`.

```lean
/-- Merging sorted lists gives a sorted list, provided `le` is transitive and total. -/
theorem merge_sorted {α : Type} (le : α → α → Bool)
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
```

Sortedness of `mergeSort` is then induction again. Lists of length at most one are sorted, and the
other case is the merge lemma applied to the two induction hypotheses.

```lean
theorem mergeSort_sorted {α : Type} (le : α → α → Bool)
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
```

Both halves together:

```lean
/-- The headline theorem. -/
theorem mergeSort_correct {α : Type} (le : α → α → Bool)
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, le a b = true ∨ le b a = true)
    (l : List α) : Sorted le (mergeSort le l) ∧ (mergeSort le l).Perm l :=
  ⟨mergeSort_sorted le trans total l, mergeSort_perm le l⟩
```

Lean can report what a proof rests on. The axioms below are standard ones (propositional
extensionality and quotients); there is no `sorry` and nothing else was assumed.

```lean (name := axioms)
#print axioms mergeSort_correct
```
```leanOutput axioms
'mergeSort_correct' depends on axioms: [propext, Quot.sound]
```

# Compile and run

A `main` that reads numbers from standard input and prints them sorted:

```lean -keep
def main : IO Unit := do
  let line ← (← IO.getStdin).getLine
  let xs := (line.trimAscii.copy.splitOn " ").filterMap String.toNat?
  IO.println (mergeSort (fun a b => decide (a ≤ b)) xs)
```

The program below was compiled and run while this page was built, with the input shown, and its
output is what it printed.

:::ioExample
```ioLean -show
def Sorted {α : Type} (le : α → α → Bool) (l : List α) : Prop :=
  l.Pairwise (fun a b => le a b = true)

def merge {α : Type} (le : α → α → Bool) : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if le x y then x :: merge le xs (y :: ys) else y :: merge le (x :: xs) ys

def mergeSort {α : Type} (le : α → α → Bool) (l : List α) : List α :=
  if h : l.length ≤ 1 then l
  else
    let half := l.length / 2
    merge le (mergeSort le (l.take half)) (mergeSort le (l.drop half))
termination_by l.length
decreasing_by all_goals simp; omega

def main : IO Unit := do
  let line ← (← IO.getStdin).getLine
  let xs := (line.trimAscii.copy.splitOn " ").filterMap String.toNat?
  IO.println (mergeSort (fun a b => decide (a ≤ b)) xs)
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
