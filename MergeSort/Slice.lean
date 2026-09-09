import MergeSort.UInt64Array
/-! Slices of a `UInt64Array` as lists, for specifying the array algorithms. -/
namespace UInt64Array

/-- Element `i`, or `0` out of range (a total function that is convenient in specifications). -/
def at' (a : UInt64Array) (i : Nat) : UInt64 := a.data.getD i 0

/-- The list `[a[off], a[off+1], ..., a[off+len-1]]`. -/
def slice (a : UInt64Array) (off len : Nat) : List UInt64 :=
  (List.range len).map (fun t => a.at' (off + t))

theorem at'_eq_get (a : UInt64Array) (i : UInt64) (h : i.toNat < a.size) : a.at' i.toNat = a.get i h := by
  simp [at', get, Array.getD, h]

theorem get_eq_at' (a : UInt64Array) (i : UInt64) (h : i.toNat < a.size) : a.get i h = a.at' i.toNat :=
  (at'_eq_get a i h).symm

theorem at'_set (a : UInt64Array) (i : UInt64) (v : UInt64) (hi) (j : Nat) :
    (a.set i v hi).at' j = if i.toNat = j then v else a.at' j := by
  unfold at' set
  simp only [Array.getD]
  by_cases hj : j < a.data.size
  · simp [hj, Array.getElem_set]
  · have : ¬ i.toNat = j := by intro e; subst e; exact hj hi
    simp [hj, this]

theorem at'_set_ne (a : UInt64Array) (i : UInt64) (v : UInt64) (hi) (j : Nat) (h : i.toNat ≠ j) :
    (a.set i v hi).at' j = a.at' j := by simp [at'_set, h]

@[simp] theorem at'_set_self (a : UInt64Array) (i : UInt64) (v : UInt64) (hi) :
    (a.set i v hi).at' i.toNat = v := by simp [at'_set]

theorem at'_set_eq (a : UInt64Array) (i : UInt64) (v : UInt64) (hi) (j : Nat) (h : i.toNat = j) :
    (a.set i v hi).at' j = v := by subst h; exact at'_set_self a i v hi

@[simp] theorem slice_zero (a : UInt64Array) (off : Nat) : a.slice off 0 = [] := by simp [slice]

theorem slice_succ (a : UInt64Array) (off len : Nat) :
    a.slice off (len + 1) = a.slice off len ++ [a.at' (off + len)] := by
  simp [slice, List.range_succ]

theorem slice_cons (a : UInt64Array) (off len : Nat) :
    a.slice off (len + 1) = a.at' off :: a.slice (off + 1) len := by
  simp [slice, List.range_succ_eq_map, Function.comp_def, Nat.add_assoc, Nat.add_comm 1]

@[simp] theorem slice_one (a : UInt64Array) (off : Nat) : a.slice off 1 = [a.at' off] := by
  simp [slice_cons]

@[simp] theorem length_slice (a : UInt64Array) (off len : Nat) : (a.slice off len).length = len := by
  simp [slice]

theorem slice_add (a : UInt64Array) (off l₁ l₂ : Nat) :
    a.slice off (l₁ + l₂) = a.slice off l₁ ++ a.slice (off + l₁) l₂ := by
  induction l₂ with
  | zero => simp
  | succ l₂ ih => rw [← Nat.add_assoc, slice_succ, ih, slice_succ, List.append_assoc, Nat.add_assoc]

theorem slice_congr' {a b : UInt64Array} {off₁ off₂ len : Nat}
    (h : ∀ t, t < len → a.at' (off₁ + t) = b.at' (off₂ + t)) : a.slice off₁ len = b.slice off₂ len := by
  simp only [slice]
  apply List.map_congr_left
  intro t ht
  exact h t (List.mem_range.mp ht)

theorem slice_congr {a b : UInt64Array} {off len : Nat}
    (h : ∀ t, t < len → a.at' (off + t) = b.at' (off + t)) : a.slice off len = b.slice off len :=
  slice_congr' h

/-- `slice` only depends on the elements in range: writing outside the range changes nothing. -/
theorem slice_set_of_not_mem (a : UInt64Array) (i : UInt64) (v : UInt64) (hi) (off len : Nat)
    (h : i.toNat < off ∨ off + len ≤ i.toNat) : (a.set i v hi).slice off len = a.slice off len := by
  apply slice_congr
  intro t ht
  rw [at'_set_ne]
  omega

theorem take_slice (a : UInt64Array) (off l₁ l₂ : Nat) :
    (a.slice off (l₁ + l₂)).take l₁ = a.slice off l₁ := by
  rw [slice_add, List.take_left' (by simp)]

theorem drop_slice (a : UInt64Array) (off l₁ l₂ : Nat) :
    (a.slice off (l₁ + l₂)).drop l₁ = a.slice (off + l₁) l₂ := by
  rw [slice_add, List.drop_left' (by simp)]

theorem slice_eq_toList (a : UInt64Array) : a.slice 0 a.size = a.data.toList := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    have : i < a.data.size := by simpa using h₂
    simp [slice, at', Array.getD, this]

end UInt64Array
