/-!
# An unboxed array of `UInt64`

Lean's runtime has *scalar arrays* (`lean_sarray`): flat buffers of fixed-size elements. Core exposes
two of them, `ByteArray` (1-byte elements) and `FloatArray` (8-byte elements). `Array UInt64` is not
one of them: its elements are heap-allocated boxes, which is why sorting it is slow.

Here we expose an 8-byte scalar array of `UInt64`, following the exact recipe core uses for
`FloatArray`: the *model* is a structure over `Array UInt64` (which the proofs use), and every runtime
operation is an `extern` that works on the flat buffer.
-/

/-- Discharges `UInt64` index arithmetic (defined at the end of this file, once the size lemmas
    exist). It is the default tactic for every bounds proof, so call sites can omit them. -/
syntax "u64" : tactic

/-- An unboxed array of `UInt64`. The field is the *model* used by proofs; at runtime the value is a
    flat `lean_sarray` of 8-byte elements, and every operation below is implemented by inline C. -/
structure UInt64Array where
  /-- The model: the elements as an ordinary `Array`. Never used at runtime. -/
  data : Array UInt64

attribute [extern "u64array_mk"] UInt64Array.mk
attribute [extern "u64array_data"] UInt64Array.data

namespace UInt64Array

@[extern c inline "lean_box(lean_sarray_size(#1))", reducible]
def size (a : @& UInt64Array) : Nat := a.data.size

/-- Read element `i`. No bounds check at runtime: the proof `h` is the bounds check. -/
@[extern c inline "((uint64_t*)lean_sarray_cptr(#1))[#2]"]
def get (a : @& UInt64Array) (i : UInt64) (h : i.toNat < a.size := by u64) : UInt64 := a.data[i.toNat]

/-- Write element `i`. In place if `a` is unshared, otherwise copy-on-write. -/
@[extern c inline "({ lean_object* _a = #1; if (__builtin_expect(!lean_is_exclusive(_a), 0)) _a = lean_copy_float_array(_a); ((uint64_t*)lean_sarray_cptr(_a))[#2] = #3; _a; })"]
def set (a : UInt64Array) (i : UInt64) (v : UInt64) (h : i.toNat < a.size := by u64) : UInt64Array :=
  ⟨a.data.set i.toNat v h⟩

/-- A zero-filled array of length `n`. -/
@[extern c inline "({ size_t _n = lean_unbox(#1); lean_object* _a = lean_alloc_sarray(8, _n, _n); __builtin_memset(lean_sarray_cptr(_a), 0, 8 * _n); _a; })"]
def zeros (n : @& Nat) : UInt64Array := ⟨Array.replicate n 0⟩

@[simp] theorem size_set (a : UInt64Array) (i : UInt64) (v : UInt64) (h) :
    (a.set i v h).size = a.size := Array.size_set h
@[simp] theorem size_zeros (n : Nat) : (zeros n).size = n := by simp [zeros, size]
@[simp] theorem size_mk (d : Array UInt64) : (mk d).size = d.size := rfl

/-- Two writes with one exclusivity check. Logically two `set`s; the C implements exactly that. -/
@[extern c inline "({ lean_object* _a = #1; if (__builtin_expect(!lean_is_exclusive(_a), 0)) _a = lean_copy_float_array(_a); uint64_t* _p = (uint64_t*)lean_sarray_cptr(_a); _p[#2] = #3; _p[#4] = #5; _a; })", reducible]
def set2 (a : UInt64Array) (i v j w : UInt64) (hi : i.toNat < a.size) (hj : j.toNat < a.size) : UInt64Array :=
  (a.set i v hi).set j w (by simpa using hj)

@[simp] theorem size_set2 (a : UInt64Array) (i v j w : UInt64) (hi hj) : (set2 a i v j w hi hj).size = a.size := by
  simp [set2]

/-- Four consecutive writes with one exclusivity check. Logically four `set`s. -/
@[extern c inline "({ lean_object* _a = #2; if (__builtin_expect(!lean_is_exclusive(_a), 0)) _a = lean_copy_float_array(_a); uint64_t* _p = (uint64_t*)lean_sarray_cptr(_a) + #1; _p[0] = #3; _p[1] = #4; _p[2] = #5; _p[3] = #6; _a; })"]
def set4 (lo : UInt64) (a : UInt64Array) (v0 v1 v2 v3 : UInt64) (h : lo.toNat + 4 ≤ a.size) (hsz : a.size < 2 ^ 64) : UInt64Array :=
  have e1 : (lo + 1).toNat = lo.toNat + 1 := by simp only [UInt64.toNat_add, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  have e2 : (lo + 2).toNat = lo.toNat + 2 := by simp only [UInt64.toNat_add, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  have e3 : (lo + 3).toNat = lo.toNat + 3 := by simp only [UInt64.toNat_add, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  (((a.set lo v0 (by omega)).set (lo + 1) v1 (by simp; omega)).set (lo + 2) v2 (by simp; omega)).set (lo + 3) v3 (by simp; omega)

@[simp] theorem size_set4 (lo : UInt64) (a : UInt64Array) (v0 v1 v2 v3 : UInt64) (h hsz) : (set4 lo a v0 v1 v2 v3 h hsz).size = a.size := by
  simp [set4]

theorem get_set (a : UInt64Array) (i j : UInt64) (v : UInt64) (hi hj) :
    (a.set i v hi).get j hj = if i = j then v else a.get j (by simpa using hj) := by
  simp only [get, set, Array.getElem_set]
  by_cases h : i = j
  · simp [h]
  · have : i.toNat ≠ j.toNat := fun e => h (UInt64.toNat.inj e)
    simp [h, this]

@[simp] theorem get_set_self (a : UInt64Array) (i : UInt64) (v : UInt64) (hi hj) :
    (a.set i v hi).get i hj = v := by simp [get_set]
theorem get_set_ne (a : UInt64Array) (i j : UInt64) (v : UInt64) (hi hj) (h : i ≠ j) :
    (a.set i v hi).get j hj = a.get j (by simpa using hj) := by simp [get_set, h]

@[simp] theorem get_zeros (n : Nat) (i : UInt64) (h) : (zeros n).get i h = 0 := by
  simp [get, zeros]

/-- Convenience conversions (used by tests and benchmarks, not by the sort). -/
def ofArray (xs : Array UInt64) : UInt64Array :=
  (go 0 ⟨zeros xs.size, by simp⟩).1
where
  go (k : Nat) (a : { a : UInt64Array // a.size = xs.size }) : { a : UInt64Array // a.size = xs.size } :=
    if h : k < xs.size then
      go (k + 1) ⟨a.1.set k.toUInt64 xs[k] (by simp [a.2]; omega), by simp [a.2]⟩
    else a
  termination_by xs.size - k

def toArray (a : UInt64Array) : Array UInt64 :=
  go 0 (Array.mkEmpty a.size)
where
  go (k : Nat) (out : Array UInt64) : Array UInt64 :=
    if h : k < a.size then
      go (k + 1) (out.push (a.get k.toUInt64 (by simp; omega)))
    else out
  termination_by a.size - k

end UInt64Array

macro_rules
  | `(tactic| u64) => `(tactic|
    ((try simp only [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_ofNat,
        UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, Nat.reducePow, Nat.reduceMod,
        UInt64Array.size_set, UInt64Array.size_set2, UInt64Array.size_set4, UInt64Array.size_zeros] at *)
     <;> omega))
