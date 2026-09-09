import MergeSort.BottomUp
import MergeSort.GenericU64
/-! Does abstracting the comparison cost anything? Same loops as `BottomUp`, comparison passed
    (a) as a function argument, (b) as a type class, with and without `@[specialize]`. -/
open UInt64Array MergeSort

class Cmp (α : Type) where
  le : α → α → Bool

instance : Cmp UInt64 := ⟨fun a b => decide (a ≤ b)⟩

namespace G

@[specialize, noinline] def mergeLoop (le : UInt64 → UInt64 → Bool) (mid hi i j k : UInt64) (src dst : UInt64Array)
    (hsz : dst.size < 2 ^ 64 := by u64)
    (hs : hi.toNat ≤ src.size := by u64) (hd : hi.toNat ≤ dst.size := by u64)
    (hmid : mid.toNat ≤ hi.toNat := by u64) (hi' : i.toNat ≤ mid.toNat := by u64)
    (hj : j.toNat ≤ hi.toNat := by u64) (hinv : i.toNat + j.toNat = k.toNat + mid.toNat := by u64) :
    { b : UInt64Array // b.size = dst.size } :=
  if hk : k < hi then
    have hk : k.toNat < hi.toNat := hk
    if hi'' : i < mid then
      have hi'' : i.toNat < mid.toNat := hi''
      if hj' : j < hi then
        have hj' : j.toNat < hi.toNat := hj'
        let x := src.get i
        let y := src.get j
        let takeLeft : Bool := le x y
        let di : UInt64 := if takeLeft then 1 else 0
        have hdi : di.toNat ≤ 1 := by show (if takeLeft then (1 : UInt64) else 0).toNat ≤ 1; split <;> decide
        Fast.castSize (mergeLoop le mid hi (i + di) (j + (1 - di)) (k + 1) src
          (dst.set k (if takeLeft then x else y))) (by simp)
      else
        Fast.castSize (mergeLoop le mid hi (i + 1) j (k + 1) src (dst.set k (src.get i))) (by simp)
    else
      have hi'' : ¬ i.toNat < mid.toNat := hi''
      Fast.castSize (mergeLoop le mid hi i (j + 1) (k + 1) src (dst.set k (src.get j))) (by simp)
  else ⟨dst, rfl⟩
termination_by hi.toNat - k.toNat
decreasing_by all_goals u64

@[specialize] def passLoop (le : UInt64 → UInt64 → Bool) (n w lo : UInt64) (src dst : UInt64Array)
    (hn : n.toNat < 2 ^ 62 := by u64) (hs : n.toNat ≤ src.size := by u64)
    (hd : n.toNat ≤ dst.size := by u64) (hdsz : dst.size < 2 ^ 64 := by u64)
    (hw : 1 ≤ w.toNat ∧ w.toNat < n.toNat := by u64) : { b : UInt64Array // b.size = dst.size } :=
  if h : lo < n then
    have h : lo.toNat < n.toNat := h
    let mid := if lo + w ≤ n then lo + w else n
    let hi := if lo + 2 * w ≤ n then lo + 2 * w else n
    have hmid : mid.toNat = min (lo.toNat + w.toNat) n.toNat := by
      show (if lo + w ≤ n then lo + w else n).toNat = _; split <;> u64
    have hhi : hi.toNat = min (lo.toNat + 2 * w.toNat) n.toNat := by
      show (if lo + 2 * w ≤ n then lo + 2 * w else n).toNat = _; split <;> u64
    let ⟨b, hb⟩ := mergeLoop le mid hi lo mid lo src dst
    Fast.castSize (passLoop le n w (lo + 2 * w) src b) hb
  else ⟨dst, rfl⟩
termination_by n.toNat - lo.toNat
decreasing_by u64

@[specialize] def widthLoop (le : UInt64 → UInt64 → Bool) (n w : UInt64) (src dst : UInt64Array)
    (hn : n.toNat < 2 ^ 62 := by u64) (hs : n.toNat = src.size := by u64)
    (hd : n.toNat = dst.size := by u64) (hw : 1 ≤ w.toNat := by u64) :
    { b : UInt64Array // b.size = src.size } :=
  if h : w < n then
    have h : w.toNat < n.toNat := h
    let ⟨b, hb⟩ := passLoop le n w 0 src dst
    Fast.castSize (widthLoop le n (2 * w) b src (hs := by rw [hb]; exact hd)) (by omega)
  else ⟨src, rfl⟩
termination_by n.toNat - w.toNat
decreasing_by u64

/-- (a) comparison as a function argument, specialized at the call site -/
def sortFn (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : UInt64Array :=
  let n : UInt64 := xs.size.toUInt64
  have hn : n.toNat = xs.size := by simp [n]; omega
  (widthLoop (fun a b => decide (a ≤ b)) n 1 xs (zeros xs.size)).1

/-- (b) comparison from a type class instance passed as an argument, specialized -/
@[specialize] def sortCls [inst : Cmp UInt64] (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : UInt64Array :=
  let n : UInt64 := xs.size.toUInt64
  have hn : n.toNat = xs.size := by simp [n]; omega
  (widthLoop (fun a b => inst.le a b) n 1 xs (zeros xs.size)).1

/-- (e) a named `@[inline]` comparison instead of a lambda -/
@[inline] def leNamed (a b : UInt64) : Bool := decide (a ≤ b)
def sortNamed (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : UInt64Array :=
  let n : UInt64 := xs.size.toUInt64
  have hn : n.toNat = xs.size := by simp [n]; omega
  (widthLoop leNamed n 1 xs (zeros xs.size)).1

/-- (f) generic pass/width loops specialised here, but the kernel instantiated in its own module -/
def sortSplit (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : UInt64Array :=
  let n : UInt64 := xs.size.toUInt64
  have hn : n.toNat = xs.size := by simp [n]; omega
  (MergeSort.G.widthLoop MergeSort.G.kernelU64 n 1 xs (zeros xs.size)).1

/-- (c) comparison passed through an opaque boundary: no specialization possible -/
@[noinline] def sortOpaque (le : UInt64 → UInt64 → Bool) (xs : UInt64Array) (hsz : xs.size < 2 ^ 62) : UInt64Array :=
  let n : UInt64 := xs.size.toUInt64
  have hn : n.toNat = xs.size := by simp [n]; omega
  (widthLoop le n 1 xs (zeros xs.size)).1

end G

def gen (n : Nat) (seed : UInt64) : Array UInt64 := Id.run do
  let mut s := seed
  let mut out := Array.mkEmpty n
  for _ in [0:n] do
    s := s ^^^ (s >>> 12); s := s ^^^ (s <<< 25); s := s ^^^ (s >>> 27)
    out := out.push (s * 0x2545F4914F6CDD1D)
  return out

def timeIt (label : String) (ref : Array UInt64) (f : Unit → UInt64Array) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  IO.println s!"{label}: {(t1 - t0).toFloat / 1000000.0} ms [{if r.toArray == ref then "exact match" else "WRONG"}]"

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 1000000
  let xs := gen n 42
  let ref := xs.qsort (· < ·)
  let us := UInt64Array.ofArray xs
  if h : us.size < 2 ^ 62 then
    for _ in [0:3] do
      timeIt "monomorphic BottomUp.sort (baseline)        " ref (fun _ => BottomUp.sort us h)
      timeIt "(a) le as function arg, @[specialize] + noinline mergeLoop" ref (fun _ => G.sortFn us h)
      timeIt "(b) le from type class Cmp, @[specialize]   " ref (fun _ => G.sortCls us h)
      timeIt "(e) le as named @[inline] def, @[specialize]  " ref (fun _ => G.sortNamed us h)
      timeIt "(f) generic loops, kernel instantiated in its own module" ref (fun _ => G.sortSplit us h)
      timeIt "(c) le as opaque closure (no specialization)" ref (fun _ => G.sortOpaque (fun a b => decide (a ≤ b)) us h)
      let dyn : UInt64 → UInt64 → Bool := if args.length > 5 then (fun a b => decide (a ≥ b)) else (fun a b => decide (a ≤ b))
      timeIt "(d) le chosen at runtime (true callback)    " ref (fun _ => G.sortOpaque dyn us h)
