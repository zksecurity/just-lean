import MergeSort.BottomUp
/-! Does a `for` loop with a single mutable array compile without per-iteration allocation? -/
open UInt64Array

/-- copy `src[0,n)` into `out` with a `for` loop and one `let mut` -/
def copyFor (src : UInt64Array) (out : UInt64Array) : UInt64Array := Id.run do
  let mut out := out
  for h : i in [0:src.size] do
    out := out.set i.toUInt64 (src.get i.toUInt64 (by sorry)) (by sorry)
  return out

/-- same, tail recursive -/
def copyRec (src : UInt64Array) (i : UInt64) (out : UInt64Array) : UInt64Array :=
  if h : i.toNat < src.size then copyRec src (i + 1) (out.set i (src.get i h) (by sorry)) else out
termination_by src.size - i.toNat
decreasing_by sorry

/-- a `for` loop with two mutable variables (array + running sum) -/
def sumFor (src : UInt64Array) (out : UInt64Array) : UInt64Array × UInt64 := Id.run do
  let mut out := out
  let mut s : UInt64 := 0
  for h : i in [0:src.size] do
    let v := src.get i.toUInt64 (by sorry)
    s := s + v
    out := out.set i.toUInt64 v (by sorry)
  return (out, s)

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 10000000
  let src := UInt64Array.zeros n
  let time (label : String) (f : Unit → UInt64Array) : IO Unit := do
    let t0 ← IO.monoNanosNow
    let _ ← IO.lazyPure f
    let t1 ← IO.monoNanosNow
    IO.println s!"{label}: {(t1 - t0).toFloat / 1000000.0} ms"
  time "for loop, one let mut (array)       " (fun _ => copyFor src (zeros n))
  time "tail recursion                       " (fun _ => copyRec src 0 (zeros n))
  time "for loop, two let mut (array + sum)  " (fun _ => (sumFor src (zeros n)).1)
