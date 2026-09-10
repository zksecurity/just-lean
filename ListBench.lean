import MergeSort.Simple
/-! `lake exe listbench [n]`: time the Part 1 list merge sort on `n` pseudo-random numbers. -/
open MergeSort

def gen (n : Nat) (seed : UInt64) : List UInt64 := Id.run do
  let mut s := seed
  let mut out : Array UInt64 := Array.mkEmpty n
  for _ in [0:n] do
    s := s ^^^ (s >>> 12); s := s ^^^ (s <<< 25); s := s ^^^ (s >>> 27)
    out := out.push (s * 0x2545F4914F6CDD1D)
  return out.toList

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 1000000
  let xs ← IO.lazyPure (fun _ => gen n 42)
  let t0 ← IO.monoNanosNow
  let ys ← IO.lazyPure (fun _ => mergeSort (fun a b => decide (a ≤ b)) xs)
  let t1 ← IO.monoNanosNow
  IO.println s!"Part 1 list merge sort, {n} UInt64: {(t1 - t0).toFloat / 1000000.0} ms; first = {ys.head?}"
