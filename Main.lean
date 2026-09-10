import MergeSort.DriftSort
/-! `lake exe sortdemo [n]`: generate `n` pseudo-random 64-bit numbers, sort them with the verified
    sort, and print the smallest one plus the time taken. -/
open MergeSort

/-- xorshift64* pseudo-random numbers -/
def gen (n : Nat) (seed : UInt64) : Array UInt64 := Id.run do
  let mut s := seed
  let mut out := Array.mkEmpty n
  for _ in [0:n] do
    s := s ^^^ (s >>> 12); s := s ^^^ (s <<< 25); s := s ^^^ (s >>> 27)
    out := out.push (s * 0x2545F4914F6CDD1D)
  return out

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 1000000
  let xs := UInt64Array.ofArray (gen n 42)
  if h : xs.size < 2 ^ 62 then
    let t0 ← IO.monoNanosNow
    let ys ← IO.lazyPure (fun _ => DriftSort.sort xs h)
    let t1 ← IO.monoNanosNow
    IO.println s!"sorted {n} numbers in {(t1 - t0).toFloat / 1000000.0} ms; smallest = {ys.toArray[0]?}"
  else IO.println "too many numbers"
