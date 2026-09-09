import MergeSort.BottomUp
/-! Performance experiment: the same bottom-up pass written in `do` notation (Id monad). -/
open UInt64Array
namespace DoStyle

/-- merge src[i,mid) and src[j,hi) into dst[k,hi), `do`-style -/
def mergeRun (mid hi : UInt64) (i j k : UInt64) (src dst : UInt64Array) : UInt64Array := Id.run do
  let mut dst := dst
  let mut i := i
  let mut j := j
  let mut k := k
  while k < hi do
    if i < mid && (j ≥ hi || src.get i (by sorry) ≤ src.get j (by sorry)) then
      dst := dst.set k (src.get i (by sorry)) (by sorry)
      i := i + 1
    else
      dst := dst.set k (src.get j (by sorry)) (by sorry)
      j := j + 1
    k := k + 1
  return dst

def sort (xs : UInt64Array) : UInt64Array := Id.run do
  let n : UInt64 := xs.size.toUInt64
  let mut src := xs
  let mut dst := zeros xs.size
  let mut w : UInt64 := 1
  while w < n do
    let mut lo : UInt64 := 0
    while lo < n do
      let mid := if lo + w ≤ n then lo + w else n
      let hi := if lo + 2 * w ≤ n then lo + 2 * w else n
      dst := mergeRun mid hi lo mid lo src dst
      lo := lo + 2 * w
    let tmp := src
    src := dst
    dst := tmp
    w := w * 2
  return src

end DoStyle

def gen (n : Nat) (seed : UInt64) : Array UInt64 := Id.run do
  let mut s := seed
  let mut out := Array.mkEmpty n
  for _ in [0:n] do
    s := s ^^^ (s >>> 12); s := s ^^^ (s <<< 25); s := s ^^^ (s >>> 27)
    out := out.push (s * 0x2545F4914F6CDD1D)
  return out

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 1000000
  let xs := gen n 42
  let ref := xs.qsort (· < ·)
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure (fun _ => DoStyle.sort (UInt64Array.ofArray xs))
  let t1 ← IO.monoNanosNow
  IO.println s!"do-style bottom-up: {(t1 - t0).toFloat / 1000000.0} ms [{if r.toArray == ref then "exact match" else "WRONG"}]"
  if h : (UInt64Array.ofArray xs).size < 2 ^ 62 then
    let t0 ← IO.monoNanosNow
    let r ← IO.lazyPure (fun _ => MergeSort.BottomUp.sort (UInt64Array.ofArray xs) h)
    let t1 ← IO.monoNanosNow
    IO.println s!"verified bottom-up: {(t1 - t0).toFloat / 1000000.0} ms [{if r.toArray == ref then "exact match" else "WRONG"}]"
