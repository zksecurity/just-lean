import MergeSort.Fast
import MergeSort.BottomUp
import MergeSort.SmallRuns
import MergeSort.BidiSort
import MergeSort.Blocked
import MergeSort.Adaptive
open MergeSort

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
  let us := UInt64Array.ofArray xs
  IO.println s!"n = {n}"
  let t0 ← IO.monoNanosNow
  if h : us.size < 2 ^ 63 then
  let r ← IO.lazyPure (fun _ => Fast.sort us h)
  let t1 ← IO.monoNanosNow
  let out := r.toArray
  let ref := xs.qsort (· < ·)
  IO.println s!"Fast.sort (total, proof-carrying): {(t1 - t0).toFloat / 1000000.0} ms [{if out == ref then "exact match" else "WRONG"}]"
  else IO.println "too big"
  if h : us.size < 2 ^ 62 then
    let t0 ← IO.monoNanosNow
    let r ← IO.lazyPure (fun _ => BottomUp.sort us h)
    let t1 ← IO.monoNanosNow
    let out := r.toArray
    let ref := xs.qsort (· < ·)
    IO.println s!"BottomUp.sort (total, proof-carrying): {(t1 - t0).toFloat / 1000000.0} ms [{if out == ref then "exact match" else "WRONG"}]"
    let t0 ← IO.monoNanosNow
    let r ← IO.lazyPure (fun _ => BottomUp.sort16 us h)
    let t1 ← IO.monoNanosNow
    let out := r.toArray
    IO.println s!"BottomUp.sort16 (insertion runs of 16): {(t1 - t0).toFloat / 1000000.0} ms [{if out == ref then "exact match" else "WRONG"}]"
    let t0 ← IO.monoNanosNow
    let r ← IO.lazyPure (fun _ => BottomUp.sort2 us h)
    let t1 ← IO.monoNanosNow
    let out := r.toArray
    IO.println s!"BottomUp.sort2 (bidirectional merge): {(t1 - t0).toFloat / 1000000.0} ms [{if out == ref then "exact match" else "WRONG"}]"
    let t0 ← IO.monoNanosNow
    let r ← IO.lazyPure (fun _ => BottomUp.sortBlocked us h)
    let t1 ← IO.monoNanosNow
    let out := r.toArray
    IO.println s!"BottomUp.sortBlocked (bidi + cache blocks): {(t1 - t0).toFloat / 1000000.0} ms [{if out == ref then "exact match" else "WRONG"}]"
    let sortedIn := UInt64Array.ofArray ref
    if h2 : sortedIn.size < 2 ^ 62 then
      let t0 ← IO.monoNanosNow
      let r ← IO.lazyPure (fun _ => BottomUp.sortAdaptive sortedIn h2)
      let t1 ← IO.monoNanosNow
      IO.println s!"BottomUp.sortAdaptive on presorted input: {(t1 - t0).toFloat / 1000000.0} ms [{if r.toArray == ref then "exact match" else "WRONG"}]"
    let revIn := UInt64Array.ofArray ref.reverse
    if h3 : revIn.size < 2 ^ 62 then
      let t0 ← IO.monoNanosNow
      let r ← IO.lazyPure (fun _ => BottomUp.sortAdaptive2 revIn h3)
      let t1 ← IO.monoNanosNow
      IO.println s!"BottomUp.sortAdaptive2 on reversed input: {(t1 - t0).toFloat / 1000000.0} ms [{if r.toArray == ref then "exact match" else "WRONG"}]"
      let t0 ← IO.monoNanosNow
      let r ← IO.lazyPure (fun _ => BottomUp.sortAdaptive3 revIn h3)
      let t1 ← IO.monoNanosNow
      IO.println s!"BottomUp.sortAdaptive3 (single scan) on reversed input: {(t1 - t0).toFloat / 1000000.0} ms [{if r.toArray == ref then "exact match" else "WRONG"}]"
      let t0 ← IO.monoNanosNow
      let r ← IO.lazyPure (fun _ => BottomUp.sortAdaptive3 us h)
      let t1 ← IO.monoNanosNow
      IO.println s!"BottomUp.sortAdaptive3 (single scan) on random input: {(t1 - t0).toFloat / 1000000.0} ms [{if r.toArray == ref then "exact match" else "WRONG"}]"
