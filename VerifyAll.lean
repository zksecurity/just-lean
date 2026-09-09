import MergeSort.BottomUp
import MergeSort.SmallRuns
import MergeSort.BidiSort
import MergeSort.Blocked
import MergeSort.Adaptive
/-! Exact cross-check of both verified sorts against `Array.qsort` on many sizes. -/
def gen (n : Nat) (seed : UInt64) : Array UInt64 := Id.run do
  let mut s := seed
  let mut out := Array.mkEmpty n
  for _ in [0:n] do
    s := s ^^^ (s >>> 12); s := s ^^^ (s <<< 25); s := s ^^^ (s >>> 27)
    out := out.push (s * 0x2545F4914F6CDD1D)
  return out

def main : IO Unit := do
  let bad ← IO.mkRef 0
  let sizes := [0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 100, 127, 128, 129, 255, 256, 257,
    1000, 1023, 1024, 1025, 4095, 4097, 12345, 65535, 65536, 65537, 100000, 1000000]
  for n in sizes do
    for seed in [1, 42, 7] do
      let xs := gen n (seed + n.toUInt64)
      -- also a few structured inputs: sorted, reversed, all-equal
      let sorted := xs.qsort (· < ·)
      -- (input, expected output); qsort is quadratic on equal keys, so references are explicit
      let inputs := [(xs, sorted), (sorted, sorted), (sorted.reverse, sorted), (Array.replicate n 5, Array.replicate n 5)]
      for (inp, ref) in inputs do
        let a := UInt64Array.ofArray inp
        if h : a.size < 2 ^ 62 then
          let r1 := (MergeSort.Fast.sort a (by omega)).toArray
          let r2 := (MergeSort.BottomUp.sort a h).toArray
          let r3 := (MergeSort.BottomUp.sort16 a h).toArray
          let r4 := (MergeSort.BottomUp.sort2 a h).toArray
          if r4 != ref then bad.modify (· + 1); IO.println s!"MISMATCH sort2 n={n}"
          let r5 := (MergeSort.BottomUp.sortBlocked a h).toArray
          if r5 != ref then bad.modify (· + 1); IO.println s!"MISMATCH sortBlocked n={n}"
          let r6 := (MergeSort.BottomUp.sortAdaptive a h).toArray
          if r6 != ref then bad.modify (· + 1); IO.println s!"MISMATCH sortAdaptive n={n}"
          let r7 := (MergeSort.BottomUp.sortAdaptive2 a h).toArray
          if r7 != ref then bad.modify (· + 1); IO.println s!"MISMATCH sortAdaptive2 n={n}"
          if r1 != ref then bad.modify (· + 1); IO.println s!"MISMATCH Fast n={n}"
          if r2 != ref then bad.modify (· + 1); IO.println s!"MISMATCH BottomUp n={n}"
          if r3 != ref then bad.modify (· + 1); IO.println s!"MISMATCH sort16 n={n}"
  IO.println s!"checked {sizes.length} sizes x 3 seeds x 4 input shapes; mismatches: {← bad.get}"
