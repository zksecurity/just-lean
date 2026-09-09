import MergeSort.Fast
import MergeSort.BottomUp
import MergeSort.SmallRuns
import MergeSort.BidiSort
import MergeSort.Blocked
import MergeSort.Adaptive
import MergeSort.Net4
import MergeSort.SmallRuns
open MergeSort

/-- Run former: verified `sort8P` on every full block of 8, threading both buffers (timing only;
    the tail is left as is). Returns (modified src, dst with sorted 8-runs). -/
def sort8All (n lo : UInt64) (src dst : UInt64Array) (hssz : src.size < 2 ^ 64) (hdsz : dst.size < 2 ^ 64)
    (hs : n.toNat ≤ src.size) (hd : n.toNat ≤ dst.size) :
    { p : UInt64Array × UInt64Array // p.1.size = src.size ∧ p.2.size = dst.size } :=
  if h : lo < n ∧ 8 ≤ n - lo then
    have h2 : lo.toNat < n.toNat := h.1
    have h1 : lo.toNat + 8 ≤ n.toNat := by have := UInt64.le_iff_toNat_le.mp h.2; u64
    let r := BottomUp.sort8P lo src dst hssz hdsz (by omega) (by omega)
    let q := sort8All n (lo + 8) r.1.1 r.1.2 (by rw [r.2.1]; exact hssz) (by rw [r.2.2]; exact hdsz) (by rw [r.2.1]; exact hs) (by rw [r.2.2]; exact hd)
    ⟨q.1, q.2.1.trans r.2.1, q.2.2.trans r.2.2⟩
  else ⟨(src, dst), rfl, rfl⟩
termination_by n.toNat - lo.toNat
decreasing_by u64

def gen (n : Nat) (seed : UInt64) : Array UInt64 := Id.run do
  let mut s := seed
  let mut out := Array.mkEmpty n
  for _ in [0:n] do
    s := s ^^^ (s >>> 12); s := s ^^^ (s <<< 25); s := s ^^^ (s >>> 27)
    out := out.push (s * 0x2545F4914F6CDD1D)
  return out

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 1000000
  let shape := (args.drop 1).headD "random"
  let xs0 := gen n 42
  let xs : Array UInt64 :=
    if shape == "runs8" then
      let r := max 1 (n / 8)
      Id.run do
        let mut out := Array.mkEmpty n
        let mut i := 0
        while i < n do
          out := out ++ (xs0.extract i (min n (i + r))).qsort (· < ·)
          i := i + r
        return out
    else if shape == "swaps1" then Id.run do
      let mut v := xs0.qsort (· < ·)
      let mut s : UInt64 := 7
      for _ in [0:n / 100] do
        s := s ^^^ (s >>> 12); s := s ^^^ (s <<< 25); s := s ^^^ (s >>> 27)
        let i := ((s * 0x2545F4914F6CDD1D) % n.toUInt64).toNat
        s := s ^^^ (s >>> 12); s := s ^^^ (s <<< 25); s := s ^^^ (s >>> 27)
        let j := ((s * 0x2545F4914F6CDD1D) % n.toUInt64).toNat
        v := v.swapIfInBounds i j
      return v
    else if shape == "sawtooth" then Id.run do
      let mut out := Array.mkEmpty n
      let mut i := 0
      while i < n do
        out := out ++ (xs0.extract i (min n (i + 1000))).qsort (· < ·)
        i := i + 1000
      return out
    else xs0
  let us ← IO.lazyPure (fun _ => UInt64Array.ofArray xs)
  IO.println s!"n = {n} shape = {shape}"
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
    have hn : us.size.toUInt64.toNat = us.size := by simp; omega
    let r8 ← IO.lazyPure (fun _ => sort8All us.size.toUInt64 0 us (UInt64Array.zeros us.size) (by omega) (by simp; omega) (by rw [hn]; omega) (by rw [hn, UInt64Array.size_zeros]; omega))
    let t1 ← IO.monoNanosNow
    IO.println s!"run former: verified sort8 on all blocks of 8: {(t1 - t0).toFloat / 1000000.0} ms [size {r8.1.2.size}]"
    if us.size % 8 == 0 then
      let ref8 := xs.qsort (· < ·)
      let t0 ← IO.monoNanosNow
      let rs ← IO.lazyPure (fun _ =>
        let p := sort8All us.size.toUInt64 0 us (UInt64Array.zeros us.size) (by omega) (by simp; omega) (by rw [hn]; omega) (by rw [hn, UInt64Array.size_zeros]; omega)
        (BottomUp.widthLoop2 us.size.toUInt64 8 p.1.2 p.1.1 (by omega) (by rw [p.2.2, UInt64Array.size_zeros, hn]) (by rw [p.2.1, hn]) (by simp)).1)
      let t1 ← IO.monoNanosNow
      IO.println s!"sort8 runs + bidi width loop from 8 (verified pieces, unverified glue): {(t1 - t0).toFloat / 1000000.0} ms [{if rs.toArray == ref8 then "exact match" else "WRONG"}]"
    if h8 : 8 < us.size then
      let t0 ← IO.monoNanosNow
      let ri ← IO.lazyPure (fun _ => BottomUp.sortBlocks us.size.toUInt64 8 0 us (by omega) (by rw [hn]; omega) (by rw [hn]; omega) (by rw [hn]; simp; omega))
      let t1 ← IO.monoNanosNow
      IO.println s!"run former: verified insertion sort on blocks of 8: {(t1 - t0).toFloat / 1000000.0} ms [size {ri.1.size}]"
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
