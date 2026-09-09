import MergeSort.BidiSort
import MergeSort.SmallRuns
import MergeSort.Adaptive
import MergeSort.Blocked
/-!
# Experiment (unverified prototype): natural-run merge sort ("driftsort-lite", Part 3 step 1–3)
Detect maximal ascending / strictly descending runs (descending ones reversed in place), extend short
runs to 32 with insertion sort, then merge adjacent runs level by level with the *verified* `mergeKernel`
(bidirectional when the two runs have equal length). Only the run scan uses `partial`.
-/
open UInt64Array MergeSort MergeSort.BottomUp
namespace NR

/-- Scan the ascending run starting at `lo` (elements already checked up to `i`). -/
partial def ascEnd (n i : UInt64) (a : UInt64Array) (hsz : a.size < 2 ^ 64) (hn : n.toNat ≤ a.size) (hi : 1 ≤ i.toNat) : UInt64 :=
  if h : i < n then
    have h1 : i.toNat < n.toNat := h
    if a.get (i - 1) ≤ a.get i then ascEnd n (i + 1) a hsz hn (by u64) else i
  else i

partial def descEnd (n i : UInt64) (a : UInt64Array) (hsz : a.size < 2 ^ 64) (hn : n.toNat ≤ a.size) (hi : 1 ≤ i.toNat) : UInt64 :=
  if h : i < n then
    have h1 : i.toNat < n.toNat := h
    if a.get i < a.get (i - 1) then descEnd n (i + 1) a hsz hn (by u64) else i
  else i

/-- Collect run starts into `runs` (each run sorted in place); returns `(runs ++ [n], a)`. -/
partial def collectRuns (minRun n lo : UInt64) (a : UInt64Array) (runs : Array UInt64)
    (hsz : a.size < 2 ^ 64) (hn : n.toNat ≤ a.size) : Array UInt64 × UInt64Array :=
  if h : lo < n then
    have h1 : lo.toNat < n.toNat := h
    have h : lo < n ∧ a.size < 2 ^ 64 ∧ n.toNat ≤ a.size := ⟨h, hsz, hn⟩
    let runs := runs.push lo
    if h4 : lo + 1 < n then
      have : lo.toNat + 1 < n.toNat := by have := UInt64.lt_iff_toNat_lt.mp h4; u64
      let x := a.get lo
      let y := a.get (lo + 1)
      let (hi, a) :=
        if y < x then
          let hi := descEnd n (lo + 2) a hsz hn (by u64)
          if h2 : hi.toNat ≤ a.size ∧ lo.toNat ≤ hi.toNat then (hi, (reverseRange lo hi a h.2.1 h2.1 h2.2).1) else (hi, a)
        else (ascEnd n (lo + 2) a hsz hn (by u64), a)
      -- extend short runs
      let (hi, a) :=
        if hi - lo < minRun then
          let hi' := if lo + minRun ≤ n then lo + minRun else n
          if h3 : a.size < 2 ^ 64 ∧ hi'.toNat ≤ a.size ∧ lo.toNat ≤ hi.toNat then
            (hi', (insertionSortRange lo hi' hi a h3.1 h3.2.1 h3.2.2).1)
          else (hi, a)
        else (hi, a)
      if h5 : a.size < 2 ^ 64 ∧ n.toNat ≤ a.size then collectRuns minRun n hi a runs h5.1 h5.2 else (runs.push n, a)
    else (runs.push n, a)
  else (runs.push n, a)

/-- Count natural runs (ascending or strictly descending) without writing; read-only scan. -/
partial def countRuns (n lo : UInt64) (a : @& UInt64Array) (acc limit : UInt64)
    (hsz : a.size < 2 ^ 64) (hn : n.toNat ≤ a.size) : UInt64 :=
  if h : lo < n ∧ acc ≤ limit then
    have h1 : lo.toNat < n.toNat := h.1
    if h4 : lo + 1 < n then
      have : lo.toNat + 1 < n.toNat := by have := UInt64.lt_iff_toNat_lt.mp h4; u64
      let hi := if a.get (lo + 1) < a.get lo then descEnd n (lo + 2) a hsz hn (by u64) else ascEnd n (lo + 2) a hsz hn (by u64)
      countRuns n hi a (acc + 1) limit hsz hn
    else acc + 1
  else acc

/-- Copy `[lo, hi)` from `src` to `dst`. -/
def copyRange (lo hi : UInt64) (src dst : UInt64Array) : UInt64Array :=
  if h : lo < hi ∧ hi.toNat ≤ src.size ∧ hi.toNat ≤ dst.size ∧ src.size < 2 ^ 64 ∧ dst.size < 2 ^ 64 then
    have : lo.toNat < hi.toNat := h.1
    copyRange (lo + 1) hi src (dst.set lo (src.get lo))
  else dst
termination_by hi.toNat - lo.toNat
decreasing_by u64

/-- One level: merge runs pairwise from `src` into `dst`; new run starts collected into `out`. -/
def mergeLevel (runs : Array UInt64) (i : Nat) (src dst : UInt64Array) (out : Array UInt64) :
    Array UInt64 × UInt64Array × UInt64Array :=
  if h : i + 1 < runs.size then
    let lo := runs[i]
    let mid := runs[i + 1]
    if h2 : i + 2 < runs.size then
      let hi := runs[i + 2]
      let dst :=
        if hh : dst.size < 2 ^ 64 ∧ hi.toNat ≤ src.size ∧ hi.toNat ≤ dst.size ∧ lo.toNat ≤ mid.toNat ∧ mid.toNat ≤ hi.toNat
            ∧ src.size < 2 ^ 64 ∧ lo.toNat < mid.toNat ∧ mid.toNat < hi.toNat then
          -- fast path: the two runs are already in order
          if src.get (mid - 1) (by have := hh.2.2.2.2.2.2; have := hh.2.1; u64) ≤ src.get mid (by have := hh.2.2.2.2.2.2.2; have := hh.2.1; u64) then
            copyRange lo hi src dst
          else
            (mergeKernel lo mid hi src dst hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2.1).1
        else if hh : dst.size < 2 ^ 64 ∧ hi.toNat ≤ src.size ∧ hi.toNat ≤ dst.size ∧ lo.toNat ≤ mid.toNat ∧ mid.toNat ≤ hi.toNat then
          (mergeKernel lo mid hi src dst hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2).1
        else dst
      mergeLevel runs (i + 2) src dst (out.push lo)
    else
      -- odd run left over: copy
      (out.push lo |>.push mid, src, copyRange lo mid src dst)
  else (out, src, dst)
termination_by runs.size - i

partial def mergeAll (runs : Array UInt64) (src dst : UInt64Array) : UInt64Array :=
  if runs.size ≤ 2 then src
  else
    let (runs', src, dst) := mergeLevel runs 0 src dst (Array.mkEmpty (runs.size / 2 + 2))
    -- ensure the sentinel `n` is at the end
    let runs' := if runs'.size > 0 && runs'[runs'.size - 1]! == runs[runs.size - 1]! then runs' else runs'.push runs[runs.size - 1]!
    mergeAll runs' dst src

def sortNatural (minRun : UInt64) (xs : UInt64Array) : UInt64Array :=
  let n := xs.size.toUInt64
  if h : xs.size < 2 ^ 62 then
    have hn : n.toNat ≤ xs.size := by simp [n]; omega
    let (runs, a) := collectRuns minRun n 0 xs (Array.mkEmpty 1024) (by omega) hn
    mergeAll runs a (zeros xs.size)
  else xs

/-- Hybrid: count natural runs first; unstructured input (average run < `minRun`) goes to the verified
    cache-blocked sort, structured input to the natural-run merge. -/
def sortHybrid (minRun : UInt64) (xs : UInt64Array) : UInt64Array :=
  let n := xs.size.toUInt64
  if h : xs.size < 2 ^ 62 then
    have hn : n.toNat ≤ xs.size := by simp [n]; omega
    let k := countRuns n 0 xs 0 (n / minRun) (by omega) hn
    if k * minRun > n then sortBlocked xs h
    else sortNatural minRun xs
  else xs

end NR

def gen (n : Nat) (seed : UInt64) : Array UInt64 := Id.run do
  let mut s := seed
  let mut out := Array.mkEmpty n
  for _ in [0:n] do
    s := s ^^^ (s >>> 12); s := s ^^^ (s <<< 25); s := s ^^^ (s >>> 27)
    out := out.push (s * 0x2545F4914F6CDD1D)
  return out

def shapeOf (shape : String) (n : Nat) (xs0 : Array UInt64) : Array UInt64 :=
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
  else if shape == "reversed" then xs0.qsort (· < ·) |>.reverse
  else xs0

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 1000000
  for shape in ["random", "runs8", "swaps1", "sawtooth", "reversed"] do
    let xs := shapeOf shape n (gen n 42)
    let ref := xs.qsort (· < ·)
    let us := UInt64Array.ofArray xs
    IO.println s!"n = {n} shape = {shape}"
    if h : us.size < 2 ^ 62 then
      let t0 ← IO.monoNanosNow
      let r ← IO.lazyPure (fun _ => BottomUp.sortBlocked us h)
      let t1 ← IO.monoNanosNow
      IO.println s!"  sortBlocked (verified):      {(t1 - t0).toFloat / 1000000.0} ms [{if r.toArray == ref then "exact match" else "WRONG"}]"
      for minRun in [32] do
        let t0 ← IO.monoNanosNow
        let r ← IO.lazyPure (fun _ => NR.sortNatural minRun us)
        let t1 ← IO.monoNanosNow
        IO.println s!"  natural runs (minRun {minRun}): {(t1 - t0).toFloat / 1000000.0} ms [{if r.toArray == ref then "exact match" else "WRONG"}]"
        let t0 ← IO.monoNanosNow
        let r ← IO.lazyPure (fun _ => NR.sortHybrid minRun us)
        let t1 ← IO.monoNanosNow
        IO.println s!"  hybrid (count runs, then natural or blocked): {(t1 - t0).toFloat / 1000000.0} ms [{if r.toArray == ref then "exact match" else "WRONG"}]"
      let t0 ← IO.monoNanosNow
      let k ← IO.lazyPure (fun _ => NR.countRuns us.size.toUInt64 0 us 0 (us.size.toUInt64 / 32) (by omega) (by simp; omega))
      let t1 ← IO.monoNanosNow
      IO.println s!"  countRuns: {k} runs in {(t1 - t0).toFloat / 1000000.0} ms"
