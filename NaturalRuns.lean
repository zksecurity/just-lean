import MergeSort.BidiSort
import MergeSort.SmallRuns
import MergeSort.Adaptive
import MergeSort.Blocked
import MergeSort.SkipMerge
import MergeSort.FindRun
/-!
# Experiment (unverified prototype): natural-run merge sort ("driftsort-lite", Part 3 step 1–3)
Detect maximal ascending / strictly descending runs (descending ones reversed in place), extend short
runs to 32 with insertion sort, then merge adjacent runs level by level with the *verified* `mergeKernel`
(bidirectional when the two runs have equal length). Run detection (`findRun`) and every merge (`mergeKernelS`) are verified; the glue loops are total too (`termination_by` on the scan position / number of runs), so nothing here is `partial`.
-/
open UInt64Array MergeSort MergeSort.BottomUp
namespace NR

/-- Collect run starts into `runs` (each run sorted in place); returns `(runs ++ [n], a, d)`.
    `useBlocks`: extend short runs with the verified cache-blocked bottom-up sort (`blockPasses`) on
    `[lo, lo + minRun)` instead of insertion sort; needs the scratch buffer `d`. -/
def collectRunsB (useBlocks : Bool) (minRun n lo : UInt64) (a d : UInt64Array) (runs : Array UInt64)
    (hsz : a.size < 2 ^ 64) (hn : n.toNat ≤ a.size) : Array UInt64 × UInt64Array × UInt64Array :=
  if h : lo < n then
    have h1 : lo.toNat < n.toNat := h
    have h : lo < n ∧ a.size < 2 ^ 64 ∧ n.toNat ≤ a.size := ⟨h, hsz, hn⟩
    let runs := runs.push lo
    if h4 : lo + 1 < n then
      have : lo.toNat + 1 < n.toNat := by have := UInt64.lt_iff_toNat_lt.mp h4; u64
      -- verified run detection (`FindRun.lean`): descending runs are reversed in place
      let r := findRun lo n a hsz hn h1
      let hi := r.1.1
      let a := r.1.2
      -- extend short runs
      let (hi, a, d) :=
        if hi - lo < minRun then
          let hi' := if lo + minRun ≤ n then lo + minRun else n
          if useBlocks then
            if h3 : hi'.toNat < 2 ^ 62 ∧ hi'.toNat ≤ a.size ∧ hi'.toNat ≤ d.size ∧ a.size < 2 ^ 64 ∧ d.size < 2 ^ 64
                ∧ minRun.toNat < 2 ^ 61 ∧ lo.toNat ≤ hi'.toNat ∧ hi'.toNat - lo.toNat ≤ minRun.toNat then
              let r := blockPasses 1 minRun lo hi' a d h3.1 h3.2.1 h3.2.2.1 h3.2.2.2.1 h3.2.2.2.2.1 (by decide) h3.2.2.2.2.2.1
                h3.2.2.2.2.2.2.1 h3.2.2.2.2.2.2.2
              (hi', r.1.1, r.1.2)
            else (hi, a, d)
          else if h3 : a.size < 2 ^ 64 ∧ hi'.toNat ≤ a.size ∧ lo.toNat ≤ hi.toNat then
            (hi', (insertionSortRange lo hi' hi a h3.1 h3.2.1 h3.2.2).1, d)
          else (hi, a, d)
        else (hi, a, d)
      if h5 : a.size < 2 ^ 64 ∧ n.toNat ≤ a.size ∧ lo < hi then
        have : lo.toNat < hi.toNat := h5.2.2
        collectRunsB useBlocks minRun n hi a d runs h5.1 h5.2.1
      else (runs.push n, a, d)
    else (runs.push n, a, d)
  else (runs.push n, a, d)
termination_by n.toNat - lo.toNat
decreasing_by u64

/-- Count natural runs (ascending or strictly descending) without writing; read-only scan. -/
def countRuns (n lo : UInt64) (a : @& UInt64Array) (acc limit : UInt64)
    (hsz : a.size < 2 ^ 64) (hn : n.toNat ≤ a.size) : UInt64 :=
  if h : lo < n ∧ acc ≤ limit then
    have h1 : lo.toNat < n.toNat := h.1
    if h4 : lo + 1 < n then
      have : lo.toNat + 1 < n.toNat := by have := UInt64.lt_iff_toNat_lt.mp h4; u64
      have e2 : (lo + 2).toNat = lo.toNat + 2 := by u64
      -- a `match` (not a `let`) so that the bound stays visible to the termination proof
      let ⟨hi, hhi⟩ : { hi : UInt64 // lo.toNat < hi.toNat } :=
        if a.get (lo + 1) < a.get lo then
          ⟨(descEnd n (lo + 2) a hsz hn (by omega)).1, by have := (descEnd n (lo + 2) a hsz hn (by omega)).2; omega⟩
        else ⟨(ascEnd n (lo + 2) a hsz hn (by omega)).1, by have := (ascEnd n (lo + 2) a hsz hn (by omega)).2; omega⟩
      countRuns n hi a (acc + 1) limit hsz hn
    else acc + 1
  else acc
termination_by n.toNat - lo.toNat
decreasing_by u64

def collectRuns (minRun n lo : UInt64) (a : UInt64Array) (runs : Array UInt64)
    (hsz : a.size < 2 ^ 64) (hn : n.toNat ≤ a.size) : Array UInt64 × UInt64Array :=
  let (r, a, _) := collectRunsB false minRun n lo a (zeros 0) runs hsz hn
  (r, a)

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
        if hh : dst.size < 2 ^ 64 ∧ hi.toNat ≤ src.size ∧ hi.toNat ≤ dst.size ∧ lo.toNat ≤ mid.toNat ∧ mid.toNat ≤ hi.toNat then
          (mergeKernelS lo mid hi src dst hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2).1
        else dst
      mergeLevel runs (i + 2) src dst (out.push lo)
    else
      -- odd run left over: copy
      (out.push lo |>.push mid, src, copyRange lo mid src dst)
  else (out, src, dst)
termination_by runs.size - i

def mergeAll (runs : Array UInt64) (src dst : UInt64Array) : UInt64Array :=
  if runs.size ≤ 2 then src
  else
    let (runs', src, dst) := mergeLevel runs 0 src dst (Array.mkEmpty (runs.size / 2 + 2))
    -- ensure the sentinel `n` is at the end
    let runs' := if runs'.size > 0 && runs'[runs'.size - 1]! == runs[runs.size - 1]! then runs' else runs'.push runs[runs.size - 1]!
    -- the level halves the number of runs; the check makes termination structural
    if h : runs'.size < runs.size then mergeAll runs' dst src else src
termination_by runs.size
decreasing_by all_goals first | exact h | (simp_wf; simpa using h)

def sortNatural (minRun : UInt64) (xs : UInt64Array) : UInt64Array :=
  let n := xs.size.toUInt64
  if h : xs.size < 2 ^ 62 then
    have hn : n.toNat ≤ xs.size := by simp [n]; omega
    let (runs, a) := collectRuns minRun n 0 xs (Array.mkEmpty 1024) (by omega) hn
    mergeAll runs a (zeros xs.size)
  else xs

/-- Natural runs, short runs extended to `minRun` with the verified cache-blocked sort. -/
def sortNaturalB (minRun : UInt64) (xs : UInt64Array) : UInt64Array :=
  let n := xs.size.toUInt64
  if h : xs.size < 2 ^ 62 then
    have hn : n.toNat ≤ xs.size := by simp [n]; omega
    let (runs, a, d) := collectRunsB true minRun n 0 xs (zeros xs.size) (Array.mkEmpty 1024) (by omega) hn
    mergeAll runs a d
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

/-- Cross-check `sortNatural` / `sortHybrid` against the reference on many sizes, seeds and shapes. -/
def verifyAll : IO Unit := do
  let sizes : List Nat := [0, 1, 2, 3, 4, 5, 7, 8, 15, 16, 17, 31, 32, 33, 63, 64, 65, 100, 127, 128, 129, 255, 256,
    257, 500, 1000, 1023, 1024, 1025, 4095, 4096, 4097, 10000, 16383, 16384, 16385, 100000, 200000]
  let shapes := ["random", "runs8", "swaps1", "sawtooth", "reversed"]
  let mut bad := 0
  let mut count := 0
  for n in sizes do
    for seed in [1, 2, 3] do
      for shape in shapes do
        let xs := shapeOf shape n (gen n seed.toUInt64)
        let ref := xs.qsort (· < ·)
        let us := UInt64Array.ofArray xs
        for minRun in [1, 2, 32] do
          count := count + 2
          if (NR.sortNatural minRun us).toArray != ref then
            bad := bad + 1; IO.println s!"MISMATCH sortNatural minRun={minRun} n={n} seed={seed} shape={shape}"
          if (NR.sortHybrid minRun us).toArray != ref then
            bad := bad + 1; IO.println s!"MISMATCH sortHybrid minRun={minRun} n={n} seed={seed} shape={shape}"
        count := count + 1
        if (NR.sortNaturalB 256 us).toArray != ref then
          bad := bad + 1; IO.println s!"MISMATCH sortNaturalB n={n} seed={seed} shape={shape}"
  IO.println s!"naturalruns verify: {count} sorts over {sizes.length} sizes x 3 seeds x {shapes.length} shapes; mismatches: {bad}"

def main (args : List String) : IO Unit := do
  if args.contains "verify" then verifyAll; return
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
      for minRun in [256, 1024, 4096] do
        let t0 ← IO.monoNanosNow
        let r ← IO.lazyPure (fun _ => NR.sortNaturalB minRun us)
        let t1 ← IO.monoNanosNow
        IO.println s!"  natural runs, blockPasses to {minRun}: {(t1 - t0).toFloat / 1000000.0} ms [{if r.toArray == ref then "exact match" else "WRONG"}]"
      let t0 ← IO.monoNanosNow
      let k ← IO.lazyPure (fun _ => NR.countRuns us.size.toUInt64 0 us 0 (us.size.toUInt64 / 32) (by omega) (by simp; omega))
      let t1 ← IO.monoNanosNow
      IO.println s!"  countRuns: {k} runs in {(t1 - t0).toFloat / 1000000.0} ms"
