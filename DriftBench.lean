import Drift
import MergeSort.Blocked
import MergeSort.DriftSort
open MergeSort

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
  else if shape == "sorted" then xs0.qsort (· < ·)
  else if shape == "dups" then xs0.map (· % 16)
  else if shape == "dups1000" then xs0.map (· % 1000)
  else xs0

def shapes : List String := ["random", "runs8", "swaps1", "sawtooth", "reversed", "sorted", "dups", "dups1000"]

/-- the bounds-safe sort as a plain function (the dependent `if` inside the loop body times out the elaborator) -/
def safeSort (xs : Array UInt64) : Array UInt64 :=
  let u := UInt64Array.ofArray xs
  if h : u.size < 2 ^ 62 then (DriftSort.sort u h).toArray else #[]

def verifyAll : IO Unit := do
  let sizes : List Nat := (List.range 80) ++ [100, 127, 128, 129, 255, 256, 257, 500, 1000, 1023, 1024, 1025, 4095, 4096, 4097, 5000,
    10000, 16383, 16384, 16385, 65536, 100000, 200000]
  let mut bad := 0
  let mut count := 0
  for n in sizes do
    for seed in [1, 2, 3] do
      for shape in shapes do
        let xs := shapeOf shape n (gen n seed.toUInt64)
        let ref := xs.qsort (· < ·)
        count := count + 1
        let r := (Drift.sort (UInt64Array.ofArray xs)).toArray
        if r != ref then
          bad := bad + 1
          if bad ≤ 10 then IO.println s!"MISMATCH n={n} seed={seed} shape={shape}"
        count := count + 1
        if safeSort xs != ref then
          bad := bad + 1
          if bad ≤ 10 then IO.println s!"MISMATCH (bounds-safe) n={n} seed={seed} shape={shape}"
  IO.println s!"driftsort port verify: {count} sorts over {sizes.length} sizes x 3 seeds x {shapes.length} shapes; mismatches: {bad}"

def timeMs (f : Unit → UInt64Array × UInt64Array) : IO (Float × UInt64Array × UInt64Array) := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  return ((t1 - t0).toFloat / 1000000.0, r)

/-- phases on 1M random, each run twice on the same (uniquely owned) buffers; the second run is warm. -/
def phases (n : Nat) : IO Unit := do
  let xs := gen n 42
  let nn := n.toUInt64
  IO.println s!"phases on n = {n} random (cold / warm, same buffers threaded through):"
  let src := UInt64Array.ofArray xs
  let twice (label : String) (f : UInt64Array → UInt64Array → UInt64Array × UInt64Array) : IO Unit := do
    let v0 ← IO.lazyPure (fun _ => UInt64Array.ofArray xs)
    let s0 ← IO.lazyPure (fun _ => UInt64Array.zeros n)
    let (t1, (v, s)) ← timeMs (fun _ => f v0 s0)
    -- warm run: same (already touched) buffers, random data copied back in
    let v := Drift.copyRange src v 0 0 nn
    let (t2, _) ← timeMs (fun _ => f v s)
    IO.println s!"  {label}: {t1} / {t2} ms"
  twice "one stable partition (scan + copy back)" (fun v s => let (_, v, s) := Drift.stablePartition v s 0 nn (nn / 2) false false; (v, s))
  twice "partition scan only                    " (fun v s => let (s, _) := Drift.partitionScan v s 0 nn (nn / 2) (Drift.get! v (nn/2)) false false; (v, s))
  let rec parts (lo : UInt64) (v s : UInt64Array) (fuel : Nat) : UInt64Array × UInt64Array :=
    match fuel with
    | 0 => (v, s)
    | f + 1 => if lo + 32768 ≤ nn then
        let (_, v, s) := Drift.stablePartition v s lo (lo + 32768) (lo + 16384) false false
        parts (lo + 32768) v s f
      else (v, s)
  twice "partition of 32K-element ranges (cache) " (fun v s => parts 0 v s (n / 32768 + 1))
  let rec parts2 (lo : UInt64) (v s : UInt64Array) (fuel : Nat) : UInt64Array × UInt64Array :=
    match fuel with
    | 0 => (v, s)
    | f + 1 => if lo + 2048 ≤ nn then
        let (_, v, s) := Drift.stablePartition v s lo (lo + 2048) (lo + 1024) false false
        parts2 (lo + 2048) v s f
      else (v, s)
  twice "partition of 2K-element ranges (L1)     " (fun v s => parts2 0 v s (n / 2048 + 1))
  let rec scans (step : UInt64) (f : UInt64Array → UInt64Array → UInt64 → UInt64 → UInt64Array) (lo : UInt64) (v s : UInt64Array)
      (fuel : Nat) : UInt64Array × UInt64Array :=
    match fuel with
    | 0 => (v, s)
    | k + 1 => if lo + step ≤ nn then scans step f (lo + step) v (f v s lo (lo + step)) k else (v, s)
  let labScan (v s : UInt64Array) (lo hi : UInt64) : UInt64Array := (Drift.ppScanLt v s lo hi (Drift.get! v ((lo + hi) / 2)) lo 0 hi).1
  let safeScan (v s : UInt64Array) (lo hi : UInt64) : UInt64Array :=
    if h : hi.toNat ≤ v.size ∧ hi.toNat ≤ s.size ∧ s.size < 2 ^ 64 ∧ lo.toNat ≤ hi.toNat ∧ ((lo + hi) / 2).toNat < v.size then
      (DriftSort.stablePartition (DriftSort.ltPivot (v.get ((lo + hi) / 2) h.2.2.2.2)) v s lo hi h.1 h.2.1 h.2.2.1 h.2.2.2.1).1.buf
    else s
  let labScan4 (v s : UInt64Array) (lo hi : UInt64) : UInt64Array := (Drift.ppScanLt4 v s lo hi (Drift.get! v ((lo + hi) / 2)) lo 0 hi).1
  let labScanR (v s : UInt64Array) (lo hi : UInt64) : UInt64Array := (Drift.partitionScan v s lo hi ((lo + hi) / 2) (Drift.get! v ((lo + hi) / 2)) false false).1
  twice "lab scan 4-way, whole array            " (fun v s => (v, labScan4 v s 0 nn))
  twice "lab scan 4-way, 32K ranges (cache)     " (fun v s => scans 32768 labScan4 0 v s (n / 32768 + 1))
  twice "lab scan 4-way 0-based, 32K ranges     " (fun v s => scans 32768 labScanR 0 v s (n / 32768 + 1))
  twice "lab scan, 32K ranges (cache)           " (fun v s => scans 32768 labScan 0 v s (n / 32768 + 1))
  twice "SAFE scan, 32K ranges (cache)           " (fun v s => scans 32768 safeScan 0 v s (n / 32768 + 1))
  twice "lab scan, 2K ranges (L1)               " (fun v s => scans 2048 labScan 0 v s (n / 2048 + 1))
  twice "SAFE scan, 2K ranges (L1)               " (fun v s => scans 2048 safeScan 0 v s (n / 2048 + 1))
  twice "copyRange (memcpy) v -> s              " (fun v s => (v, Drift.copyRange v s 0 0 nn))
  twice "copyRangeRev s -> v                    " (fun v s => (Drift.copyRangeRev s v (nn - 1) 0 nn, s))
  let rec blocks (lo : UInt64) (v s : UInt64Array) (fuel : Nat) : UInt64Array × UInt64Array :=
    match fuel with
    | 0 => (v, s)
    | f + 1 => if lo + 32 ≤ nn then let (v, s) := Drift.smallSort v s lo (lo + 32); blocks (lo + 32) v s f else (v, s)
  twice "smallSort on every block of 32         " (fun v s => blocks 0 v s (n / 32 + 1))
  let rec stage1 (lo : UInt64) (v s : UInt64Array) (fuel : Nat) : UInt64Array × UInt64Array :=
    match fuel with
    | 0 => (v, s)
    | f + 1 => if lo + 32 ≤ nn then
        let s := Drift.sort8Stable v lo s 0 32
        let s := Drift.sort8Stable v (lo + 16) s 16 40
        stage1 (lo + 32) v s f
      else (v, s)
  twice "  stage 1: two sort8 per block           " (fun v s => stage1 0 v s (n / 32 + 1))
  let rec stage12 (lo : UInt64) (v s : UInt64Array) (fuel : Nat) : UInt64Array × UInt64Array :=
    match fuel with
    | 0 => (v, s)
    | f + 1 => if lo + 32 ≤ nn then
        let s := Drift.sort8Stable v lo s 0 32
        let s := Drift.sort8Stable v (lo + 16) s 16 40
        let s := Drift.smallInsertLoop v s lo 0 8 16
        let s := Drift.smallInsertLoop v s (lo + 16) 16 8 16
        stage12 (lo + 32) v s f
      else (v, s)
  twice "  stage 1+2: + insertion of 8+8          " (fun v s => stage12 0 v s (n / 32 + 1))
  let rec stage123 (lo : UInt64) (v s : UInt64Array) (fuel : Nat) : UInt64Array × UInt64Array :=
    match fuel with
    | 0 => (v, s)
    | f + 1 => if lo + 32 ≤ nn then
        let s := Drift.sort8Stable v lo s 0 32
        let s := Drift.sort8Stable v (lo + 16) s 16 40
        let s := Drift.smallInsertLoop v s lo 0 8 16
        let s := Drift.smallInsertLoop v s (lo + 16) 16 8 16
        let v := Drift.bidirectionalMerge s 0 32 v lo
        stage123 (lo + 32) v s f
      else (v, s)
  twice "  stage 1+2+3: + bidirectional merge     " (fun v s => stage123 0 v s (n / 32 + 1))
  twice "stableQuicksort on the whole array     " (fun v s => Drift.stableQuicksort v s 0 nn nn)
  twice "copy-back quicksort, insertion leaves  " (fun v s => Drift.stableQuicksortIns v s 0 nn nn)
  twice "ping-pong quicksort, insertion leaves  " (fun v s => Drift.stableQuicksortPP v s 0 nn nn)
  twice "ping-pong, insertion leaves, 4-way scan" (fun v s => Drift.stableQuicksortPP4 v s 0 nn nn)
  twice "lab scan into s[lo,hi) (1 elem/check)  " (fun v s => let (s, _) := Drift.ppScanLt v s 0 nn (nn / 2) 0 0 nn; (v, s))
  -- the bounds-safe kernels
  let safeBlocks (v s : UInt64Array) : UInt64Array × UInt64Array :=
    if h : v.size = n ∧ s.size = n ∧ n < 2 ^ 62 then
      let rec go (lo : UInt64) (v s : UInt64Array) (hv : v.size = n) (hs : s.size = n) (hn : n < 2 ^ 62) (fuel : Nat) : UInt64Array × UInt64Array :=
        match fuel with
        | 0 => (v, s)
        | f + 1 =>
          if hlo : lo.toNat + 32 ≤ n ∧ (lo + 32).toNat = lo.toNat + 32 then
            let r := DriftSort.smallSort v s lo (lo + 32) (by omega) (by omega) (by omega) (by omega) (by omega)
            go (lo + 32) r.1.1 r.1.2 (r.2.1.trans hv) (r.2.2.trans hs) hn f
          else (v, s)
      go 0 v s h.1 h.2.1 h.2.2 (n / 32 + 1)
    else (v, s)
  twice "SAFE smallSort on every block of 32     " safeBlocks
  let safePart (v s : UInt64Array) : UInt64Array × UInt64Array :=
    if h : v.size = n ∧ s.size = n ∧ nn.toNat = n ∧ 0 < n ∧ n < 2 ^ 62 then
      let r := DriftSort.stablePartition (DriftSort.ltPivot (v.get (nn / 2) (by simp; omega))) v s 0 nn (by omega) (by omega) (by omega) (by simp)
      (v, r.1.buf)
    else (v, s)
  twice "SAFE one stable partition (scan only)   " safePart
  let safeMerge (v s : UInt64Array) : UInt64Array × UInt64Array :=
    if h : v.size = n ∧ s.size = n ∧ nn.toNat = n ∧ n < 2 ^ 62 then
      let r := DriftSort.mergeRuns v s 0 (nn / 2) nn (by omega) (by omega) (by omega) (by omega) (by simp) (by simp; omega)
      (r.1.1, r.1.2)
    else (v, s)
  twice "SAFE mergeRuns of two halves            " safeMerge
  let safeQuick (v s : UInt64Array) : UInt64Array × UInt64Array :=
    if h : v.size = n ∧ s.size = n ∧ nn.toNat = n ∧ n < 2 ^ 62 then
      let r := DriftSort.stableQuicksort v s 0 nn nn (by omega) (by omega) (by omega) (by omega) (by simp)
      (r.1.1, r.1.2)
    else (v, s)
  twice "SAFE stableQuicksort on the whole array " safeQuick
  let safeFull (v s : UInt64Array) : UInt64Array × UInt64Array :=
    if h : v.size = n ∧ s.size = n ∧ nn.toNat = n ∧ n < 2 ^ 62 then
      let r := DriftSort.driftSortFull v s 0 nn nn (by omega) (by omega) (by omega) (by omega) (by simp)
      (r.1.1, r.1.2)
    else (v, s)
  twice "SAFE driftSortFull (scratch given)      " safeFull
  let safeEntry (v _s : UInt64Array) : UInt64Array × UInt64Array :=
    if h : v.size < 2 ^ 62 then (DriftSort.sort v h, UInt64Array.zeros 1) else (v, UInt64Array.zeros 1)
  twice "SAFE sort entry (allocates scratch)     " safeEntry
  twice "zeros n (8 MB memset)                   " (fun v _ => (v, UInt64Array.zeros n))
  twice "uninit n (lab)                          " (fun v _ => (v, Drift.uninit n))
  twice "zeros n (memset), then touch all       " (fun v _ => (v, Drift.copyRange v (UInt64Array.zeros n) 0 0 nn))
  twice "uninit n, then touch all               " (fun v _ => (v, Drift.copyRange v (Drift.uninit n) 0 0 nn))
  twice "Drift.sort entry (whole sort)          " (fun v _ => (Drift.sort v, UInt64Array.zeros 1))

@[noinline] def pairId (v s : UInt64Array) : UInt64Array × UInt64Array := (v, s)
def pairLoop (v s : UInt64Array) (fuel : Nat) : UInt64Array × UInt64Array :=
  match fuel with
  | 0 => (v, s)
  | f + 1 => let (v, s) := pairId v s; pairLoop v s f

def sortedPhases (n : Nat) : IO Unit := do
  let xs := (gen n 42).qsort (· < ·)
  let nn := n.toUInt64
  IO.println s!"sorted-input phases on n = {n}:"
  let (t, _) ← timeMs (fun _ => (UInt64Array.zeros n, UInt64Array.zeros 1))
  IO.println s!"  zeros n:                        {t} ms"
  let v ← IO.lazyPure (fun _ => UInt64Array.ofArray xs)
  let (t, r) ← timeMs (fun _ => let (rl, _) := Drift.findExistingRun v 0 nn; (UInt64Array.zeros rl.toNat, v))
  IO.println s!"  findExistingRun (sorted):       {t} ms (run length {r.1.size})"
  let v ← IO.lazyPure (fun _ => UInt64Array.ofArray xs)
  let (t, _) ← timeMs (fun _ => (Drift.reverseRange v 0 nn, UInt64Array.zeros 1))
  IO.println s!"  reverseRange whole array:       {t} ms"
  let v ← IO.lazyPure (fun _ => UInt64Array.ofArray xs)
  let (t, _) ← timeMs (fun _ => let (r, v, s) := Drift.createRun v (UInt64Array.zeros n) 0 nn 1000 false; (UInt64Array.zeros (Drift.runLen r).toNat, v))
  IO.println s!"  createRun (sorted, + zeros n):  {t} ms"
  let v ← IO.lazyPure (fun _ => UInt64Array.ofArray xs)
  let (t, _) ← timeMs (fun _ => Drift.driftSortFull v (UInt64Array.zeros n) 0 nn nn)
  IO.println s!"  driftSortFull (+ zeros n):      {t} ms"
  let v ← IO.lazyPure (fun _ => UInt64Array.ofArray xs)
  let (t, _) ← timeMs (fun _ => (Drift.sort v, UInt64Array.zeros 1))
  IO.println s!"  Drift.sort:                     {t} ms"

def main (args : List String) : IO Unit := do
  if args.contains "sortedphases" then sortedPhases ((args.head? >>= String.toNat?).getD 1000000); return
  if args.contains "pairs" then
    let n := 31250
    let (t, _) ← timeMs (fun _ => pairLoop (UInt64Array.zeros 8) (UInt64Array.zeros 8) n)
    IO.println s!"{n} non-inlined calls returning a pair of arrays: {t} ms"
    return
  if args.contains "verify" then verifyAll; return
  if args.contains "ppcheck" then
    let mut bad := 0
    let mut count := 0
    for n in [33, 64, 100, 1000, 4096, 65536, 1000000] do
      for seed in [1, 2, 3] do
        for shape in shapes do
          let xs := shapeOf shape n (gen n seed.toUInt64)
          let ref := xs.qsort (· < ·)
          let us ← IO.lazyPure (fun _ => UInt64Array.ofArray xs)
          let (r, _) ← IO.lazyPure (fun _ => Drift.stableQuicksortPP us (UInt64Array.zeros n) 0 n.toUInt64 n.toUInt64)
          count := count + 1
          if r.toArray != ref then
            bad := bad + 1
            IO.println s!"  MISMATCH n={n} seed={seed} shape={shape}"
    IO.println s!"ping-pong check: {count} sorts, mismatches: {bad}"
    return
  if args.contains "phases" then phases ((args.head? >>= String.toNat?).getD 1000000); return
  if args.contains "duel2" then
    -- interleaved rounds of the two driftsorts with a pre-touched scratch (no allocation inside the clock)
    let n := (args.head? >>= String.toNat?).getD 1000000
    let rounds := ((args.drop 2).head? >>= String.toNat?).getD 10
    let xs := gen n 42
    let ref := xs.qsort (· < ·)
    let nn := n.toUInt64
    let mut sp ← IO.lazyPure (fun _ => Drift.copyRange (UInt64Array.ofArray xs) (UInt64Array.zeros n) 0 0 nn)
    let mut sv ← IO.lazyPure (fun _ => Drift.copyRange (UInt64Array.ofArray xs) (UInt64Array.zeros n) 0 0 nn)
    let mut tp : Array Float := #[]
    let mut tv : Array Float := #[]
    let mut ok := true
    for _ in [0:rounds] do
      let us ← IO.lazyPure (fun _ => UInt64Array.ofArray xs)
      let s := sp
      let t0 ← IO.monoNanosNow
      let (r, s') ← IO.lazyPure (fun _ => Drift.driftSortFull us s 0 nn nn)
      let t1 ← IO.monoNanosNow
      sp := s'
      tp := tp.push ((t1 - t0).toFloat / 1000000.0)
      ok := ok && r.toArray == ref
      let us ← IO.lazyPure (fun _ => UInt64Array.ofArray xs)
      let s := sv
      if h : us.size = n ∧ s.size = n ∧ nn.toNat = n ∧ n < 2 ^ 62 then
        let t0 ← IO.monoNanosNow
        let r ← IO.lazyPure (fun _ => (DriftSort.driftSortFull us s 0 nn nn (by omega) (by omega) (by omega) (by omega) (by simp)).1)
        let t1 ← IO.monoNanosNow
        sv := r.2
        tv := tv.push ((t1 - t0).toFloat / 1000000.0)
        ok := ok && r.1.toArray == ref
    let stats (ts : Array Float) : String :=
      let s := ts.qsort (· < ·)
      s!"min {s[0]!} ms  median {s[s.size / 2]!} ms  max {s[s.size - 1]!} ms"
    IO.println s!"duel2 (scratch given) on n = {n}, {rounds} interleaved rounds [{if ok then "all exact matches" else "WRONG"}]"
    IO.println s!"  Drift.driftSortFull (unverified):   {stats tp}"
    IO.println s!"  DriftSort.driftSortFull (verified): {stats tv}"
    return
  if args.contains "duel" then
    -- interleaved rounds of the three whole sorts; min and median of each
    let n := (args.head? >>= String.toNat?).getD 1000000
    let rounds := ((args.drop 2).head? >>= String.toNat?).getD 10
    let shape := (args.drop 3).headD "random"
    let xs := shapeOf shape n (gen n 42)
    let ref := xs.qsort (· < ·)
    let mut tp : Array Float := #[]
    let mut tv : Array Float := #[]
    let mut tb : Array Float := #[]
    let mut ok := true
    for _ in [0:rounds] do
      let us ← IO.lazyPure (fun _ => UInt64Array.ofArray xs)
      let t0 ← IO.monoNanosNow
      let r ← IO.lazyPure (fun _ => Drift.sort us)
      let t1 ← IO.monoNanosNow
      tp := tp.push ((t1 - t0).toFloat / 1000000.0)
      ok := ok && r.toArray == ref
      let us ← IO.lazyPure (fun _ => UInt64Array.ofArray xs)
      if h : us.size < 2 ^ 62 then
        let t0 ← IO.monoNanosNow
        let r ← IO.lazyPure (fun _ => DriftSort.sort us h)
        let t1 ← IO.monoNanosNow
        tv := tv.push ((t1 - t0).toFloat / 1000000.0)
        ok := ok && r.toArray == ref
      let us ← IO.lazyPure (fun _ => UInt64Array.ofArray xs)
      if h : us.size < 2 ^ 62 then
        let t0 ← IO.monoNanosNow
        let r ← IO.lazyPure (fun _ => BottomUp.sortBlocked us h)
        let t1 ← IO.monoNanosNow
        tb := tb.push ((t1 - t0).toFloat / 1000000.0)
        ok := ok && r.toArray == ref
    let stats (ts : Array Float) : String :=
      let s := ts.qsort (· < ·)
      s!"min {s[0]!} ms  median {s[s.size / 2]!} ms  max {s[s.size - 1]!} ms"
    IO.println s!"duel on n = {n} shape = {shape}, {rounds} interleaved rounds [{if ok then "all exact matches" else "WRONG"}]"
    IO.println s!"  driftsort port (Lean, unverified): {stats tp}"
    IO.println s!"  driftsort, bounds-safe (verified): {stats tv}"
    IO.println s!"  sortBlocked (verified, Part 2):    {stats tb}"
    return
  let n := (args.head? >>= String.toNat?).getD 1000000
  let only := (args.drop 1).headD ""
  for shape in shapes do
    if only != "" && only != shape then continue
    let xs := shapeOf shape n (gen n 42)
    let ref := xs.qsort (· < ·)
    IO.println s!"n = {n} shape = {shape}  (input produced by an IO action before the clock, handed over uniquely)"
    for _ in [0:3] do
      let us ← IO.lazyPure (fun _ => UInt64Array.ofArray xs)
      let t0 ← IO.monoNanosNow
      let r ← IO.lazyPure (fun _ => Drift.sort us)
      let t1 ← IO.monoNanosNow
      IO.println s!"  driftsort port (Lean):  {(t1 - t0).toFloat / 1000000.0} ms [{if r.toArray == ref then "exact match" else "WRONG"}]"
    for _ in [0:3] do
      let us ← IO.lazyPure (fun _ => UInt64Array.ofArray xs)
      if h : us.size < 2 ^ 62 then
        let t0 ← IO.monoNanosNow
        let r ← IO.lazyPure (fun _ => DriftSort.sort us h)
        let t1 ← IO.monoNanosNow
        IO.println s!"  driftsort, bounds-safe: {(t1 - t0).toFloat / 1000000.0} ms [{if r.toArray == ref then "exact match" else "WRONG"}]"
    for _ in [0:2] do
      let us ← IO.lazyPure (fun _ => UInt64Array.ofArray xs)
      if h : us.size < 2 ^ 62 then
        let t0 ← IO.monoNanosNow
        let r ← IO.lazyPure (fun _ => BottomUp.sortBlocked us h)
        let t1 ← IO.monoNanosNow
        IO.println s!"  sortBlocked (verified): {(t1 - t0).toFloat / 1000000.0} ms [{if r.toArray == ref then "exact match" else "WRONG"}]"
    -- the old protocol for comparison: input shared with the harness => copied inside the timing
    let us := UInt64Array.ofArray xs
    let t0 ← IO.monoNanosNow
    let r ← IO.lazyPure (fun _ => Drift.sort us)
    let t1 ← IO.monoNanosNow
    IO.println s!"  driftsort port, input shared (old protocol): {(t1 - t0).toFloat / 1000000.0} ms [{if r.toArray == ref && us.size == n then "exact match" else "WRONG"}]"
