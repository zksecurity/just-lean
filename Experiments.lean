import MergeSort.BottomUp
/-! Unverified experiments on top of the verified bottom-up sort (partial defs, no proofs). -/
open UInt64Array
namespace Exp
@[extern c inline "({ ((uint64_t*)lean_sarray_cptr(#1))[#2] = #3; #1; })"]
def setUnchecked (a : UInt64Array) (i : UInt64) (v : UInt64) (h : i.toNat < a.size) : UInt64Array :=
  ⟨a.data.set i.toNat v h⟩

/-- Branchless merge with UNCHECKED writes (unsafe floor experiment). -/
partial def mergeLoopBLU (mid hi i j k : UInt64) (src dst : UInt64Array) : UInt64Array :=
  if k < hi then
    if i < mid then
      if j < hi then
        let x := src.get i (by sorry)
        let y := src.get j (by sorry)
        let takeLeft : Bool := decide (x ≤ y)
        let v := if takeLeft then x else y
        let di : UInt64 := if takeLeft then 1 else 0
        mergeLoopBLU mid hi (i + di) (j + (1 - di)) (k + 1) src (setUnchecked dst k v (by sorry))
      else mergeLoopBLU mid hi (i + 1) j (k + 1) src (setUnchecked dst k (src.get i (by sorry)) (by sorry))
    else mergeLoopBLU mid hi i (j + 1) (k + 1) src (setUnchecked dst k (src.get j (by sorry)) (by sorry))
  else dst

/-- Branchless merge step: compute both candidates, select. -/
partial def mergeLoopBL (mid hi i j k : UInt64) (src dst : UInt64Array) : UInt64Array :=
  if k < hi then
    if i < mid then
      if j < hi then
        let x := src.get i (by sorry)
        let y := src.get j (by sorry)
        let takeLeft : Bool := decide (x ≤ y)
        let v := if takeLeft then x else y
        let di : UInt64 := if takeLeft then 1 else 0
        mergeLoopBL mid hi (i + di) (j + (1 - di)) (k + 1) src (dst.set k v (by sorry))
      else mergeLoopBL mid hi (i + 1) j (k + 1) src (dst.set k (src.get i (by sorry)) (by sorry))
    else mergeLoopBL mid hi i (j + 1) (k + 1) src (dst.set k (src.get j (by sorry)) (by sorry))
  else dst

/-- Same as the verified merge (branchy), for a same-file baseline. -/
partial def mergeLoopB (mid hi i j k : UInt64) (src dst : UInt64Array) : UInt64Array :=
  if k < hi then
    if i < mid then
      if j < hi then
        if src.get i (by sorry) ≤ src.get j (by sorry) then
          mergeLoopB mid hi (i + 1) j (k + 1) src (dst.set k (src.get i (by sorry)) (by sorry))
        else mergeLoopB mid hi i (j + 1) (k + 1) src (dst.set k (src.get j (by sorry)) (by sorry))
      else mergeLoopB mid hi (i + 1) j (k + 1) src (dst.set k (src.get i (by sorry)) (by sorry))
    else mergeLoopB mid hi i (j + 1) (k + 1) src (dst.set k (src.get j (by sorry)) (by sorry))
  else dst

/-- Bidirectional branchless merge (driftsort style): the front loop produces the `half` smallest
    outputs from the left, the back loop the rest from the right, interleaved for ILP. Requires
    both runs non-empty and `half = (hi - lo) / 2`, `half ≤ len - half`. -/
partial def mergeBidi (mid hi : UInt64) (i j k : UInt64) (i' j' k' : UInt64) (cnt : UInt64)
    (src dst : UInt64Array) : UInt64Array :=
  if cnt > 0 then
    -- front step (stable: take left on ties)
    let x := src.get i (by sorry)
    let y := src.get j (by sorry)
    let takeL : Bool := decide (x ≤ y)
    let dst := dst.set k (if takeL then x else y) (by sorry)
    let di : UInt64 := if takeL then 1 else 0
    -- back step (stable: take right on ties)
    let x' := src.get i' (by sorry)
    let y' := src.get j' (by sorry)
    let takeR : Bool := decide (x' ≤ y')
    let dst := dst.set k' (if takeR then y' else x') (by sorry)
    let dj : UInt64 := if takeR then 1 else 0
    mergeBidi mid hi (i + di) (j + (1 - di)) (k + 1) (i' - (1 - dj)) (j' - dj) (k' - 1) (cnt - 1) src dst
  else dst

/-- Merge with the bidirectional kernel when both runs are long enough, then finish the middle with
    the plain branchless merge. Front consumes `half` elements; back consumes `half`; the remaining
    `len - 2*half` (0 or 1) element is copied. -/
partial def mergeRunBidi (mid hi lo : UInt64) (src dst : UInt64Array) : UInt64Array :=
  let lenL := mid - lo
  let lenR := hi - mid
  -- Bidirectional only for equal-length runs: then neither direction can run past its run
  -- (each direction consumes exactly `lenL` elements), so no guards are needed inside the loop.
  if lenL == lenR && lenL > 0 then
    mergeBidi mid hi lo mid lo (mid - 1) (hi - 1) (hi - 1) lenL src dst
  else
    mergeLoopBL mid hi lo mid lo src dst

partial def passLoop (bl : Bool) (n w lo : UInt64) (src dst : UInt64Array) : UInt64Array :=
  if lo < n then
    let mid := if lo + w ≤ n then lo + w else n
    let hi := if lo + 2 * w ≤ n then lo + 2 * w else n
    let dst := if bl then mergeRunBidi mid hi lo src dst
      else (MergeSort.BottomUp.mergeLoop mid hi lo mid lo src dst (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)
        (by sorry) (by sorry)).1
    passLoop bl n w (lo + 2 * w) src dst
  else dst

partial def widthLoop (bl : Bool) (n w : UInt64) (src dst : UInt64Array) : UInt64Array :=
  if w < n then widthLoop bl n (2 * w) (passLoop bl n w 0 src dst) src else src

/-- insertion sort of a[lo, hi) in place -/
partial def insertLoop (lo k : UInt64) (a : UInt64Array) : UInt64Array :=
  if lo < k then
    let x := a.get k (by sorry)
    let y := a.get (k - 1) (by sorry)
    if x < y then insertLoop lo (k - 1) ((a.set k y (by sorry)).set (k - 1) x (by sorry)) else a
  else a
partial def insertionSortRange (lo hi k : UInt64) (a : UInt64Array) : UInt64Array :=
  if k < hi then insertionSortRange lo hi (k + 1) (insertLoop lo k a) else a
partial def sortBlocks (n w lo : UInt64) (a : UInt64Array) : UInt64Array :=
  if lo < n then
    let hi := if lo + w ≤ n then lo + w else n
    sortBlocks n w (lo + w) (insertionSortRange lo hi (lo + 1) a)
  else a

/-- Branchless compare-swap on two positions (min/max compile to cmov). -/
@[inline] def cswap (a : UInt64Array) (p q : UInt64) : UInt64Array :=
  let x := a.get p (by sorry)
  let y := a.get q (by sorry)
  let lo := if x ≤ y then x else y
  let hi := if x ≤ y then y else x
  (a.set p lo (by sorry)).set q hi (by sorry)

/-- Optimal 8-element sorting network (19 compare-swaps), applied to a[b, b+8). -/
def net8 (b : UInt64) (a : UInt64Array) : UInt64Array :=
  let a := cswap a (b+0) (b+2); let a := cswap a (b+1) (b+3); let a := cswap a (b+4) (b+6); let a := cswap a (b+5) (b+7)
  let a := cswap a (b+0) (b+4); let a := cswap a (b+1) (b+5); let a := cswap a (b+2) (b+6); let a := cswap a (b+3) (b+7)
  let a := cswap a (b+0) (b+1); let a := cswap a (b+2) (b+3); let a := cswap a (b+4) (b+5); let a := cswap a (b+6) (b+7)
  let a := cswap a (b+2) (b+4); let a := cswap a (b+3) (b+5)
  let a := cswap a (b+1) (b+4); let a := cswap a (b+3) (b+6)
  let a := cswap a (b+1) (b+2); let a := cswap a (b+3) (b+4); let a := cswap a (b+5) (b+6)
  a

/-- sort every full 8-block with the network; a short tail block with insertion sort -/
partial def net8Blocks (n lo : UInt64) (a : UInt64Array) : UInt64Array :=
  if lo + 8 ≤ n then net8Blocks n (lo + 8) (net8 lo a)
  else if lo < n then insertionSortRange lo n (lo + 1) a
  else a

def sortNet8 (bl : Bool) (xs : UInt64Array) : UInt64Array :=
  let n := xs.size.toUInt64
  widthLoop bl n 8 (net8Blocks n 0 xs) (zeros xs.size)

/-- passes w = 1, 2, ..., until w ≥ B inside the block [lo, hi) (fixed number of passes = log2 B,
    so every block ends in the same buffer); ping-pong between src and dst. -/
partial def blockPasses (w B lo hi : UInt64) (src dst : UInt64Array) : UInt64Array × UInt64Array :=
  if w < B then
    -- one pass over [lo, hi) with run length w: merge pairs from src into dst
    let dst := passRange w lo hi lo src dst
    blockPasses (2 * w) B lo hi dst src
  else (src, dst)
where
  passRange (w lo hi cur : UInt64) (src dst : UInt64Array) : UInt64Array :=
    if cur < hi then
      let mid := if cur + w ≤ hi then cur + w else hi
      let hi' := if cur + 2 * w ≤ hi then cur + 2 * w else hi
      passRange w lo hi (cur + 2 * w) src (mergeRunBidi mid hi' cur src dst)
    else dst

/-- sort every block of B elements completely (log2 B passes), then merge globally from w = B -/
partial def blockedSort (B : UInt64) (xs : UInt64Array) : UInt64Array :=
  let n := xs.size.toUInt64
  let rec blocks (lo : UInt64) (src dst : UInt64Array) : UInt64Array × UInt64Array :=
    if lo < n then
      let hi := if lo + B ≤ n then lo + B else n
      let (src, dst) := blockPasses 1 B lo hi src dst
      blocks (lo + B) src dst
    else (src, dst)
  let (src, dst) := blocks 0 xs (zeros xs.size)
  widthLoop true n B src dst

/-- network-sorted 8-blocks, then cache-blocked passes from w = 8, then global passes -/
partial def blockedNet8 (B : UInt64) (xs : UInt64Array) : UInt64Array :=
  let n := xs.size.toUInt64
  let xs := net8Blocks n 0 xs
  let rec blocks (lo : UInt64) (src dst : UInt64Array) : UInt64Array × UInt64Array :=
    if lo < n then
      let hi := if lo + B ≤ n then lo + B else n
      let (src, dst) := blockPasses 8 B lo hi src dst
      blocks (lo + B) src dst
    else (src, dst)
  let (src, dst) := blocks 0 xs (zeros xs.size)
  widthLoop true n B src dst

/-- Stable quicksort prototype (driftsort's engine for unsorted runs): branchless partition into a
    scratch buffer (smaller elements from the front, others from the back), copy back (reversing the
    back part to keep stability), recurse; insertion sort for short ranges. -/
partial def partitionLoop (pivot : UInt64) (i hi : UInt64) (l r : UInt64) (src scratch : UInt64Array) : UInt64Array × UInt64 :=
  if i < hi then
    let x := src.get i (by sorry)
    let isL : Bool := decide (x < pivot)
    let pos := if isL then l else r
    let scratch := scratch.set pos x (by sorry)
    let dl : UInt64 := if isL then 1 else 0
    partitionLoop pivot (i + 1) hi (l + dl) (r - (1 - dl)) src scratch
  else (scratch, l)

/-- memcpy-based range copy (unsafe prototype helper): a[dst, dst+len) := scratch[src, src+len) -/
@[extern c inline "({ lean_object* _a = #1; if (__builtin_expect(!lean_is_exclusive(_a), 0)) _a = lean_copy_float_array(_a); __builtin_memcpy((uint64_t*)lean_sarray_cptr(_a) + #2, (uint64_t*)lean_sarray_cptr(#3) + #4, 8 * #5); _a; })"]
def copyRange (a : UInt64Array) (dst : UInt64) (scratch : @& UInt64Array) (src len : UInt64) : UInt64Array := a

/-- copy scratch[lo, m) forward and scratch[m, hi) reversed into a[lo, hi) -/
partial def copyBackFwd (k m : UInt64) (scratch a : UInt64Array) : UInt64Array :=
  if k < m then copyBackFwd (k + 1) m scratch (a.set k (scratch.get k (by sorry)) (by sorry)) else a
partial def copyBackRev (k hi : UInt64) (src' : UInt64) (scratch a : UInt64Array) : UInt64Array :=
  -- a[k] := scratch[src'], src' decreasing
  if k < hi then copyBackRev (k + 1) hi (src' - 1) scratch (a.set k (scratch.get src' (by sorry)) (by sorry)) else a

partial def qsortRange (lo hi : UInt64) (a scratch : UInt64Array) : UInt64Array × UInt64Array :=
  if hi - lo ≤ 32 then (insertionSortRange lo hi (lo + 1) a, scratch)
  else
    -- median of three as pivot
    let x := a.get lo (by sorry); let y := a.get (lo + (hi - lo) / 2) (by sorry); let z := a.get (hi - 1) (by sorry)
    let pivot := if x ≤ y then (if y ≤ z then y else if x ≤ z then z else x) else (if x ≤ z then x else if y ≤ z then z else y)
    let (scratch, m) := partitionLoop pivot lo hi lo (hi - 1) a scratch
    if m == lo then
      -- all ≥ pivot: separate the pivot-equal elements to guarantee progress (simple fallback: move on with insertion)
      (insertionSortRange lo hi (lo + 1) a, scratch)
    else
      let a := copyRange a lo scratch lo (m - lo)
      let a := copyBackRev m hi (hi - 1) scratch a
      let (a, scratch) := qsortRange lo m a scratch
      qsortRange m hi a scratch

def stableQuick (xs : UInt64Array) : UInt64Array :=
  let n := xs.size.toUInt64
  (qsortRange 0 n xs (zeros xs.size)).1

def sortWith (bl : Bool) (w0 : UInt64) (xs : UInt64Array) : UInt64Array :=
  let n := xs.size.toUInt64
  let xs := if w0 > 1 then sortBlocks n w0 0 xs else xs
  widthLoop bl n w0 xs (zeros xs.size)

end Exp

def gen (n : Nat) (seed : UInt64) : Array UInt64 := Id.run do
  let mut s := seed
  let mut out := Array.mkEmpty n
  for _ in [0:n] do
    s := s ^^^ (s >>> 12); s := s ^^^ (s <<< 25); s := s ^^^ (s >>> 27)
    out := out.push (s * 0x2545F4914F6CDD1D)
  return out

def timeIt (label : String) (ref : Array UInt64) (f : Unit → UInt64Array) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  IO.println s!"{label}: {(t1 - t0).toFloat / 1000000.0} ms [{if r.toArray == ref then "ok" else "WRONG"}]"

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
  let shape := (args.drop 1).headD "random"
  let xs := shapeOf shape n (gen n 42)
  let ref := xs.qsort (· < ·)
  IO.println s!"n = {n}"
  timeIt "verified BottomUp.sort            " ref (fun _ => MergeSort.BottomUp.sort (UInt64Array.ofArray xs) (by sorry))
  timeIt "exp: VERIFIED mergeLoop in exp loops" ref (fun _ => Exp.sortWith false 1 (UInt64Array.ofArray xs))
  timeIt "exp: bidirectional branchless merge     " ref (fun _ => Exp.sortWith true 1 (UInt64Array.ofArray xs))
  timeIt "exp: branchy, insertion w0=8      " ref (fun _ => Exp.sortWith false 8 (UInt64Array.ofArray xs))
  timeIt "exp: branchy, insertion w0=16     " ref (fun _ => Exp.sortWith false 16 (UInt64Array.ofArray xs))
  timeIt "exp: branchless, insertion w0=16  " ref (fun _ => Exp.sortWith true 16 (UInt64Array.ofArray xs))
  timeIt "exp: branchless, insertion w0=32  " ref (fun _ => Exp.sortWith true 32 (UInt64Array.ofArray xs))
  timeIt "exp: sort8 network + bidi passes   " ref (fun _ => Exp.sortNet8 true (UInt64Array.ofArray xs))
  timeIt "exp: cache-blocked bidi, B=16384    " ref (fun _ => Exp.blockedSort 16384 (UInt64Array.ofArray xs))
  timeIt "exp: net8 + cache-blocked bidi, B=2^15" ref (fun _ => Exp.blockedNet8 32768 (UInt64Array.ofArray xs))
  timeIt "exp: stable quicksort (branchless partition)" ref (fun _ => Exp.stableQuick (UInt64Array.ofArray xs))
