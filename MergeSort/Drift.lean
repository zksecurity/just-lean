import MergeSort.UInt64Array
/-!
# An unverified, line-by-line port of Rust's driftsort (`core::slice::sort::stable`) to Lean, for `u64`

Sources: `lab/driftsort-src/{drift,merge,quicksort,smallsort,shared_mod,shared_pivot}.rs` (rust-lang/rust
master, Sept 2026). Every function below mirrors one Rust function; names are kept. The comparison is
`is_less a b = a < b`. All accesses are bounds-checked (`get!`/`set!` return 0 / leave the array unchanged
when out of range); everything is total (`termination_by`), nothing is `partial`, no proof is admitted.
Both buffers are threaded through every call as a pair so that writes stay in place.
-/
namespace Drift
open UInt64Array

abbrev A := UInt64Array

/-- UNCHECKED experiment: the C ignores the bounds (the model is the checked version). -/
@[extern c inline "((uint64_t*)lean_sarray_cptr(#1))[#2]"]
def getU (a : @& A) (i : UInt64) : UInt64 := if h : i.toNat < a.size then a.get i h else 0
@[extern c inline "({ lean_object* _a = #1; if (__builtin_expect(!lean_is_exclusive(_a), 0)) _a = lean_copy_float_array(_a); ((uint64_t*)lean_sarray_cptr(_a))[#2] = #3; _a; })"]
def setU (a : A) (i v : UInt64) : A := if h : i.toNat < a.size then a.set i v h else a
@[inline] def get! (a : @& A) (i : UInt64) : UInt64 := getU a i
@[inline] def set! (a : A) (i v : UInt64) : A := setU a i v

/-- two stores, one exclusivity check (model: two `set!`s) -/
@[extern c inline "({ lean_object* _a = #1; if (__builtin_expect(!lean_is_exclusive(_a), 0)) _a = lean_copy_float_array(_a); uint64_t* _p = (uint64_t*)lean_sarray_cptr(_a); _p[#2] = #3; _p[#4] = #5; _a; })"]
def set2 (a : A) (i v j w : UInt64) : A := set! (set! a i v) j w
/-- four consecutive stores, one exclusivity check (model: four `set!`s) -/
@[extern c inline "({ lean_object* _a = #1; if (__builtin_expect(!lean_is_exclusive(_a), 0)) _a = lean_copy_float_array(_a); uint64_t* _p = (uint64_t*)lean_sarray_cptr(_a) + #2; _p[0] = #3; _p[1] = #4; _p[2] = #5; _p[3] = #6; _a; })"]
def set4 (a : A) (d v0 v1 v2 v3 : UInt64) : A := set! (set! (set! (set! a d v0) (d + 1) v1) (d + 2) v2) (d + 3) v3
@[inline] def lt (a b : UInt64) : Bool := decide (a < b)

/-- `SMALL_SORT_GENERAL_THRESHOLD` -/
def smallSortThreshold : UInt64 := 32
/-- `SMALL_SORT_GENERAL_SCRATCH_LEN` -/
def smallSortScratchLen : UInt64 := smallSortThreshold + 16
/-- `MAX_LEN_ALWAYS_INSERTION_SORT` -/
def maxLenAlwaysInsertion : UInt64 := 20
/-- `MIN_SQRT_RUN_LEN` -/
def minSqrtRunLen : UInt64 := 64
/-- `PSEUDO_MEDIAN_REC_THRESHOLD` -/
def pseudoMedianRecThreshold : UInt64 := 64

/-! ## smallsort.rs -/

/-- `sort4_stable`: read `src[b, b+4)`, write the four values sorted to `dst[d, d+4)`. -/
@[inline] def sort4Stable (src : @& A) (b : UInt64) (dst : A) (d : UInt64) : A :=
  let v0 := get! src b
  let v1 := get! src (b + 1)
  let v2 := get! src (b + 2)
  let v3 := get! src (b + 3)
  let c1 := lt v1 v0
  let c2 := lt v3 v2
  let a := if c1 then v1 else v0
  let bb := if c1 then v0 else v1
  let c := if c2 then v3 else v2
  let dd := if c2 then v2 else v3
  let c3 := lt c a
  let c4 := lt dd bb
  let mn := if c3 then c else a
  let mx := if c4 then bb else dd
  let ul := if c3 then a else (if c4 then c else bb)
  let ur := if c4 then dd else (if c3 then bb else c)
  let c5 := lt ur ul
  let lo := if c5 then ur else ul
  let hi := if c5 then ul else ur
  set4 dst d mn lo hi mx

/-- The loop of `bidirectional_merge` (`k` iterations left), reading from `src`, writing to `dst`;
    the odd-length fix-up is done in the base case so that the loop returns only the array
    (returning the six cursors would box five `UInt64`s per call). -/
def bidiLoop (src : @& A) (dst : A) (k left right out leftRev rightRev outRev : UInt64) (odd : Bool) : A :=
  if h : 0 < k then
    have h' : 0 < k.toNat := h
    -- merge_up
    let l := get! src left
    let r := get! src right
    let isL := !(lt r l)
    let right := right + (if isL then 0 else 1)
    let left := left + (if isL then 1 else 0)
    -- merge_down
    let lr := get! src leftRev
    let rr := get! src rightRev
    let isL' := !(lt rr lr)
    let dst := set2 dst out (if isL then l else r) outRev (if isL' then rr else lr)
    let out := out + 1
    let rightRev := rightRev - (if isL' then 1 else 0)
    let leftRev := leftRev - (if isL' then 0 else 1)
    let outRev := outRev - 1
    bidiLoop src dst (k - 1) left right out leftRev rightRev outRev odd
  else if odd then
    let leftEnd := leftRev + 1
    let leftNonempty := lt left leftEnd
    set! dst out (get! src (if leftNonempty then left else right))
  else dst
termination_by k.toNat
decreasing_by u64

/-- `bidirectional_merge`: `src[s, s+len)` holds two sorted halves; write the merge to `dst[d, d+len)`. -/
@[inline] def bidirectionalMerge (src : @& A) (s len : UInt64) (dst : A) (d : UInt64) : A :=
  let half := len / 2
  bidiLoop src dst half s (s + half) d (s + half - 1) (s + len - 1) (d + len - 1) (len % 2 == 1)

/-- `bidirectional_merge` with source and destination in the same array (non-overlapping ranges). -/
def bidiLoopSame (a : A) (k left right out leftRev rightRev outRev : UInt64) (odd : Bool) : A :=
  if h : 0 < k then
    have h' : 0 < k.toNat := h
    let l := get! a left
    let r := get! a right
    let isL := !(lt r l)
    let right := right + (if isL then 0 else 1)
    let left := left + (if isL then 1 else 0)
    let lr := get! a leftRev
    let rr := get! a rightRev
    let isL' := !(lt rr lr)
    let a := set2 a out (if isL then l else r) outRev (if isL' then rr else lr)
    let out := out + 1
    let rightRev := rightRev - (if isL' then 1 else 0)
    let leftRev := leftRev - (if isL' then 0 else 1)
    let outRev := outRev - 1
    bidiLoopSame a (k - 1) left right out leftRev rightRev outRev odd
  else if odd then
    let leftEnd := leftRev + 1
    let leftNonempty := lt left leftEnd
    set! a out (get! a (if leftNonempty then left else right))
  else a
termination_by k.toNat
decreasing_by u64

@[inline] def bidirectionalMergeSame (a : A) (s len d : UInt64) : A :=
  let half := len / 2
  bidiLoopSame a half s (s + half) d (s + half - 1) (s + len - 1) (d + len - 1) (len % 2 == 1)

/-- `sort8_stable`: `src[b, b+8)` → `dst[d, d+8)` using `tmp[t, t+8)` of `dst` as temporary. -/
def sort8Stable (src : @& A) (b : UInt64) (dst : A) (d t : UInt64) : A :=
  let dst := sort4Stable src b dst t
  let dst := sort4Stable src (b + 4) dst (t + 4)
  bidirectionalMergeSame dst t 8 d

/-- The shifting loop of `insert_tail`: `tmp` is the element being inserted, the gap is at `gap`. -/
def insertTailLoop (a : A) (begin sift gap tmp : UInt64) : A :=
  let a := set! a gap (get! a sift)
  if h : begin < sift then
    have h' : begin.toNat < sift.toNat := h
    have hb := UInt64.toNat_lt sift
    let sift' := sift - 1
    if !(lt tmp (get! a sift')) then set! a sift tmp
    else insertTailLoop a begin sift' sift tmp
  else set! a sift tmp
termination_by sift.toNat - begin.toNat
decreasing_by u64

/-- `insert_tail`: `a[begin, tail)` is sorted; insert `a[tail]`. -/
@[inline] def insertTail (a : A) (begin tail : UInt64) : A :=
  let tmp := get! a tail
  if !(lt tmp (get! a (tail - 1))) then a
  else insertTailLoop a begin (tail - 1) tail tmp

/-- `insertion_sort_shift_left`: `a[lo, lo+offset)` is sorted; sort `a[lo, hi)`. -/
def insertionSortShiftLeft (a : A) (lo hi tail : UInt64) : A :=
  if h : tail < hi then
    have h' : tail.toNat < hi.toNat := h
    have hb := UInt64.toNat_lt hi
    insertionSortShiftLeft (insertTail a lo tail) lo hi (tail + 1) else a
termination_by hi.toNat - tail.toNat
decreasing_by u64

/-- copy `v[src+i]` into `s[dst+i]` and insert it, for `i ∈ [i, n)` (the insertion loop of the small sort) -/
def smallInsertLoop (v : @& A) (s : A) (src dst i n : UInt64) : A :=
  if h : i < n then
    have h' : i.toNat < n.toNat := h
    have hb := UInt64.toNat_lt n
    let s := set! s (dst + i) (get! v (src + i))
    let s := insertTail s dst (dst + i)
    smallInsertLoop v s src dst (i + 1) n
  else s
termination_by n.toNat - i.toNat
decreasing_by u64

/-- `small_sort_general_with_scratch`: sort `v[lo, hi)` (`hi - lo ≤ 32`) using `s[0, len+16)`. -/
def smallSort (v s : A) (lo hi : UInt64) : A × A :=
  let len := hi - lo
  if len < 2 then (v, s)
  else
    let half := len / 2
    let presorted : UInt64 := if len ≥ 16 then 8 else if len ≥ 8 then 4 else 1
    let s :=
      if len ≥ 16 then
        let s := sort8Stable v lo s 0 len
        sort8Stable v (lo + half) s half (len + 8)
      else if len ≥ 8 then
        let s := sort4Stable v lo s 0
        sort4Stable v (lo + half) s half
      else
        let s := set! s 0 (get! v lo)
        set! s half (get! v (lo + half))
    let s := smallInsertLoop v s lo 0 presorted half
    let s := smallInsertLoop v s (lo + half) half presorted (len - half)
    let v := bidirectionalMerge s 0 len v lo
    (v, s)

/-! ## merge.rs -/

def copyRangeLoop (src : @& A) (dst : A) (sIdx dIdx n : UInt64) : A :=
  if h : 0 < n then copyRangeLoop src (set! dst dIdx (get! src sIdx)) (sIdx + 1) (dIdx + 1) (n - 1) else dst
termination_by n.toNat
decreasing_by u64

/-- `ptr::copy_nonoverlapping` of `n` elements (UNCHECKED experiment: `memcpy`, distinct arrays). -/
@[extern c inline "({ lean_object* _d = #2; if (__builtin_expect(!lean_is_exclusive(_d), 0)) _d = lean_copy_float_array(_d); __builtin_memcpy((uint64_t*)lean_sarray_cptr(_d) + #4, (uint64_t*)lean_sarray_cptr(#1) + #3, (size_t)(#5) * 8); _d; })"]
def copyRange (src : @& A) (dst : A) (sIdx dIdx n : UInt64) : A := copyRangeLoop src dst sIdx dIdx n

/-- `merge_up`: left run in `s[start, end)`, right run in `v[right, rightEnd)`, output to `v[dst..)`. -/
def mergeUp (v s : A) (start «end» dst right rightEnd : UInt64) : A × UInt64 × UInt64 :=
  if h : start < «end» ∧ right < rightEnd then
    have h1 : start.toNat < «end».toNat := h.1
    have h2 : right.toNat < rightEnd.toNat := h.2
    have hb1 := UInt64.toNat_lt «end»
    have hb2 := UInt64.toNat_lt rightEnd
    let l := get! s start
    let r := get! v right
    let consumeLeft := !(lt r l)
    let di : UInt64 := if consumeLeft then 1 else 0
    let x := if consumeLeft then l else r
    let v := set! v dst x
    mergeUp v s (start + di) «end» (dst + 1) (right + (1 - di)) rightEnd
  else (v, start, dst)
termination_by («end».toNat - start.toNat) + (rightEnd.toNat - right.toNat)
decreasing_by all_goals (split <;> u64)

/-- `merge_down`: left run in `v[leftEnd, dst)` (consumed from the back), right run in `s[0, end)`,
    output to `v[.., out)` from the back. Returns `(v, dst, end)`. -/
def mergeDown (v s : A) (leftEnd dst «end» out : UInt64) : A × UInt64 × UInt64 :=
  if h : leftEnd < dst ∧ 0 < «end» then
    have h1 : leftEnd.toNat < dst.toNat := h.1
    have h2 : 0 < «end».toNat := h.2
    have hb1 := UInt64.toNat_lt dst
    have hb2 := UInt64.toNat_lt «end»
    let left := dst - 1
    let right := «end» - 1
    let out := out - 1
    let lv := get! v left
    let rv := get! s right
    let consumeLeft := lt rv lv
    let di : UInt64 := if consumeLeft then 1 else 0
    let x := if consumeLeft then lv else rv
    let v := set! v out x
    mergeDown v s leftEnd (dst - di) («end» - (1 - di)) out
  else (v, dst, «end»)
termination_by (dst.toNat - leftEnd.toNat) + «end».toNat
decreasing_by all_goals (split <;> u64)

/-- `merge`: `v[lo, mid)` and `v[mid, hi)` are sorted; merge them in place using `s` (≥ the shorter run). -/
def merge (v s : A) (lo mid hi : UInt64) : A × A :=
  if mid ≤ lo || hi ≤ mid then (v, s)
  else
    let leftLen := mid - lo
    let rightLen := hi - mid
    if leftLen ≤ rightLen then
      let s := copyRange v s lo 0 leftLen
      let (v, start, dst) := mergeUp v s 0 leftLen lo mid hi
      -- MergeState::drop: copy what is left of the shorter run into the gap
      (copyRange s v start dst (leftLen - start), s)
    else
      let s := copyRange v s mid 0 rightLen
      let (v, dst, «end») := mergeDown v s lo mid rightLen hi
      (copyRange s v 0 dst «end», s)

/-! ## shared/pivot.rs -/

def median3 (v : @& A) (a b c : UInt64) : UInt64 :=
  let x := lt (get! v a) (get! v b)
  let y := lt (get! v a) (get! v c)
  if x == y then
    let z := lt (get! v b) (get! v c)
    if z != x then c else b
  else a

def median3Rec (v : @& A) (a b c n : UInt64) : UInt64 :=
  if h : n * 8 ≥ pseudoMedianRecThreshold ∧ 8 ≤ n then
    have h2 : 8 ≤ n.toNat := h.2
    have hb := UInt64.toNat_lt n
    let n8 := n / 8
    let a := median3Rec v a (a + n8 * 4) (a + n8 * 7) n8
    let b := median3Rec v b (b + n8 * 4) (b + n8 * 7) n8
    let c := median3Rec v c (c + n8 * 4) (c + n8 * 7) n8
    median3 v a b c
  else median3 v a b c
termination_by n.toNat
decreasing_by all_goals u64

/-- `choose_pivot` on `v[lo, hi)` (`hi - lo ≥ 8`), returns an absolute index. -/
def choosePivot (v : @& A) (lo hi : UInt64) : UInt64 :=
  let len := hi - lo
  let d8 := len / 8
  let a := lo
  let b := lo + d8 * 4
  let c := lo + d8 * 7
  if len < pseudoMedianRecThreshold then median3 v a b c else median3Rec v a b c d8

/-! ## quicksort.rs -/

/-- The scan of `stable_partition` over `v[i, hi)` with `x < pivot` going left (no pivot inside the range). -/
def partitionScanLt (v : @& A) (s : A) (i hi pivot numLeft scratchRev : UInt64) : A × UInt64 :=
  if h : i < hi then
    have h' : i.toNat < hi.toNat := h
    have hb := UInt64.toNat_lt hi
    let x := get! v i
    let towardsLeft := lt x pivot
    let scratchRev := scratchRev - 1
    let dst := (if towardsLeft then 0 else scratchRev) + numLeft
    let s := set! s dst x
    partitionScanLt v s (i + 1) hi pivot (numLeft + (if towardsLeft then 1 else 0)) scratchRev
  else (s, numLeft)
termination_by hi.toNat - i.toNat
decreasing_by u64

/-- Same with `x ≤ pivot` going left (the equal-partition comparator `!is_less(pivot, x)`). -/
def partitionScanLe (v : @& A) (s : A) (i hi pivot numLeft scratchRev : UInt64) : A × UInt64 :=
  if h : i < hi then
    have h' : i.toNat < hi.toNat := h
    have hb := UInt64.toNat_lt hi
    let x := get! v i
    let towardsLeft := !(lt pivot x)
    let scratchRev := scratchRev - 1
    let dst := (if towardsLeft then 0 else scratchRev) + numLeft
    let s := set! s dst x
    partitionScanLe v s (i + 1) hi pivot (numLeft + (if towardsLeft then 1 else 0)) scratchRev
  else (s, numLeft)
termination_by hi.toNat - i.toNat
decreasing_by u64

/-- The whole scan: `[lo, pivotPos)`, the pivot, `(pivotPos, hi)`, like Rust's two `loop_end_pos` rounds.
    `scratchRev` after a scan is arithmetic (one decrement per element), so the scans return one pair. -/
def partitionScan (v : @& A) (s : A) (lo hi pivotPos pivot : UInt64) (pivotGoesLeft eqMode : Bool) : A × UInt64 :=
  let len := hi - lo
  let sr1 := len - (pivotPos - lo)          -- after scanning [lo, pivotPos)
  let (s, nl) := if eqMode then partitionScanLe v s lo pivotPos pivot 0 len else partitionScanLt v s lo pivotPos pivot 0 len
  -- the pivot
  let sr2 := sr1 - 1
  let dst := (if pivotGoesLeft then 0 else sr2) + nl
  let s := set! s dst pivot
  let nl := nl + (if pivotGoesLeft then 1 else 0)
  if eqMode then partitionScanLe v s (pivotPos + 1) hi pivot nl sr2 else partitionScanLt v s (pivotPos + 1) hi pivot nl sr2

def copyRangeRevLoop (src : @& A) (dst : A) (sIdx dIdx n : UInt64) : A :=
  if h : 0 < n then copyRangeRevLoop src (set! dst dIdx (get! src sIdx)) (sIdx - 1) (dIdx + 1) (n - 1) else dst
termination_by n.toNat
decreasing_by u64

/-- reversed copy of `n` elements, `dst[dIdx+i] := src[sIdx-i]` (UNCHECKED experiment: plain C loop, vectorisable). -/
@[extern c inline "({ lean_object* _d = #2; if (__builtin_expect(!lean_is_exclusive(_d), 0)) _d = lean_copy_float_array(_d); uint64_t* _dp = (uint64_t*)lean_sarray_cptr(_d) + #4; const uint64_t* _sp = (const uint64_t*)lean_sarray_cptr(#1) + #3; size_t _n = (size_t)(#5); for (size_t _i = 0; _i < _n; _i++) _dp[_i] = _sp[-(ptrdiff_t)_i]; _d; })"]
def copyRangeRev (src : @& A) (dst : A) (sIdx dIdx n : UInt64) : A := copyRangeRevLoop src dst sIdx dIdx n

/-- `stable_partition` of `v[lo, hi)` around `v[pivotPos]`; returns the number of left elements. -/
@[inline] def stablePartition (v s : A) (lo hi pivotPos : UInt64) (pivotGoesLeft eqMode : Bool) : UInt64 × A × A :=
  let len := hi - lo
  let pivot := get! v pivotPos
  let (s, numLeft) := partitionScan v s lo hi pivotPos pivot pivotGoesLeft eqMode
  let v := copyRange s v 0 lo numLeft
  let v := copyRangeRev s v (len - 1) (lo + numLeft) (len - numLeft)
  (numLeft, v, s)

/-! ## drift.rs -/

@[inline] def mkSorted (len : UInt64) : UInt64 := (len <<< 1) ||| 1
@[inline] def mkUnsorted (len : UInt64) : UInt64 := len <<< 1
@[inline] def runLen (r : UInt64) : UInt64 := r >>> 1
@[inline] def runSorted (r : UInt64) : Bool := r &&& 1 == 1

@[inline] def log2U (x : UInt64) : UInt64 := x.toNat.log2.toUInt64

def clz (x : UInt64) : UInt64 := if x == 0 then 64 else 63 - log2U x

def mergeTreeScaleFactor (n : UInt64) : UInt64 := (((1 : UInt64) <<< 62) + n - 1) / n

def mergeTreeDepth (left mid right scale : UInt64) : UInt64 :=
  clz ((scale * (left + mid)) ^^^ (scale * (mid + right)))

def sqrtApprox (n : UInt64) : UInt64 :=
  let ilog := log2U (n ||| 1)
  let shift := (ilog + 1) / 2
  ((1 <<< shift) + (n >>> shift)) / 2

def findRunLoop (v : @& A) (i hi : UInt64) (desc : Bool) : UInt64 :=
  if h : i < hi then
    have h' : i.toNat < hi.toNat := h
    have hb := UInt64.toNat_lt hi
    let c := lt (get! v i) (get! v (i - 1))
    if c == desc then findRunLoop v (i + 1) hi desc else i
  else i
termination_by hi.toNat - i.toNat
decreasing_by u64

/-- `find_existing_run` on `v[lo, hi)`: (run length, strictly descending?) -/
def findExistingRun (v : @& A) (lo hi : UInt64) : UInt64 × Bool :=
  if hi - lo < 2 then (hi - lo, false)
  else
    let desc := lt (get! v (lo + 1)) (get! v lo)
    (findRunLoop v (lo + 2) hi desc - lo, desc)

def reverseRange (v : A) (lo hi : UInt64) : A :=
  if h : lo < hi ∧ lo + 1 < hi then
    have hb := UInt64.toNat_lt hi
    have h0 : lo.toNat < hi.toNat := h.1
    have h' : lo.toNat + 1 < hi.toNat := by have := UInt64.lt_iff_toNat_lt.mp h.2; u64
    let x := get! v lo
    let y := get! v (hi - 1)
    reverseRange (set! (set! v lo y) (hi - 1) x) (lo + 1) (hi - 1)
  else v
termination_by hi.toNat - lo.toNat
decreasing_by u64

/-- `create_run` on `v[lo, hi)`. -/
def createRun (v s : A) (lo hi minGoodRunLen : UInt64) (eager : Bool) : UInt64 × A × A :=
  let len := hi - lo
  let tryRun : Option (UInt64 × A) :=
    if len ≥ minGoodRunLen then
      let (rl, rev) := findExistingRun v lo hi
      if rl ≥ minGoodRunLen then some (rl, if rev then reverseRange v lo (lo + rl) else v) else none
    else none
  match tryRun with
  | some (rl, v) => (mkSorted rl, v, s)
  | none =>
    if eager then
      let n := min smallSortThreshold len
      let (v, s) := smallSort v s lo (lo + n)
      (mkSorted n, v, s)
    else (mkUnsorted (min minGoodRunLen len), v, s)

/-- `logical_merge` of the runs `[lo, lo+len left)` and the following `right`. -/
@[specialize] def logicalMerge (quick : A → A → UInt64 → UInt64 → A × A) (v s : A) (lo : UInt64)
    (left right scratchLen : UInt64) : UInt64 × A × A :=
  let len := runLen left + runLen right
  let canFit := len ≤ scratchLen
  if !canFit || runSorted left || runSorted right then
    let mid := lo + runLen left
    let (v, s) := if runSorted left then (v, s) else quick v s lo mid
    let (v, s) := if runSorted right then (v, s) else quick v s mid (lo + len)
    let (v, s) := merge v s lo mid (lo + len)
    (mkSorted len, v, s)
  else (mkUnsorted len, v, s)

/-- Pop and merge while the top of the stack wants to be deeper than `desired`. -/
@[specialize] def collapse (quick : A → A → UInt64 → UInt64 → A × A) (lo scratchLen desired scanIdx : UInt64)
    (prevRun stackLen : UInt64) (runs depths : @& A) (v s : A) : UInt64 × UInt64 × A × A :=
  if h : 1 < stackLen ∧ get! depths (stackLen - 1) ≥ desired then
    have h1 : 1 < stackLen.toNat := h.1
    have hb := UInt64.toNat_lt stackLen
    let left := get! runs (stackLen - 1)
    let mergedLen := runLen left + runLen prevRun
    let start := lo + scanIdx - mergedLen
    let (prevRun, v, s) := logicalMerge quick v s start left prevRun scratchLen
    collapse quick lo scratchLen desired scanIdx prevRun (stackLen - 1) runs depths v s
  else (prevRun, stackLen, v, s)
termination_by stackLen.toNat
decreasing_by u64

/-- The main loop of `drift::sort` (`scanIdx` relative to `lo`). -/
@[specialize] def driftLoop (quick : A → A → UInt64 → UInt64 → A × A) (lo len scratchLen minGood scale : UInt64)
    (eager : Bool) (scanIdx prevRun stackLen : UInt64) (runs depths v s : A) : A × A :=
  if h : scanIdx < len then
    have h0 : scanIdx.toNat < len.toNat := h
    have hb := UInt64.toNat_lt len
    let (nextRun, v, s) := createRun v s (lo + scanIdx) (lo + len) minGood eager
    let nlen := runLen nextRun
    let desired := mergeTreeDepth (scanIdx - runLen prevRun) scanIdx (scanIdx + nlen) scale
    let (prevRun, stackLen, v, s) := collapse quick lo scratchLen desired scanIdx prevRun stackLen runs depths v s
    let runs := set! runs stackLen prevRun
    let depths := set! depths stackLen desired
    if h2 : 0 < nlen ∧ nlen ≤ len - scanIdx then
      have h3 : 0 < (runLen nextRun).toNat := h2.1
      have h4 : (runLen nextRun).toNat ≤ len.toNat - scanIdx.toNat := by
        have := UInt64.le_iff_toNat_le.mp h2.2; rwa [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt h)] at this
      have hb2 := UInt64.toNat_lt (runLen nextRun)
      driftLoop quick lo len scratchLen minGood scale eager (scanIdx + nlen) nextRun (stackLen + 1) runs depths v s
    else (v, s)
  else
    -- final dummy run with root-level desired depth: collapse everything
    let (prevRun, _, v, s) := collapse quick lo scratchLen 0 scanIdx prevRun stackLen runs depths v s
    if runSorted prevRun then (v, s) else quick v s lo (lo + len)
termination_by len.toNat - scanIdx.toNat
decreasing_by u64

/-- `drift::sort` on `v[lo, hi)`. -/
@[specialize] def driftSort (quick : A → A → UInt64 → UInt64 → A × A) (v s : A) (lo hi scratchLen : UInt64) (eager : Bool) : A × A :=
  let len := hi - lo
  if len < 2 then (v, s)
  else
    let scale := mergeTreeScaleFactor len
    let minGood := if len ≤ minSqrtRunLen * minSqrtRunLen then min (len - len / 2) minSqrtRunLen else sqrtApprox len
    driftLoop quick lo len scratchLen minGood scale eager 0 (mkSorted 0) 0 (zeros 66) (zeros 66) v s

/-- eager mode never produces unsorted runs, so the "quicksort" is never called; pass the small sort -/
def driftSortEager (v s : A) (lo hi scratchLen : UInt64) : A × A :=
  driftSort (fun v s lo hi => smallSort v s lo hi) v s lo hi scratchLen true

/-- `quicksort` on `v[lo, hi)`; `hasLA`/`la` encode `left_ancestor_pivot`. -/
def quicksort (v s : A) (lo hi scratchLen limit : UInt64) (hasLA : Bool) (la : UInt64) : A × A :=
  if hlo : hi < lo then (v, s) else
  have hlen : (hi - lo).toNat = hi.toNat - lo.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.not_lt.mp hlo)
  let len := hi - lo
  if len ≤ smallSortThreshold then smallSort v s lo hi
  else if limit == 0 then driftSortEager v s lo hi scratchLen
  else
    let limit := limit - 1
    let pivotPos := choosePivot v lo hi
    let pivot := get! v pivotPos
    let performEq := hasLA && !(lt la pivot)
    let (lp, v, s) := if performEq then (0, v, s) else stablePartition v s lo hi pivotPos false false
    let performEq := performEq || lp == 0
    if performEq then
      let (midEq, v, s) := stablePartition v s lo hi pivotPos true true
      if h : 0 < midEq ∧ midEq ≤ len then
        have hb := UInt64.toNat_lt hi
        have h1 : 0 < midEq.toNat := h.1
        have h2 : midEq.toNat ≤ hi.toNat - lo.toNat := by have := UInt64.le_iff_toNat_le.mp h.2; rwa [hlen] at this
        quicksort v s (lo + midEq) hi scratchLen limit false 0 else (v, s)
    else
      if h : 0 < lp ∧ lp < len then
        have hb := UInt64.toNat_lt hi
        have h1 : 0 < lp.toNat := h.1
        have h2 : lp.toNat < hi.toNat - lo.toNat := by have := UInt64.lt_iff_toNat_lt.mp h.2; rwa [hlen] at this
        let (v, s) := quicksort v s (lo + lp) hi scratchLen limit true pivot
        quicksort v s lo (lo + lp) scratchLen limit hasLA la
      else (v, s)
termination_by hi.toNat - lo.toNat
decreasing_by all_goals u64

/-- `stable_quicksort` -/
def stableQuicksort (v s : A) (lo hi scratchLen : UInt64) : A × A :=
  let limit := 2 * log2U ((hi - lo) ||| 1)
  quicksort v s lo hi scratchLen limit false 0

def driftSortFull (v s : A) (lo hi scratchLen : UInt64) : A × A :=
  driftSort (fun v s lo hi => stableQuicksort v s lo hi scratchLen) v s lo hi scratchLen false

/-! ## mod.rs: entry point -/

/-- `slice::sort` (stable) for `u64`. -/
def sort (xs : A) : A :=
  let n := xs.size.toUInt64
  if n < 2 then xs
  else if n ≤ maxLenAlwaysInsertion then insertionSortShiftLeft xs 0 n 1
  else
    -- driftsort_main: alloc_len = max(max(len - len/2, min(len, 8MB / 8)), SMALL_SORT_GENERAL_SCRATCH_LEN)
    let maxFullAlloc : UInt64 := 8000000 / 8
    let allocLen := max (max (n - n / 2) (min n maxFullAlloc)) smallSortScratchLen
    let s := zeros allocLen.toNat
    let eager := n ≤ smallSortThreshold * 2
    let (v, _) := if eager then driftSortEager xs s 0 n allocLen else driftSortFull xs s 0 n allocLen
    v

end Drift
