import MergeSort.Net4
import MergeSort.SkipMerge
import MergeSort.SmallRunsCorrect
import MergeSort.FindRun
import MergeSort.Adaptive
/-!
# driftsort, the bounds-safe version (Part 3)

The same algorithm as `Drift.lean` (Rust's `core::slice::sort::stable` for `u64`), but every array access
carries its bounds proof and the kernels are the verified ones from Parts 2 and 3:
`sort4` (network), `mergeKernel` (bidirectional / one-sided merge), `copyRange`, `insertionSortRange`,
`findRun`, `reverseRange`. Deviations from the Rust code, all semantically invisible for `u64`:
the 4-element network is wired differently (same output), the small sort's odd-length final merge is
one-sided, the physical merge goes through the scratch buffer and back, the scratch buffer has the
size of the input (Rust: `max(n - n/2, min(n, 1M))`), the run stack is a list, and the pivot
position is not special-cased in the partition (for `u64` the generic rule gives the same result).
The quicksort's depth-limit fallback is the eager drift sort, as in Rust.
-/
namespace DriftSort
open UInt64Array MergeSort MergeSort.Fast MergeSort.BottomUp

abbrev A := UInt64Array

theorem toNat_add_of_lt (a b : UInt64) (h : a.toNat + b.toNat < 2 ^ 64) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]
/-- Both buffers, sizes preserved. -/
abbrev VS (v s : A) := { p : A × A // p.1.size = v.size ∧ p.2.size = s.size }

@[inline] def castVS {v s v' s' : A} (r : VS v s) (h1 : v.size = v'.size) (h2 : s.size = s'.size) : VS v' s' :=
  ⟨r.1, r.2.1.trans h1, r.2.2.trans h2⟩

@[simp] theorem castVS_val {v s v' s' : A} (r : VS v s) (h1 : v.size = v'.size) (h2 : s.size = s'.size) :
    (castVS r h1 h2).1 = r.1 := rfl

def smallSortThreshold : UInt64 := 32

/-! ## The small sort (`small_sort_general_with_scratch`) -/

/-- Stages 2 and 3: `s[lo, lo+pre)` and `s[mid, mid+pre)` are sorted; copy the rest of each half of
    `v` into `s`, insert, then merge the two halves of `s` into `v[lo, hi)`. -/
def smallSortRest (v s : A) (lo mid hi pre : UInt64)
    (hv : hi.toNat ≤ v.size := by u64) (hs : hi.toNat ≤ s.size := by u64)
    (hvsz : v.size < 2 ^ 64 := by u64) (hssz : s.size < 2 ^ 64 := by u64)
    (h1 : lo.toNat + pre.toNat ≤ mid.toNat := by u64) (h2 : mid.toNat + pre.toNat ≤ hi.toNat := by u64) : VS v s :=
  have e1 : (lo + pre).toNat = lo.toNat + pre.toNat := toNat_add_of_lt _ _ (by omega)
  have e2 : (mid + pre).toNat = mid.toNat + pre.toNat := toNat_add_of_lt _ _ (by omega)
  let ⟨s1, hs1⟩ := copyRange (lo + pre) mid v s
  let ⟨s2, hs2⟩ := insertionSortRange lo mid (lo + pre) s1 (by rw [hs1]; exact hssz) (by rw [hs1]; omega) (by omega)
  let ⟨s3, hs3⟩ := copyRange (mid + pre) hi v s2 (by rw [hs2, hs1]; exact hssz) hv (by rw [hs2, hs1]; exact hs)
  let ⟨s4, hs4⟩ := insertionSortRange mid hi (mid + pre) s3 (by rw [hs3, hs2, hs1]; exact hssz) (by rw [hs3, hs2, hs1]; exact hs) (by omega)
  let ⟨v', hv'⟩ := mergeKernel lo mid hi s4 v hvsz (by rw [hs4, hs3, hs2, hs1]; exact hs) hv (by omega) (by omega)
  ⟨(v', s4), hv', hs4.trans (hs3.trans (hs2.trans hs1))⟩

/-- `small_sort_general_with_scratch` on `v[lo, hi)`, `hi - lo ≤ 32`. -/
def smallSort (v s : A) (lo hi : UInt64)
    (hv : hi.toNat ≤ v.size := by u64) (hs : hi.toNat ≤ s.size := by u64)
    (hvsz : v.size < 2 ^ 64 := by u64) (hssz : s.size < 2 ^ 64 := by u64)
    (hlo : lo.toNat ≤ hi.toNat := by u64) : VS v s :=
  let len := hi - lo
  have hlen : len.toNat = hi.toNat - lo.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hlo)
  if h2 : len < 2 then ⟨(v, s), rfl, rfl⟩
  else
    have h2 : 2 ≤ len.toNat := by have := UInt64.not_lt.mp h2; have := UInt64.le_iff_toNat_le.mp this; simpa using this
    let half := len / 2
    have hhalf : half.toNat = len.toNat / 2 := by simp [half]
    let mid := lo + half
    have hmid : mid.toNat = lo.toNat + half.toNat := toNat_add_of_lt _ _ (by omega)
    if h16 : 16 ≤ len then
      have h16 : 16 ≤ len.toNat := by have := UInt64.le_iff_toNat_le.mp h16; simpa using this
      have e4 : (lo + 4).toNat = lo.toNat + 4 := toNat_add_of_lt _ _ (by simp; omega)
      have e8 : (lo + 8).toNat = lo.toNat + 8 := toNat_add_of_lt _ _ (by simp; omega)
      have m4 : (mid + 4).toNat = mid.toNat + 4 := toNat_add_of_lt _ _ (by simp; omega)
      have m8 : (mid + 8).toNat = mid.toNat + 8 := toNat_add_of_lt _ _ (by simp; omega)
      let ⟨v1, hv1⟩ := sort4 lo v hvsz (by omega)
      let ⟨v2, hv2⟩ := sort4 (lo + 4) v1 (by rw [hv1]; exact hvsz) (by rw [hv1]; omega)
      let ⟨s1, hs1⟩ := mergeKernel lo (lo + 4) (lo + 8) v2 s hssz (by rw [hv2, hv1]; omega) (by omega) (by omega) (by omega)
      let ⟨v3, hv3⟩ := sort4 mid v2 (by rw [hv2, hv1]; exact hvsz) (by rw [hv2, hv1]; omega)
      let ⟨v4, hv4⟩ := sort4 (mid + 4) v3 (by rw [hv3, hv2, hv1]; exact hvsz) (by rw [hv3, hv2, hv1]; omega)
      let ⟨s2, hs2⟩ := mergeKernel mid (mid + 4) (mid + 8) v4 s1 (by rw [hs1]; exact hssz) (by rw [hv4, hv3, hv2, hv1]; omega)
        (by rw [hs1]; omega) (by omega) (by omega)
      castVS (smallSortRest v4 s2 lo mid hi 8 (by rw [hv4, hv3, hv2, hv1]; exact hv) (by rw [hs2, hs1]; exact hs)
        (by rw [hv4, hv3, hv2, hv1]; exact hvsz) (by rw [hs2, hs1]; exact hssz) (by simp; omega) (by simp; omega))
        (hv4.trans (hv3.trans (hv2.trans hv1))) (hs2.trans hs1)
    else if h8 : 8 ≤ len then
      have h8 : 8 ≤ len.toNat := by have := UInt64.le_iff_toNat_le.mp h8; simpa using this
      have e4 : (lo + 4).toNat = lo.toNat + 4 := toNat_add_of_lt _ _ (by simp; omega)
      have m4 : (mid + 4).toNat = mid.toNat + 4 := toNat_add_of_lt _ _ (by simp; omega)
      let ⟨v1, hv1⟩ := sort4 lo v hvsz (by omega)
      let ⟨s1, hs1⟩ := copyRange lo (lo + 4) v1 s hssz (by rw [hv1]; omega) (by omega)
      let ⟨v2, hv2⟩ := sort4 mid v1 (by rw [hv1]; exact hvsz) (by rw [hv1]; omega)
      let ⟨s2, hs2⟩ := copyRange mid (mid + 4) v2 s1 (by rw [hs1]; exact hssz) (by rw [hv2, hv1]; omega) (by rw [hs1]; omega)
      castVS (smallSortRest v2 s2 lo mid hi 4 (by rw [hv2, hv1]; exact hv) (by rw [hs2, hs1]; exact hs)
        (by rw [hv2, hv1]; exact hvsz) (by rw [hs2, hs1]; exact hssz) (by simp; omega) (by simp; omega))
        (hv2.trans hv1) (hs2.trans hs1)
    else
      have e1 : (lo + 1).toNat = lo.toNat + 1 := toNat_add_of_lt _ _ (by simp; omega)
      have m1 : (mid + 1).toNat = mid.toNat + 1 := toNat_add_of_lt _ _ (by simp; omega)
      let ⟨s1, hs1⟩ := copyRange lo (lo + 1) v s hssz (by omega) (by omega)
      let ⟨s2, hs2⟩ := copyRange mid (mid + 1) v s1 (by rw [hs1]; exact hssz) (by omega) (by rw [hs1]; omega)
      castVS (smallSortRest v s2 lo mid hi 1 hv (by rw [hs2, hs1]; exact hs) hvsz (by rw [hs2, hs1]; exact hssz)
        (by simp; omega) (by simp; omega)) rfl (hs2.trans hs1)

/-! ## The physical merge (`merge.rs`): through the scratch buffer and back -/

def mergeRuns (v s : A) (lo mid hi : UInt64)
    (hv : hi.toNat ≤ v.size := by u64) (hs : hi.toNat ≤ s.size := by u64)
    (hvsz : v.size < 2 ^ 64 := by u64) (hssz : s.size < 2 ^ 64 := by u64)
    (hlo : lo.toNat ≤ mid.toNat := by u64) (hmid : mid.toNat ≤ hi.toNat := by u64) : VS v s :=
  let ⟨s1, hs1⟩ := mergeKernelS lo mid hi v s hssz hv hs hlo hmid
  let ⟨v1, hv1⟩ := copyRange lo hi s1 v hvsz (by rw [hs1]; exact hs) hv
  ⟨(v1, s1), hv1, hs1⟩

/-! ## The stable partition (`quicksort.rs`) -/

/-- The two partition predicates. Separate definitions (no `Bool` literal at the call site), so that the
    compiler specialises the scan on each of them instead of on a shared mode flag. -/
def ltPivot (pivot x : UInt64) : Bool := decide (x < pivot)

def lePivot (pivot x : UInt64) : Bool := decide (x ≤ pivot)

/-- Both modes, for the specification. -/
def goesLeft (eq : Bool) (pivot : UInt64) : UInt64 → Bool := if eq then lePivot pivot else ltPivot pivot

/-- The result of a partition scan: the buffer and the size of the left part. (A structure, so that the
    `UInt64` is stored unboxed: one allocation per partition instead of two.) -/
structure Scan where
  buf : A
  nl : UInt64

/-- The scan: `v[i, hi)` still to do, `nl` elements already on the left (`s[lo, lo+nl)`), the right
    ones at the back of `s[lo, hi)` in reverse order. `sv = hi - (i - lo)` is a running position: after its
    decrement, `sv + nl` is the write position of the next right element (`hi - 1 - r`). Branchless: one
    select, one store. The predicate is a parameter so that each partition mode compiles to its own loop. -/
@[specialize] def partScan (p : UInt64 → Bool) (v : @& A) (s : A) (lo hi i nl sv : UInt64)
    (hv : hi.toNat ≤ v.size := by u64) (hs : hi.toNat ≤ s.size := by u64) (hssz : s.size < 2 ^ 64 := by u64)
    (hi1 : lo.toNat ≤ i.toNat := by u64) (_hi2 : i.toNat ≤ hi.toNat := by u64)
    (hnl : nl.toNat ≤ i.toNat - lo.toNat := by u64)
    (hsv : sv.toNat = hi.toNat - (i.toNat - lo.toNat) := by u64) :
    { q : Scan // q.buf.size = s.size ∧ nl.toNat ≤ q.nl.toNat ∧ q.nl.toNat ≤ nl.toNat + (hi.toNat - i.toNat) } :=
  if h : i < hi then
    have hlt : i.toNat < hi.toNat := UInt64.lt_iff_toNat_lt.mp h
    have hb := UInt64.toNat_lt hi
    let x := v.get i
    let gl := p x
    let sv' := sv - 1
    have esv : sv'.toNat = sv.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
    let base := if gl then lo else sv'
    have hbase : base.toNat = (if gl then lo.toNat else hi.toNat - 1 - (i.toNat - lo.toNat)) := by
      show (if gl then lo else sv').toNat = _
      split <;> omega
    let dst := base + nl
    have hdst : dst.toNat = base.toNat + nl.toNat := toNat_add_of_lt _ _ (by rw [hbase]; split <;> omega)
    have hdst' : dst.toNat < hi.toNat := by rw [hdst, hbase]; split <;> omega
    -- (the store first, the count after: the C compiler then folds the count into the compare)
    let s' := s.set dst x (by omega)
    have hs' : s'.size = s.size := size_set _ _ _ _
    let d : UInt64 := if gl then 1 else 0
    have hd : d.toNat ≤ 1 := by show (if gl then (1 : UInt64) else 0).toNat ≤ 1; split <;> simp
    have en : (nl + d).toNat = nl.toNat + d.toNat := toNat_add_of_lt _ _ (by omega)
    have ei : (i + 1).toNat = i.toNat + 1 := toNat_add_of_lt _ _ (by simp; omega)
    let rec_ := partScan p v s' lo hi (i + 1) (nl + d) sv' (hv := hv) (hs := by rw [hs']; exact hs)
      (hssz := by rw [hs']; exact hssz) (hi1 := by omega) (_hi2 := by omega) (hnl := by omega) (hsv := by rw [esv, ei]; omega)
    ⟨rec_.1, rec_.2.1.trans hs', Nat.le_trans (by rw [en]; omega) rec_.2.2.1,
      Nat.le_trans rec_.2.2.2 (by rw [en, ei]; omega)⟩
  else ⟨⟨s, nl⟩, rfl, by simp, by simp⟩
termination_by hi.toNat - i.toNat
decreasing_by all_goals u64

/-- `stable_partition` of `a[lo, hi)` by `p`, into `b[lo, hi)`: the `p`-elements first, in their order,
    then the others (in reverse order, which is unobservable for `u64`s). `a` is left untouched and the
    quicksort continues with the buffers swapped, so nothing is copied back. Returns the size of the left
    part. Specialised on `p`, so each partition mode is its own scan loop. -/
@[specialize] def stablePartition (p : UInt64 → Bool) (a : @& A) (b : A) (lo hi : UInt64)
    (ha : hi.toNat ≤ a.size := by u64) (hb : hi.toNat ≤ b.size := by u64) (hbsz : b.size < 2 ^ 64 := by u64)
    (hlo : lo.toNat ≤ hi.toNat := by u64) :
    { r : Scan // r.buf.size = b.size ∧ r.nl.toNat ≤ hi.toNat - lo.toNat } :=
  let ⟨⟨b1, nl⟩, hb1, _, hnl⟩ := partScan p a b lo hi lo 0 hi ha hb hbsz (by omega) hlo (by simp) (by simp)
  ⟨⟨b1, nl⟩, hb1, by simpa using hnl⟩

/-! ## Pivot selection (`shared/pivot.rs`), returning an index with its bound -/

def median3 (v : @& A) (a b c : UInt64) (ha : a.toNat < v.size) (hb : b.toNat < v.size) (hc : c.toNat < v.size) :
    { i : UInt64 // i = a ∨ i = b ∨ i = c } :=
  let x := decide (v.get a ha < v.get b hb)
  let y := decide (v.get a ha < v.get c hc)
  if x == y then
    let z := decide (v.get b hb < v.get c hc)
    if z != x then ⟨c, Or.inr (Or.inr rfl)⟩ else ⟨b, Or.inr (Or.inl rfl)⟩
  else ⟨a, Or.inl rfl⟩

/-- `median3_rec` on the three windows starting at `a`, `b`, `c`, each of length `n`; returns an index
    inside `[lo, hi)` given that the windows are. -/
def median3Rec (v : @& A) (lo hi a b c n : UInt64) (hvsz : v.size < 2 ^ 64) (hv : hi.toNat ≤ v.size)
    (hn : 0 < n.toNat) (ha : lo.toNat ≤ a.toNat ∧ a.toNat + n.toNat ≤ hi.toNat)
    (hb : lo.toNat ≤ b.toNat ∧ b.toNat + n.toNat ≤ hi.toNat) (hc : lo.toNat ≤ c.toNat ∧ c.toNat + n.toNat ≤ hi.toNat) :
    { i : UInt64 // lo.toNat ≤ i.toNat ∧ i.toNat < hi.toNat } :=
  if h : 8 ≤ n then
    have h8 : 8 ≤ n.toNat := by have := UInt64.le_iff_toNat_le.mp h; simpa using this
    have hbnd := UInt64.toNat_lt hi
    let n8 := n / 8
    have hn8 : n8.toNat = n.toNat / 8 := by simp [n8]
    have ea4 : (a + n8 * 4).toNat = a.toNat + n8.toNat * 4 := by u64
    have ea7 : (a + n8 * 7).toNat = a.toNat + n8.toNat * 7 := by u64
    have eb4 : (b + n8 * 4).toNat = b.toNat + n8.toNat * 4 := by u64
    have eb7 : (b + n8 * 7).toNat = b.toNat + n8.toNat * 7 := by u64
    have ec4 : (c + n8 * 4).toNat = c.toNat + n8.toNat * 4 := by u64
    have ec7 : (c + n8 * 7).toNat = c.toNat + n8.toNat * 7 := by u64
    let ⟨a', ha'⟩ := median3Rec v lo hi a (a + n8 * 4) (a + n8 * 7) n8 hvsz hv (by omega) (by omega) (by omega) (by omega)
    let ⟨b', hb'⟩ := median3Rec v lo hi b (b + n8 * 4) (b + n8 * 7) n8 hvsz hv (by omega) (by omega) (by omega) (by omega)
    let ⟨c', hc'⟩ := median3Rec v lo hi c (c + n8 * 4) (c + n8 * 7) n8 hvsz hv (by omega) (by omega) (by omega) (by omega)
    let ⟨i, hi⟩ := median3 v a' b' c' (by omega) (by omega) (by omega)
    ⟨i, by rcases hi with h | h | h <;> rw [h] <;> omega⟩
  else
    let ⟨i, hi⟩ := median3 v a b c (by omega) (by omega) (by omega)
    ⟨i, by rcases hi with h | h | h <;> rw [h] <;> omega⟩
termination_by n.toNat
decreasing_by all_goals u64

/-- `choose_pivot` on `v[lo, hi)`, `hi - lo ≥ 8`. -/
def choosePivot (v : @& A) (lo hi : UInt64) (hvsz : v.size < 2 ^ 64) (hv : hi.toNat ≤ v.size)
    (h8 : lo.toNat + 8 ≤ hi.toNat) : { i : UInt64 // lo.toNat ≤ i.toNat ∧ i.toNat < hi.toNat } :=
  have hbnd := UInt64.toNat_lt hi
  let len := hi - lo
  have hlen : len.toNat = hi.toNat - lo.toNat := UInt64.toNat_sub_of_le _ _ (by u64)
  let d8 := len / 8
  have hd8 : d8.toNat = len.toNat / 8 := by simp [d8]
  have e4 : (lo + d8 * 4).toNat = lo.toNat + d8.toNat * 4 := by u64
  have e7 : (lo + d8 * 7).toNat = lo.toNat + d8.toNat * 7 := by u64
  if len < 64 then
    let ⟨i, hi⟩ := median3 v lo (lo + d8 * 4) (lo + d8 * 7) (by omega) (by omega) (by omega)
    ⟨i, by rcases hi with h | h | h <;> rw [h] <;> omega⟩
  else
    median3Rec v lo hi lo (lo + d8 * 4) (lo + d8 * 7) d8 hvsz hv (by omega) (by omega) (by omega) (by omega)

/-! ## Runs and the powersort stack (`drift.rs`); the stack is a list of (run, desired depth) -/

/-- A logical run: its length and whether it is sorted (Rust packs this into a `usize`). -/
structure Run where
  len : UInt64
  sorted : Bool

@[inline] def mkSorted (len : UInt64) : Run := ⟨len, true⟩
@[inline] def mkUnsorted (len : UInt64) : Run := ⟨len, false⟩
@[inline] def runLen (r : Run) : UInt64 := r.len
@[inline] def runSorted (r : Run) : Bool := r.sorted

@[inline] def log2U (x : UInt64) : UInt64 := x.toNat.log2.toUInt64
def clz (x : UInt64) : UInt64 := if x == 0 then 64 else 63 - log2U x
def mergeTreeScaleFactor (n : UInt64) : UInt64 := (((1 : UInt64) <<< 62) + n - 1) / n
def mergeTreeDepth (left mid right scale : UInt64) : UInt64 :=
  clz ((scale * (left + mid)) ^^^ (scale * (mid + right)))
def sqrtApprox (n : UInt64) : UInt64 :=
  let ilog := log2U (n ||| 1)
  let shift := (ilog + 1) / 2
  ((1 <<< shift) + (n >>> shift)) / 2
def minSqrtRunLen : UInt64 := 64

/-- A range sorter for the unsorted runs: `quick v s lo hi …` sorts `v[lo, hi)`. -/
abbrev Quick := (v s : A) → (lo hi : UInt64) → hi.toNat ≤ v.size → hi.toNat ≤ s.size →
    v.size < 2 ^ 64 → s.size < 2 ^ 64 → lo.toNat ≤ hi.toNat → VS v s

/-- No natural run: in eager mode a small-sorted run of ≤ 32, else an unsorted run of ≤ `minGood`. -/
def createRunRest (v s : A) (lo hi minGood : UInt64) (eager : Bool)
    (hv : hi.toNat ≤ v.size) (hs : hi.toNat ≤ s.size) (hvsz : v.size < 2 ^ 64) (hssz : s.size < 2 ^ 64)
    (hlo : lo.toNat < hi.toNat) (hmg : 0 < minGood.toNat) :
    { r : Run × A × A // r.2.1.size = v.size ∧ r.2.2.size = s.size ∧
        0 < r.1.len.toNat ∧ lo.toNat + r.1.len.toNat ≤ hi.toNat } :=
  have hbnd := UInt64.toNat_lt hi
  let len := hi - lo
  have hlen : len.toNat = hi.toNat - lo.toNat := UInt64.toNat_sub_of_le _ _ (by u64)
  if eager then
    let m := if smallSortThreshold ≤ len then smallSortThreshold else len
    have hm : 0 < m.toNat ∧ lo.toNat + m.toNat ≤ hi.toNat := by
      show 0 < (if smallSortThreshold ≤ len then smallSortThreshold else len).toNat ∧
        lo.toNat + (if smallSortThreshold ≤ len then smallSortThreshold else len).toNat ≤ hi.toNat
      split <;> (simp only [smallSortThreshold, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *; omega)
    have em : (lo + m).toNat = lo.toNat + m.toNat := toNat_add_of_lt _ _ (by omega)
    let ⟨(v1, s1), hv1, hs1⟩ := smallSort v s lo (lo + m) (by rw [em]; omega) (by rw [em]; omega) hvsz hssz (by rw [em]; omega)
    ⟨(mkSorted m, v1, s1), hv1, hs1, hm.1, hm.2⟩
  else
    let m := if minGood ≤ len then minGood else len
    have hm : 0 < m.toNat ∧ lo.toNat + m.toNat ≤ hi.toNat := by
      show 0 < (if minGood ≤ len then minGood else len).toNat ∧
        lo.toNat + (if minGood ≤ len then minGood else len).toNat ≤ hi.toNat
      split <;> (simp only [UInt64.le_iff_toNat_le] at *; omega)
    ⟨(mkUnsorted m, v, s), rfl, rfl, hm.1, hm.2⟩

/-- `create_run` on `v[lo, hi)` (`lo < hi`): a sorted natural run of length ≥ `minGood` (a descending
    one reversed in place), else `createRunRest`. The run length is ≥ 1. -/
def createRun (v s : A) (lo hi minGood : UInt64) (eager : Bool)
    (hv : hi.toNat ≤ v.size) (hs : hi.toNat ≤ s.size) (hvsz : v.size < 2 ^ 64) (hssz : s.size < 2 ^ 64)
    (hlo : lo.toNat < hi.toNat) (hmg : 0 < minGood.toNat) :
    { r : Run × A × A // r.2.1.size = v.size ∧ r.2.2.size = s.size ∧
        0 < r.1.len.toNat ∧ lo.toNat + r.1.len.toNat ≤ hi.toNat } :=
  let len := hi - lo
  have hlen : len.toNat = hi.toNat - lo.toNat := UInt64.toNat_sub_of_le _ _ (by u64)
  if minGood ≤ len then
    let ⟨(e, v1), he1, he2, hv1⟩ := findRun lo hi v hvsz hv hlo
    have he1' : lo.toNat < e.toNat := he1
    have he2' : e.toNat ≤ hi.toNat := he2
    have hv1' : v1.size = v.size := hv1
    have ee : (e - lo).toNat = e.toNat - lo.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))
    if h : minGood ≤ e - lo then
      have h' := UInt64.le_iff_toNat_le.mp h
      ⟨(mkSorted (e - lo), v1, s), hv1', rfl, by show 0 < (e - lo).toNat; rw [ee]; omega,
        by show lo.toNat + (e - lo).toNat ≤ hi.toNat; rw [ee]; omega⟩
    else
      let ⟨r, hr1, hr2, hr3, hr4⟩ := createRunRest v1 s lo hi minGood eager (by rw [hv1']; exact hv) hs (by rw [hv1']; exact hvsz) hssz hlo hmg
      ⟨r, hr1.trans hv1', hr2, hr3, hr4⟩
  else createRunRest v s lo hi minGood eager hv hs hvsz hssz hlo hmg

/-- `logical_merge` of the adjacent runs `v[lo, mid)` (sorted iff `lsorted`) and `v[mid, hi)`:
    physical when one side is sorted or the pair no longer fits the scratch buffer. Returns the
    sorted flag of the combined run. -/
@[specialize] def logicalMerge (quick : Quick) (v s : A) (lo mid hi scratchLen : UInt64) (lsorted rsorted : Bool)
    (hv : hi.toNat ≤ v.size) (hs : hi.toNat ≤ s.size) (hvsz : v.size < 2 ^ 64) (hssz : s.size < 2 ^ 64)
    (hlo : lo.toNat ≤ mid.toNat) (hmid : mid.toNat ≤ hi.toNat) :
    { r : Bool × A × A // r.2.1.size = v.size ∧ r.2.2.size = s.size } :=
  let canFit := hi - lo ≤ scratchLen
  if !canFit || lsorted || rsorted then
    let ⟨(v1, s1), hv1, hs1⟩ : VS v s :=
      if lsorted then ⟨(v, s), rfl, rfl⟩ else quick v s lo mid (by omega) (by omega) hvsz hssz hlo
    let ⟨(v2, s2), hv2, hs2⟩ : VS v1 s1 :=
      if rsorted then ⟨(v1, s1), rfl, rfl⟩
      else quick v1 s1 mid hi (by rw [hv1]; exact hv) (by rw [hs1]; exact hs) (by rw [hv1]; exact hvsz) (by rw [hs1]; exact hssz) hmid
    let ⟨(v3, s3), hv3, hs3⟩ := mergeRuns v2 s2 lo mid hi (by rw [hv2, hv1]; exact hv) (by rw [hs2, hs1]; exact hs)
      (by rw [hv2, hv1]; exact hvsz) (by rw [hs2, hs1]; exact hssz) hlo hmid
    ⟨(true, v3, s3), hv3.trans (hv2.trans hv1), hs3.trans (hs2.trans hs1)⟩
  else ⟨(false, v, s), rfl, rfl⟩

/-- The run stack: (run, desired depth), top first. -/
abbrev Stack := List (Run × UInt64)
def stackSum (st : Stack) : Nat := (st.map (fun e => e.1.len.toNat)).sum

@[simp] theorem stackSum_nil : stackSum [] = 0 := rfl
@[simp] theorem stackSum_cons (e : Run × UInt64) (st : Stack) : stackSum (e :: st) = e.1.len.toNat + stackSum st := by
  simp [stackSum]

/-- Pop and merge while the top of the stack (never the bottom dummy) wants to be at least as deep
    as `desired`. `prevRun` occupies `v[lo + scanIdx - prevRun.len, lo + scanIdx)`. -/
@[specialize] def collapse (quick : Quick) (lo scanIdx scratchLen desired : UInt64) (prevRun : Run) (st : Stack) (v s : A)
    (hv : lo.toNat + scanIdx.toNat ≤ v.size) (hs : lo.toNat + scanIdx.toNat ≤ s.size)
    (hvsz : v.size < 2 ^ 64) (hssz : s.size < 2 ^ 64)
    (hsum : stackSum st + prevRun.len.toNat = scanIdx.toNat) :
    { r : Run × Stack × A × A // r.2.2.1.size = v.size ∧ r.2.2.2.size = s.size ∧
        stackSum r.2.1 + r.1.len.toNat = scanIdx.toNat } :=
  match st with
  | [] => ⟨(prevRun, [], v, s), rfl, rfl, by simpa using hsum⟩
  | (left, depth) :: rest =>
    if rest ≠ [] ∧ desired ≤ depth then
      have hbnd := UInt64.toNat_lt scanIdx
      have hsum' : left.len.toNat + stackSum rest + prevRun.len.toNat = scanIdx.toNat := by simpa [Nat.add_assoc] using hsum
      let mergedLen := left.len + prevRun.len
      have hml : mergedLen.toNat = left.len.toNat + prevRun.len.toNat := toNat_add_of_lt _ _ (by omega)
      let «end» := lo + scanIdx
      have hen : «end».toNat = lo.toNat + scanIdx.toNat := toNat_add_of_lt _ _ (by omega)
      let start := «end» - mergedLen
      have hst : start.toNat = lo.toNat + scanIdx.toNat - mergedLen.toNat := by
        show («end» - mergedLen).toNat = _
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hen]; omega)), hen]
      let mid := start + left.len
      have hmi : mid.toNat = start.toNat + left.len.toNat := toNat_add_of_lt _ _ (by omega)
      let ⟨(sorted, v1, s1), hv1, hs1⟩ := logicalMerge quick v s start mid «end» scratchLen left.sorted prevRun.sorted
        (by omega) (by omega) hvsz hssz (by omega) (by omega)
      let ⟨r, hr1, hr2, hr3⟩ := collapse quick lo scanIdx scratchLen desired ⟨mergedLen, sorted⟩ rest v1 s1
        (by rw [hv1]; exact hv) (by rw [hs1]; exact hs) (by rw [hv1]; exact hvsz) (by rw [hs1]; exact hssz)
        (by simp only [hml]; omega)
      ⟨r, hr1.trans hv1, hr2.trans hs1, hr3⟩
    else ⟨(prevRun, (left, depth) :: rest, v, s), rfl, rfl, hsum⟩

/-- The main loop of `drift::sort` on `v[lo, lo+len)`; `scanIdx` is relative to `lo`. -/
@[specialize] def driftLoop (quick : Quick) (lo len scratchLen minGood scale : UInt64) (eager : Bool)
    (scanIdx : UInt64) (prevRun : Run) (st : Stack) (v s : A)
    (hv : lo.toNat + len.toNat ≤ v.size) (hs : lo.toNat + len.toNat ≤ s.size)
    (hvsz : v.size < 2 ^ 64) (hssz : s.size < 2 ^ 64) (hmg : 0 < minGood.toNat)
    (hscan : scanIdx.toNat ≤ len.toNat) (hsum : stackSum st + prevRun.len.toNat = scanIdx.toNat) : VS v s :=
  have hbnd := UInt64.toNat_lt len
  if h : scanIdx < len then
    have hlt : scanIdx.toNat < len.toNat := UInt64.lt_iff_toNat_lt.mp h
    have es : (lo + scanIdx).toNat = lo.toNat + scanIdx.toNat := toNat_add_of_lt _ _ (by omega)
    have el : (lo + len).toNat = lo.toNat + len.toNat := toNat_add_of_lt _ _ (by omega)
    let ⟨(nextRun, v1, s1), hv1, hs1, hpos, hle⟩ := createRun v s (lo + scanIdx) (lo + len) minGood eager
      (by rw [el]; exact hv) (by rw [el]; exact hs) hvsz hssz (by omega) hmg
    have hv1' : v1.size = v.size := hv1
    have hs1' : s1.size = s.size := hs1
    have hpos' : 0 < nextRun.len.toNat := hpos
    have hle' : (lo + scanIdx).toNat + nextRun.len.toNat ≤ (lo + len).toNat := hle
    have hnlen : scanIdx.toNat + nextRun.len.toNat ≤ len.toNat := by omega
    let desired := mergeTreeDepth (scanIdx - prevRun.len) scanIdx (scanIdx + nextRun.len) scale
    let ⟨(prevRun', st', v2, s2), hv2, hs2, hsum'⟩ := collapse quick lo scanIdx scratchLen desired prevRun st v1 s1
      (by rw [hv1']; omega) (by rw [hs1']; omega) (by rw [hv1']; exact hvsz) (by rw [hs1']; exact hssz) hsum
    have hv2' : v2.size = v1.size := hv2
    have hs2' : s2.size = s1.size := hs2
    have hsum'' : stackSum st' + prevRun'.len.toNat = scanIdx.toNat := hsum'
    have esn : (scanIdx + nextRun.len).toNat = scanIdx.toNat + nextRun.len.toNat := toNat_add_of_lt _ _ (by omega)
    castVS (driftLoop quick lo len scratchLen minGood scale eager (scanIdx + nextRun.len) nextRun ((prevRun', desired) :: st') v2 s2
      (by rw [hv2', hv1']; exact hv) (by rw [hs2', hs1']; exact hs) (by rw [hv2', hv1']; exact hvsz) (by rw [hs2', hs1']; exact hssz) hmg
      (by rw [esn]; exact hnlen) (by simp only [stackSum_cons, esn]; omega)) (hv2'.trans hv1') (hs2'.trans hs1')
  else
    -- the final dummy run wants root depth: collapse everything, then sort the rest if unsorted
    let ⟨(prevRun', _, v2, s2), hv2, hs2, _⟩ := collapse quick lo scanIdx scratchLen 0 prevRun st v s
      (by omega) (by omega) hvsz hssz hsum
    have hv2' : v2.size = v.size := hv2
    have hs2' : s2.size = s.size := hs2
    -- (the length check always holds: the bottom of the stack is the empty dummy run; it is checked
    -- rather than proved as an invariant)
    if prevRun'.sorted ∧ prevRun'.len = len then ⟨(v2, s2), hv2', hs2'⟩
    else
      have el : (lo + len).toNat = lo.toNat + len.toNat := toNat_add_of_lt _ _ (by omega)
      castVS (quick v2 s2 lo (lo + len) (by rw [hv2', el]; exact hv) (by rw [hs2', el]; exact hs) (by rw [hv2']; exact hvsz)
        (by rw [hs2']; exact hssz) (by omega)) hv2' hs2'
termination_by len.toNat - scanIdx.toNat
decreasing_by all_goals (simp only [esn]; omega)

/-- `drift::sort` on `v[lo, hi)`. -/
@[specialize] def driftSort (quick : Quick) (v s : A) (lo hi scratchLen : UInt64) (eager : Bool)
    (hv : hi.toNat ≤ v.size) (hs : hi.toNat ≤ s.size) (hvsz : v.size < 2 ^ 64) (hssz : s.size < 2 ^ 64)
    (hlo : lo.toNat ≤ hi.toNat) : VS v s :=
  let len := hi - lo
  have hlen : len.toNat = hi.toNat - lo.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hlo)
  if len < 2 then ⟨(v, s), rfl, rfl⟩
  else
    let scale := mergeTreeScaleFactor len
    let minGood0 := if len ≤ minSqrtRunLen * minSqrtRunLen then min (len - len / 2) minSqrtRunLen else sqrtApprox len
    -- (always ≥ 1 for len ≥ 2; the `max` only makes that fact free)
    let minGood := if minGood0 == 0 then 1 else minGood0
    have hmg : 0 < minGood.toNat := by
      show 0 < (if minGood0 == 0 then 1 else minGood0).toNat
      split
      · decide
      · rename_i h; have : minGood0 ≠ 0 := by simpa using h
        have : minGood0.toNat ≠ 0 := fun c => this (UInt64.toNat.inj (by simpa using c))
        omega
    driftLoop quick lo len scratchLen minGood scale eager 0 ⟨0, true⟩ [] v s (by omega) (by omega) hvsz hssz hmg
      (Nat.zero_le _) rfl

/-- A range sort that is never executed in eager mode (unsorted runs do not exist there), but the
    generic loop needs one: insertion sort (verified, quadratic). -/
def insertionQuick : Quick := fun v s lo hi hv _ hvsz _ hlo =>
  let ⟨v1, hv1⟩ := insertionSortRange lo hi lo v hvsz hv (by omega)
  ⟨(v1, s), hv1, rfl⟩

def driftSortEager (v s : A) (lo hi scratchLen : UInt64) (hv : hi.toNat ≤ v.size) (hs : hi.toNat ≤ s.size)
    (hvsz : v.size < 2 ^ 64) (hssz : s.size < 2 ^ 64) (hlo : lo.toNat ≤ hi.toNat) : VS v s :=
  driftSort insertionQuick v s lo hi scratchLen true hv hs hvsz hssz hlo

/-- `quicksort` on `a[lo, hi)`, ping-pong style: the partition writes `b[lo, hi)` and the recursion
    continues with the buffers swapped, so nothing is copied back (`a` is left as it was and becomes the
    scratch). The sorted range lands in `b` if `toB`, else in `a`; a leaf copies its block over when it
    has to. `hasLA`/`la` encode `left_ancestor_pivot`. -/
def quicksort (a b : A) (lo hi scratchLen limit : UInt64) (hasLA : Bool) (la : UInt64) (toB : Bool)
    (ha : hi.toNat ≤ a.size) (hb : hi.toNat ≤ b.size) (hasz : a.size < 2 ^ 64) (hbsz : b.size < 2 ^ 64)
    (hlo : lo.toNat ≤ hi.toNat) : VS a b :=
  have hbnd := UInt64.toNat_lt hi
  let len := hi - lo
  have hlen : len.toNat = hi.toNat - lo.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hlo)
  if h32 : len ≤ smallSortThreshold then
    if toB then
      let ⟨b1, hb1⟩ := copyRange lo hi a b hbsz ha hb
      let ⟨(b2, a2), hb2, ha2⟩ := smallSort b1 a lo hi (by rw [hb1]; exact hb) ha (by rw [hb1]; exact hbsz) hasz hlo
      ⟨(a2, b2), ha2, hb2.trans hb1⟩
    else smallSort a b lo hi ha hb hasz hbsz hlo
  else
    have h32 : 32 < len.toNat := by
      have := UInt64.not_le.mp h32; have := UInt64.lt_iff_toNat_lt.mp this
      simpa [smallSortThreshold] using this
    if limit == 0 then
      let ⟨(a1, b1), ha1, hb1⟩ := driftSortEager a b lo hi scratchLen ha hb hasz hbsz hlo
      have ha1' : a1.size = a.size := ha1
      have hb1' : b1.size = b.size := hb1
      if toB then
        let ⟨b2, hb2⟩ := copyRange lo hi a1 b1 (by rw [hb1']; exact hbsz) (by rw [ha1']; exact ha) (by rw [hb1']; exact hb)
        ⟨(a1, b2), ha1', hb2.trans hb1'⟩
      else ⟨(a1, b1), ha1', hb1'⟩
    else
      let limit := limit - 1
      let ⟨pp, hpp⟩ := choosePivot a lo hi hasz ha (by omega)
      let pivot := a.get pp (by omega)
      let performEq := hasLA && decide (pivot ≤ la)
      let ⟨⟨b1, nl⟩, hb1, hnl⟩ : { r : Scan // r.buf.size = b.size ∧ r.nl.toNat ≤ hi.toNat - lo.toNat } :=
        if performEq then ⟨⟨b, 0⟩, rfl, by simp⟩ else stablePartition (ltPivot pivot) a b lo hi ha hb hbsz hlo
      have hb1' : b1.size = b.size := hb1
      have hnl' : nl.toNat ≤ hi.toNat - lo.toNat := hnl
      if performEq || nl == 0 then
        -- the equal-element partition, again from the untouched `a`: `b2[lo, lo + midEq)` is all pivots
        let ⟨⟨b2, midEq⟩, hb2, hme⟩ := stablePartition (lePivot pivot) a b1 lo hi ha (by rw [hb1']; exact hb)
          (by rw [hb1']; exact hbsz) hlo
        have hb2' : b2.size = b1.size := hb2
        have hme' : midEq.toNat ≤ hi.toNat - lo.toNat := hme
        have em : (lo + midEq).toNat = lo.toNat + midEq.toNat := toNat_add_of_lt _ _ (by omega)
        -- ... and has to land where the result goes
        let ⟨a1, ha1⟩ : { r : A // r.size = a.size } :=
          if toB then ⟨a, rfl⟩ else copyRange lo (lo + midEq) b2 a hasz (by rw [hb2', hb1', em]; omega) (by rw [em]; omega)
        have ha1' : a1.size = a.size := ha1
        if h : 0 < midEq.toNat then
          let ⟨(b3, a3), hb3, ha3⟩ := quicksort b2 a1 (lo + midEq) hi scratchLen limit false 0 (!toB) (by rw [hb2', hb1']; exact hb)
            (by rw [ha1']; exact ha) (by rw [hb2', hb1']; exact hbsz) (by rw [ha1']; exact hasz) (by rw [em]; omega)
          ⟨(a3, b3), ha3.trans ha1', hb3.trans (hb2'.trans hb1')⟩
        else ⟨(a1, b2), ha1', hb2'.trans hb1'⟩
      else
        if h : 0 < nl.toNat ∧ nl.toNat < len.toNat then
          have en : (lo + nl).toNat = lo.toNat + nl.toNat := toNat_add_of_lt _ _ (by omega)
          let ⟨(b2, a2), hb2, ha2⟩ := quicksort b1 a (lo + nl) hi scratchLen limit true pivot (!toB) (by rw [hb1']; exact hb) ha
            (by rw [hb1']; exact hbsz) hasz (by rw [en]; omega)
          have hb2' : b2.size = b1.size := hb2
          have ha2' : a2.size = a.size := ha2
          let ⟨(b3, a3), hb3, ha3⟩ := quicksort b2 a2 lo (lo + nl) scratchLen limit hasLA la (!toB) (by rw [hb2', hb1', en]; omega)
            (by rw [ha2', en]; omega) (by rw [hb2', hb1']; exact hbsz) (by rw [ha2']; exact hasz) (by rw [en]; omega)
          ⟨(a3, b3), ha3.trans ha2', hb3.trans (hb2'.trans hb1')⟩
        else ⟨(a, b1), rfl, hb1'⟩
termination_by hi.toNat - lo.toNat
decreasing_by all_goals (first | (simp only [em]; omega) | (simp only [en]; omega))

def stableQuicksort (v s : A) (lo hi scratchLen : UInt64) (hv : hi.toNat ≤ v.size) (hs : hi.toNat ≤ s.size)
    (hvsz : v.size < 2 ^ 64) (hssz : s.size < 2 ^ 64) (hlo : lo.toNat ≤ hi.toNat) : VS v s :=
  quicksort v s lo hi scratchLen (2 * log2U ((hi - lo) ||| 1)) false 0 false hv hs hvsz hssz hlo

def driftSortFull (v s : A) (lo hi scratchLen : UInt64) (hv : hi.toNat ≤ v.size) (hs : hi.toNat ≤ s.size)
    (hvsz : v.size < 2 ^ 64) (hssz : s.size < 2 ^ 64) (hlo : lo.toNat ≤ hi.toNat) : VS v s :=
  driftSort (fun v s lo hi hv hs hvsz hssz hlo => stableQuicksort v s lo hi scratchLen hv hs hvsz hssz hlo)
    v s lo hi scratchLen false hv hs hvsz hssz hlo

def maxLenAlwaysInsertion : UInt64 := 20

-- ANCHOR: sort
/-- driftsort for `u64`, bounds-safe. An input that is one natural run (sorted, or descending and
    reversed in place) needs no scratch buffer; everything else gets one of the same size. -/
def sort (xs : A) (hsz : xs.size < 2 ^ 62) : A :=
  let n : UInt64 := xs.size.toUInt64
  have hn : n.toNat = xs.size := by simp [n]; omega
  if h2 : n < 2 then xs
  else if n ≤ maxLenAlwaysInsertion then (insertionSortRange 0 n 0 xs (by omega) (by omega) (by simp)).1
  else
    have h2 : 2 ≤ n.toNat := by have := UInt64.not_lt.mp h2; have := UInt64.le_iff_toNat_le.mp this; simpa using this
    let ⟨(e, xs1), _, _, hxs1⟩ := findRun 0 n xs (by omega) (by omega) (by simp; omega)
    have hxs1' : xs1.size = xs.size := hxs1
    if e = n then xs1
    else
      let s := zeros xs.size
      have hs : s.size = xs.size := by simp [s]
      let eager := n ≤ smallSortThreshold * 2
      if eager then (driftSortEager xs1 s 0 n n (by omega) (by rw [hs]; omega) (by omega) (by rw [hs]; omega) (by simp)).1.1
      else (driftSortFull xs1 s 0 n n (by omega) (by rw [hs]; omega) (by omega) (by rw [hs]; omega) (by simp)).1.1
-- ANCHOR_END: sort

end DriftSort
