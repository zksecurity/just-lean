import MergeSort.DriftSort
/-! C entry point: sort a `UInt64Array` (a `lean_sarray` of 8-byte elements) in place. -/
namespace MergeSort

-- ANCHOR: sortExport
/-- Exported symbol for other languages. The size precondition is checked at runtime. -/
@[export mergesort_sort_u64]
def sortExport (xs : UInt64Array) : UInt64Array :=
  if h : xs.size < 2 ^ 62 then DriftSort.sort xs h else xs
-- ANCHOR_END: sortExport

end MergeSort
