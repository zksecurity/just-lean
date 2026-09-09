#!/bin/sh
# Build everything, run the exact cross-check, print the axioms of every theorem, and benchmark.
set -e
cd "$(dirname "$0")"
lake build
lake build msbench verifyall naturalruns
./.lake/build/bin/verifyall
cat > /tmp/mergesort_axioms.lean <<'LEAN'
import MergeSort
#print axioms MergeSort.mergeSort_correct
#print axioms MergeSort.Fast.sort_toList
#print axioms MergeSort.Fast.sort_sorted
#print axioms MergeSort.Fast.sort_perm
#print axioms MergeSort.BottomUp.sort_sorted
#print axioms MergeSort.BottomUp.sort_perm
#print axioms MergeSort.BottomUp.sort16_sorted
#print axioms MergeSort.BottomUp.sort16_perm
#print axioms MergeSort.BottomUp.sort2_sorted
#print axioms MergeSort.BottomUp.sort2_perm
#print axioms MergeSort.BottomUp.sortBlocked_sorted
#print axioms MergeSort.BottomUp.sortBlocked_perm
#print axioms MergeSort.BottomUp.sortAdaptive_sorted
#print axioms MergeSort.BottomUp.sortAdaptive_perm
#print axioms MergeSort.BottomUp.sortAdaptive2_sorted
#print axioms MergeSort.BottomUp.sortAdaptive2_perm
#print axioms MergeSort.BottomUp.sortAdaptive3_sorted
#print axioms MergeSort.BottomUp.sortAdaptive3_perm
#print axioms MergeSort.BottomUp.mergeKernelS_spec
#print axioms MergeSort.BottomUp.findRun_spec
#print axioms MergeSort.BottomUp.net4_sorted
#print axioms MergeSort.BottomUp.net4_perm
LEAN
lake env lean /tmp/mergesort_axioms.lean
grep -rn "sorry" MergeSort/ MergeSort.lean && { echo "sorry found in the library"; exit 1; } || echo "no sorry in the library"
./.lake/build/bin/naturalruns verify
./.lake/build/bin/msbench "${1:-1000000}"
