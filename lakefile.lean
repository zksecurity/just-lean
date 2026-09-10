import Lake
open Lake DSL

package mergesort

/-- The verified sorts (Parts 1 to 3 of the tutorial). -/
@[default_target]
lean_lib MergeSort where
  defaultFacets := #[LeanLib.leanArtsFacet, LeanLib.staticFacet, LeanLib.sharedFacet]

/-- Unverified lab code: the line-by-line port of Rust's driftsort used for comparison. -/
lean_lib Lab where
  srcDir := "lab"
  roots := #[`Drift]

lean_exe sortdemo where
  root := `Main

lean_exe msbench where
  root := `Bench

lean_exe driftbench where
  root := `DriftBench

lean_exe verifyall where
  root := `VerifyAll

lean_exe listbench where
  root := `ListBench
