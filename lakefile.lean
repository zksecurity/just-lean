import Lake
open Lake DSL
package mergesort
@[default_target]
lean_lib MergeSort where
  defaultFacets := #[LeanLib.leanArtsFacet, LeanLib.staticFacet, LeanLib.sharedFacet]
lean_exe msbench where
  root := `Bench
lean_exe dobench where
  root := `DoBench
lean_exe verifyall where
  root := `VerifyAll
lean_exe experiments where
  root := `Experiments
lean_exe doloop where
  root := `DoLoop
lean_exe sortdemo where
  root := `Main

lean_exe naturalruns where
  root := `NaturalRuns

lean_exe genericbench where
  root := `GenericBench
