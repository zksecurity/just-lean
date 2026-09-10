import Lake
open Lake DSL

/-- Part 1 of the tutorial as a standalone project: the list merge sort, its proof, and a `main`.
    `lake build && echo 5 3 9 1 1 7 | lake exe part1` -/
package part1

@[default_target]
lean_exe part1 where
  root := `Main
