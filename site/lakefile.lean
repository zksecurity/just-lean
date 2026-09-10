import Lake
open Lake DSL

package «just-lean-site»

require verso from git "https://github.com/leanprover/verso.git" @ "v4.33.0"
require mergesort from ".."

lean_lib JustLean

@[default_target]
lean_exe «just-lean-site» where
  root := `JustLeanMain
