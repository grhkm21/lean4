import Lake
open Lake DSL

package «lean4» {
  -- add package configuration options here
}

lean_lib «Lean4» {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_exe «lean4» {
  root := `Main
}