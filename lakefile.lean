import Lake
open Lake DSL

package «lean4» where
  moreServerOptions := #[⟨`autoImplicit, false⟩]

lean_lib «Lean4» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_exe «lean4» where
  root := `Main

lean_exe mk_all where
  srcDir := "scripts"
  supportInterpreter := true
  -- Executables which import `Lake` must set `-lLake`.
  weakLinkArgs := #["-lLake"]
