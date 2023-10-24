import Lean

open Lean

/-
instance : BEq MVarId := Lean.instBEqMVarId
instance : Hashable MVarId := Lean.instHashableMVarId
-/

elab "asdf" : tactic => do
  let xs ← [1, 2, 3, 4, 5].mapM (fun _ ↦ mkFreshMVarId)
  let f := fun x ↦ return (x, ←mkFreshMVarId)
  let ys ← xs.mapM f
  /-
  let mp1 := HashMap.ofList ys
  Error: don't know how to synthesize implicit argument
    ⊢ BEq MVarId
    ⊢ Hashable MVarId
  -/
  let mp2 := @HashMap.ofList _ _ Lean.instBEqMVarId Lean.instHashableMVarId ys
  logInfo m!"{repr ys}"
  logInfo m!"{repr $ mp2.find! xs[0]!}"

example : true := by asdf

