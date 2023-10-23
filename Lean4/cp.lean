import Lean

open Lean Meta Elab.Tactic


example : 1 + (2 + 2) = 3 := by
  testDefEq 1 + ?A = 3
