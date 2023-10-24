import Lean4.setm.Setm

open Mathlib.Tactic

/- set_option trace.Tactic.setm true -/
/- TODO: setm ... at ... -/

example : (4 + 0) - (3 + 1) = 0 := by
  setm ?A - ?B = (_ : Nat)
  rfl

/- example (h : (1 + 1) + (2 + 2) - (1 + 1) = 4) : true := by -/
/-   setm ?A + ?B - ?A = (_ : Nat) -/

example (h : 1 + 0 = 1) : 1 + 2 = 3 := by
  rewrite [Nat.add_zero] at h
  rfl

