import Lean4.setm.Setm
import Mathlib.Tactic

/- TODO: setm ... at ... -/

example : 4 * 2 = 8 := by
  setm ?A * ?B = (_ : Nat)
  unfold_let A B at *
  clear A B hA hB
  change 4 + 4 = 8
  setm ?A + ?B = (_ : Nat)
  rfl

example (h : 1 + 0 = 1) : 1 + 2 = 3 := by
  rewrite [Nat.add_zero] at h
  rfl

