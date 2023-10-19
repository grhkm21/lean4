import Mathlib.Tactic

theorem f (a b : ℕ) : a = b := sorry

example (a b : ℕ) : a + 1 = b + 1 ∧ false := by
  constructor
  simp only [show a + 1 = b + 1 by simp only [f a b]]
