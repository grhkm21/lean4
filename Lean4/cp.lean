import Mathlib

#check IsWellOrder
theorem nonempty_nat_set_contains_minimum {s : Set ℕ} (hs : s.Nonempty) :
    ∃ n ∈ s, ∀ m ∈ s, n ≤ m := by
  use (⊥ : s)
  simp
