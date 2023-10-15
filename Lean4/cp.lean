import Mathlib.Tactic

open Nat

example {m n : ℕ} (h : n ≠ 0) : ∃ m : ℕ, n = m.succ := exists_eq_succ_of_ne_zero h

example {a b : ℕ} : a < b ∨ a = b ∨ a > b := Nat.lt_trichotomy a b
example {a b : ℕ} : a ≤ b ∨ b ≤ a := Nat.le_or_le a b
example : False → P := by exact?
example {a : ℕ} : a ≤ succ a := by exact?
example (h : succ a ≤ succ b) : a ≤ b := by exact?
example (h : ¬P ∨ Q) (h' : P) : Q := by exact?
example (h : ¬P ∨ Q) (h' : P) : Q := imp_iff_not_or.mpr h h'
