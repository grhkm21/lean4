import Mathlib.Tactic

open Nat Set Polynomial FiniteField

-- What is the degree of x^q - x over F_q?
variable (F : Type*) [Fintype F] [Field F] (q : ℕ) [hq : Fact (IsPrimePow q)]

example : degree (X ^ q - X : F[X]) = q := by
  rw [degree_sub_eq_left_of_degree_lt, degree_X_pow]
  rw [degree_X_pow, degree_X, one_lt_cast]
  exact hq.out.one_lt


