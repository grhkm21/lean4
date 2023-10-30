import Mathlib.Tactic
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real BigOperators

example : 0 ≤ ∑ x in Finset.Icc (1 : ℕ) 6, x * (log (x + 1) - log x) - 7 + log 7 := by
  have : Finset.Icc (1 : ℕ) 6 = {1, 2, 3, 4, 5, 6} := by rfl
  simp [this]
  ring_nf
  rw [add_sub, add_sub]
  repeat rw [←sub_eq_add_neg]
  iterate 4 rw [sub_sub, ←log_mul]
  nth_rw 3 [show (7 : ℝ) = (7 : ℕ) by rfl]
  rw [mul_comm (log _) _, add_comm_sub, ←log_pow, ←log_div]
  all_goals try norm_num
  rw [le_log_iff_exp_le]
  /- annoying issue: There's both (a : ℝ) ^ (b : ℕ) and (a : ℝ) ^ (b : ℝ) -/
  let h := @rpow_le_rpow _ _ (7 : ℕ) ?_ (tsub_le_iff_left.mp $ (abs_le.mp exp_one_near_10).right) ?_
  rw [exp_one_rpow, rpow_nat_cast] at h
  apply h.trans
  all_goals norm_num
  exact le_of_lt $ exp_pos 1

example {a b : ℝ} : a - b = a + (-b) := by
  change _ = _ - _
