import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Data.Real.Basic

open scoped Real
open Complex Function Metric MeasureTheory intervalIntegral IntervalIntegrable Filter

local notation "e " x:100 => exp (2 * π * I * x)

theorem integral_exp_mul {a b : ℝ} {c : ℝ} (hc : c ≠ 0) :
    (∫ x in a..b, rexp (c * x)) = (rexp (c * b) - rexp (c * a)) / c := by
  have := @integral_exp_mul_complex a b c (by norm_cast)
  norm_cast at this
  rw [intervalIntegral.integral_ofReal] at this
  norm_cast at this

@[simp] theorem Complex.exp_mul_int (z : ℂ) (n : ℤ) : cexp (z * n) = cexp z ^ n :=
  mul_comm (n : ℂ) z ▸ exp_int_mul z n

lemma integral_aux {a : ℤ} : ∫ y in (0 : ℝ)..1, e (a * y) = if a = 0 then 1 else 0 := by
  split_ifs with ha
  · subst ha; simp
  · have : 2 * π * I * a ≠ 0 := by simp [ha, Real.pi_ne_zero]
    simp_rw [mul_assoc, ← mul_assoc I, ← mul_assoc (π : ℂ), ← mul_assoc]
    simp [integral_exp_mul_complex this, Complex.exp_mul_I]

/- Hua's Lemma for j = 0 (Vaughan, "trivial") -/
lemma hua0 (N : ℤ) : ∫ y in (0 : ℝ)..1, (∑ m in Finset.Icc 1 N, e (m * y)) = 0 := by
  rw [intervalIntegral.integral_finset_sum]
  · (conv_lhs => enter [2, i]; rw [integral_aux]); simp
  · intros; exact Continuous.intervalIntegrable (by continuity) ..

/- Hua's Lemma for j = 1 (Vaughan, "trivial") -/
lemma hua1 (k : ℕ) :
    (fun N : ℕ ↦ ∫ y in (0 : ℝ)..1, (∑ m in Finset.Icc 1 N, e (m ^ k * y)) ^ 2)
      =O[atTop] (fun N ↦ (0 : ℝ)) := by
  rw [intervalIntegral.integral_finset_sum]
  · (conv_lhs => enter [2, i]; rw [integral_aux]); simp
  · intros; exact Continuous.intervalIntegrable (by continuity) ..

/- lemma hua_1 (k : ℕ) : ∫ y in (0 : ℝ)..1, (∑  -/
