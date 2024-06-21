import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Algebra.Periodic
import Mathlib.Analysis.Calculus.FDeriv.Basic

-- Section 8.1 of Cojocaru & Murty, The large sieve inequality

open Int Finset Function MeasureTheory intervalIntegral

example {z : ℤ} (hz : 0 < z) :
    ∑ d ∈ Icc 1 z, 1 = z := by
  rw [sum_const, nsmul_one, card_Icc, add_sub_cancel_right, toNat_of_nonneg (by omega)]

example {z : ℕ} :
    ∑ d ∈ Icc 1 z, ∑ a ∈ (Ico 0 d).filter d.Coprime, 1 = ∑ d ∈ Icc 1 z, Nat.totient d := by
  apply sum_congr rfl
  intro x _
  rw [Nat.totient, sum_const, nsmul_one, Nat.cast_id]
  congr
  ext t; simp

#check HasFDerivAt
example {F : ℝ → ℂ} {F' : ℝ →L[ℝ] ℂ} (hF : Periodic F 1) (hF_diff : ∀ x, HasFDerivAt F F' x) {z : ℕ} :
    ∑ d ∈ Icc 1 z, (∑ a ∈ (Ico 0 d).filter d.Coprime, ‖F ((a : ℝ) / d)‖)
      ≤ z ^ 2 * ∫ α in (0 : ℝ)..1, ‖F α‖ + ∫ α in (0 : ℝ)..1, ‖F' α‖ := by
  sorry

-- Lemma 8.1.1
