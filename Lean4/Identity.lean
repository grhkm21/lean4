import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral

open scoped Interval
open Nat Rat Real Finset BigOperators MeasureTheory intervalIntegral

def H (n : ℕ) : ℚ := ∑ k in range n.succ, 1 / k

example (a : ℝ) : -a = (-1) * a := by
  rw [neg_mul, one_mul]

lemma lem1 (r : ℕ) (h : 0 < r): ∫ x in (-1 : ℝ)..0, x^(r - 1) = (-1 : ℤ)^(r - 1) / r := by
  rw [integral_rpow]
  simp [zero_pow h]
  {
    
  }
  {
    simp [h]
  }

lemma lem2 (n : ℕ) : ∑ r in range n, (-1 : ℚ)^r / r.succ * (choose n r.succ) = 1 := by
  sorry

theorem thm (n k : ℕ) (h : k ≤ n) :
  ∑ r in range (n - k), choose (r + k) k = (choose n k) * (H n - H k) := by
  sorry

#eval H 3
#eval (range 5).sum (λ i => i * 2)
#eval choose 5 3
#eval ∑ r in range (10 - 6), (choose (r + 6) 6) / (10 - (r + 6) : ℚ)
#eval (choose 10 6) * (H 10 - H 6)
