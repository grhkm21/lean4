import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Intervals
import Mathlib.Data.Nat.Interval
import Mathlib.Data.Nat.Prime
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Order.LocallyFinite

open Nat Finset BigOperators ArithmeticFunction

variable (z x n : ℕ)

def smooth : Prop := ∀ p, p.Prime ∧ p < z → ¬p ∣ x

instance : ∀ z, DecidablePred (smooth z) :=
  fun z n ↦ decidable_of_iff (∀ p : ℕ, p < z → p.Prime → ¬p ∣ n)
    ⟨fun h p ⟨hp, hz⟩ ↦ h p hz hp, fun h p hz hp ↦ h p ⟨hp, hz⟩⟩

def prime_Icc (a b : ℕ) := (Icc a b).filter Nat.Prime

def prime_Ico (a b : ℕ) := (Ico a b).filter Nat.Prime

/- Number of remaining numbers ≤ x after sieving < z -/
def Φ := ((Icc 1 x).filter (smooth z)).card

/- Primorial of primes < z -/
def Pr : ℕ := ((Ico 1 z).filter Nat.Prime).prod _root_.id

/- You might want to induction -/
lemma prime_dvd_Pr_iff (hd : d.Prime) : d ∣ Pr z ↔ d ∈ Ico 1 z := by
  sorry

/- Factors of Pr z -/
lemma factors_Pr : (Pr z).factors = (List.Ico 1 z).filter Nat.Prime := by
  sorry

/- Prime divisors of Pr z -/
lemma prime_divisors_Pr : (Pr z).factors.toFinset = (Ico 1 z).filter Nat.Prime := by
  sorry

/- Taking gcd with Pr z works as a sieve -/
lemma gcd_Pr_ne_one_iff : n.gcd (Pr z) = 1 ↔ smooth z n := by
  sorry

/- Intuitively this follows from definition -/
example : Φ z x = ∑ n in Icc 1 x, if n.gcd (Pr z) = 1 then 1 else 0 := by
  rw [Φ, sum_boole]
  congr
  ext t
  exact (gcd_Pr_ne_one_iff _ _).symm

/- Basic mobius inversion manipulation -/
example : Φ x z = ∑ d in (Pr z).divisors, (x / d) * μ d := by
  sorry

