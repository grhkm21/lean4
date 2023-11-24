import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Basic

open Nat BigOperators Polynomial
open Finset hiding choose

lemma sum_ite_iff_eq [DecidableEq α] [AddCommMonoid β] [DecidablePred p]
    {f : α → β} {a : α} {s : Finset α} (h : ∀ x ∈ s, p x ↔ x = a) :
    (∑ x in s, if p x then f x else 0) = (if a ∈ s then f a else 0) := by
  rw [sum_congr rfl (g := fun x ↦ if x = a then f x else 0)]
  · rw [sum_ite_eq']
  · intro x hx
    simp only [h x hx]

variable {n k p : ℕ} [hp : Fact p.Prime]

theorem lucas : choose n k ≡ choose (n % p) (k % p) * choose (n / p) (k / p) [ZMOD p] := by
  have decompose : ((X : (ZMod p)[X]) + 1) ^ n = (X + 1) ^ (n % p) * (X ^ p + 1) ^ (n / p) := by
    nth_rw 1 [←mod_add_div n p, pow_add, pow_mul, add_pow_char (ZMod p)[X] (p := p), one_pow]
  simp only [←ZMod.int_cast_eq_int_cast_iff, Int.cast_mul, Int.cast_ofNat, ←coeff_X_add_one_pow _ n k]
  rw [←eq_intCast (Int.castRingHom (ZMod p)), ←coeff_map, Polynomial.map_pow, Polynomial.map_add,
    Polynomial.map_one, map_X, decompose]
  simp only [add_pow, one_pow, mul_one, ←pow_mul, sum_mul_sum]
  conv =>
    lhs ; arg 1 ; arg 2 ; ext k
    rw [←mul_assoc, mul_right_comm _ _ (X ^ (p * k.2)), ←pow_add, mul_assoc, ←cast_mul]
  rw [finset_sum_coeff]
  simp only [coeff_mul_natCast, coeff_X_pow, ite_mul, zero_mul, one_mul, ←cast_mul]
  have step2 :
      ∀ x ∈ range (n % p + 1) ×ˢ range (n / p + 1), k = x.1 + p * x.2 ↔ x = (k % p, k / p) := by
    intro ⟨x₁, x₂⟩ hx
    simp only [Prod.mk.injEq]
    constructor <;> intro h
    · simp only [mem_product, mem_range] at hx
      have h' : x₁ < p := lt_of_lt_of_le hx.left $ mod_lt _ Fin.size_pos'
      rw [h, add_mul_mod_self_left, add_mul_div_left _ _ Fin.size_pos', self_eq_add_left]
      exact ⟨(mod_eq_of_lt h').symm, div_eq_of_lt h'⟩
    · rw [h.left, h.right, mod_add_div]
  rw [sum_ite_iff_eq step2]
  simp_rw [mem_product, mem_range]
  split_ifs with h
  · rfl
  · simp only [lt_succ, not_and_or, not_le] at h
    cases' h with h h <;> simp only [choose_eq_zero_of_lt h, zero_mul, mul_zero, cast_zero]

theorem lucas' {a : ℕ} (ha₁ : n ≤ p ^ a) (ha₂ : k ≤ p ^ a) :
    (choose n k) % p = ∏ i in range a.succ, choose (n / p ^ i % p) (k / p ^ i % p) % p := by
  sorry
