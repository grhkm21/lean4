import Mathlib.Tactic

open Nat

theorem thm1 (h : a * b = c) (h' : c ≠ 0) : a ≠ 0 ∧ b ≠ 0 := by
  subst c
  exact Nat.mul_ne_zero_iff.mp h'

theorem thm2 (h : a * b = c) (h' : c ≠ 0) : a ≤ c := by
  subst c
  apply?

theorem thm3 (h : a * b = c) (h' : c ≠ 0) : a ≤ c ∧ b ≤ c :=
  ⟨thm2 h h', thm2 (Nat.mul_comm _ _ ▸ h) h'⟩

def OurPrime (n : ℕ) : Prop := 2 ≤ n ∧ ∀ k, k ∣ n → k = 1 ∨ k = n
example (h : 1 < c) (hc : ¬OurPrime c) : ∃ a b, c = a * b ∧ 1 < a ∧ a < c ∧ 1 < b ∧ b < c := by
  rw [OurPrime] at hc
  push_neg at hc
  let ⟨k, ⟨⟨k', hk'⟩, hk, h''⟩⟩ := hc h
  have hk' := hk'.symm
  have hk1 : k ≠ 0 := fun ha => not_eq_zero_of_lt h $ (mul_eq_zero_of_left ha k' ▸ hk').symm
  have ⟨hk2, hk3⟩ := thm3 hk' $ not_eq_zero_of_lt h
  have hk4 : k' ≠ c := fun hkc => hk $ (mul_eq_right₀ $ not_eq_zero_of_lt h).mp $ hkc ▸ hk'
  refine ⟨k, k', ⟨hk'.symm, ?_, lt_of_le_of_ne hk2 h'', ?_, lt_of_le_of_ne hk3 hk4⟩⟩
  · iterate 2 cases' k with k <;> try trivial
    linarith
  · iterate 2 cases' k' with k' <;> try simp [←one_eq_succ_zero, h''] at hk' <;> try linarith
    linarith

