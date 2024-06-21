import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.SetTheory.Cardinal.SchroederBernstein
import Mathlib.Tactic

section NT1

open Nat BigOperators Finset Real ArithmeticFunction

/-
lemma moebius_rec_sum {N : ℕ} (hN : N ≠ 0) :
  ∑ (x : ℕ) in N.divisors, (μ x : ℝ) / x = ∏ p in filter nat.prime N.divisors, (1 - p⁻¹) :=
-/

/-
  Proof outline is that ∑_{x | N} μ x / x = (λ x, μ x / x) * ζ
  Where * is the Dirichlet convolution, which is multiplicative.
  We then prove the theorem for primes, for which it's easy.
-/

-- My attempt
example {n : ℕ} (hn: 0 < n) : (φ n : ℚ) / n = ∏ p in filter Nat.Prime n.divisors, (1 - (p : ℚ)⁻¹) :=
by
  revert hn
  rw [←prime_divisors_eq_to_filter_divisors_prime]
  refine recOnPosPrimePosCoprime ?_ ?_ ?_ ?_ n
  · intro p k hp hk _
    have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpk' : (p^k : ℚ) ≠ 0 := by exact_mod_cast (pow_eq_zero_iff hk).not.mpr hp.ne_zero
    -- "math part"
    rw [hp.factors_pow, List.toFinset_replicate_of_ne_zero (Nat.ne_of_gt hk), prod_singleton,
    totient_prime_pow hp hk, div_eq_iff hpk']
    -- "lean part"
    rw [cast_mul, cast_sub (by linarith [hp.two_le]), mul_sub, cast_one, mul_one, ←cast_mul]
    conv => lhs; lhs; rhs; rhs; rw [←pow_one p]
    rw [←pow_add, Nat.sub_add_cancel hk, sub_mul, one_mul, sub_right_inj, mul_comm, inv_eq_one_div,
    ←mul_div_assoc, mul_one]
    apply Eq.symm
    rw [div_eq_iff hp']
    conv => rhs; rhs; rhs; rw [←pow_one p]
    norm_cast
    rw [←pow_add, Nat.sub_add_cancel hk]
  · simp
  · simp
  · intro m n hm hn hmn Pm Pn _
    specialize Pm (zero_lt_one.trans hm)
    specialize Pn (zero_lt_one.trans hn)
    rw [Nat.factors_mul_toFinset_of_coprime hmn, prod_union, ← Pm, ← Pn, totient_mul hmn]
    field_simp
    rw [List.disjoint_toFinset_iff_disjoint]
    exact Nat.coprime_factors_disjoint hmn

-- ericrbg
example {p k : ℕ} (hp : Nat.Prime p) (hk : 0 < k) :
  ↑(φ (p ^ k)) / ↑(p ^ k) = ∏ p in filter Nat.Prime (p ^ k).divisors, (1 - (p : ℚ)⁻¹) :=
by
  have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpk' : (p^k : ℚ) ≠ 0 := by exact_mod_cast (pow_eq_zero_iff hk).not.mpr hp.ne_zero
  have := one_le_two.trans hp.two_le
  rw [← prime_divisors_eq_to_filter_divisors_prime, hp.factors_pow,
  List.toFinset_replicate_of_ne_zero hk.ne', prod_singleton, totient_prime_pow hp hk]
  rw [mul_tsub, cast_sub <| mul_le_mul_left _ this, ←_root_.pow_succ',
      tsub_add_cancel_of_le <| succ_le.mpr hk, sub_div, div_self hpk']
  rw [mul_one, cast_pow, cast_pow, sub_right_inj, ←mul_eq_one_iff_eq_inv₀ hp']
  rw [mul_comm, mul_div, ←_root_.pow_succ, tsub_add_cancel_of_le <| succ_le.mpr hk, div_self]
  exact pow_ne_zero _ hp'

lemma moebius_rec_sum {N : ℕ} (hN : N ≠ 0) :
  ∑ x in N.divisors, (μ x : ℝ) / x = ∏ p in filter Nat.Prime N.divisors, (1 - (p : ℝ)⁻¹) :=
by
  let f' : ArithmeticFunction ℝ := ⟨fun x => (μ x : ℝ) / x, by simp⟩
  have hf': f'.IsMultiplicative := by sorry
  let f : ArithmeticFunction ℝ := f' * ζ
  have hf : f.IsMultiplicative := by sorry
  -- Rewrite LHS using f'
  change ∑ x in N.divisors, f' x = _
  rw [←coe_mul_zeta_apply]
  change f N = _
  -- Manipulate RHS
  rw [←prime_divisors_eq_to_filter_divisors_prime]
  -- Now we have (multiplicative function) N = _
  -- We separate this into prime powers and prove each
  revert hN
  refine recOnPosPrimePosCoprime ?_ ?_ ?_ ?_ N
  · sorry
  · intro _; contradiction
  · intro _; rw [hf.left]; rfl
  · intro m n hm hn hmn Pm Pn _
    specialize Pm (by linarith)
    specialize Pn (by linarith)
    rw [hf.right hmn, factors_mul_toFinset_of_coprime hmn, prod_union _, Pm, Pn]
    exact factorization_disjoint_of_coprime hmn

end NT1

-----------------------------

section NT2

open Nat Real Asymptotics Filter BigOperators Set Finset

set_option pp.rawOnError true

-- This is to fix a bug in v4.2.0-rc1
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

example {x : ℝ} : x ^ 2 - x = x * (x - 1) := by
  rw [mul_sub, ←pow_two, mul_one]

-- Proving x = O(x^2), meaning that *eventually* x <= cx^2 (c = 1 works)
example : (fun x : ℝ => x) =O[atTop] (fun x => x ^ 2) := by
  have : ∀ x : ℝ, 1 ≤ x → x ≤ x ^ 2 := by
    intro x hx
    rw [←sub_nonneg, show x ^ 2 - x = x * (x - 1) by rw [mul_sub, ←pow_two, mul_one]]
    refine mul_nonneg (by linarith) (by linarith)
  apply IsBigO.of_bound'
  rw [eventually_atTop]
  use 1
  intro b hb
  simp_rw [norm_of_nonneg (sq_nonneg _), norm_of_nonneg (zero_le_one.trans hb), this b hb]

noncomputable
def summatory (a : ℕ → M) (k : ℕ) (x : ℝ) [AddCommMonoid M] : M := ∑ n in Icc k ⌊x⌋₊, a n

-- partial summation (Theorem 1.3.1, modified)
/- theorem partial_summation {𝕜 : Type*} [IsROrC 𝕜] (c : ℕ → 𝕜) (f f' : ℝ → 𝕜) (n₀ : ℕ) (X : ℝ) -/
/-   (hf : ∀ x ∈ Ici (n₀ : ℝ), HasDerivAt f (f' x) x) -/
/-   (hf' : ContinuousOn f' (Ici ↑n₀)) : -/
/-   -- Why doesn't this require the integrated function (e.g. f') to be integrable? -/
/-   summatory (fun n => c n * f n) n₀ X = -/
/-     (summatory c n₀ X) * f X - ∫ t in Icc ↑n₀ X, (summatory c n₀ t) * f' t := -/
/- by -/
/-   sorry -/
/-  -/
/- lemma sum_one (X : ℝ) : summatory (fun _ => 1 : ℕ → ℝ) 1 X = ⌊X⌋₊ := by -/
/-   rw [summatory, sum_const, card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one] -/
/-  -/
/- lemma sum_log (X : ℝ) : -/
/-   summatory (fun x => Real.log x) 1 X = ⌊X⌋₊ * log X - ∫ t in Icc 1 X, ⌊t⌋₊ / t := -/
/- by -/
/-   set c : ℕ → ℝ := fun x => 1 with hc -/
/-   let f : ℝ → ℝ := fun x => log x -/
/-   let f' : ℝ → ℝ := fun x => 1 / x -/
/-   have hf : ∀ x ∈ Ici (1 : ℝ), HasDerivAt f (f' x) x := sorry -/
/-   have hf' : ContinuousOn f' (Ici 1) := sorry -/
/-   have hs := @partial_summation _ _ c f f' 1 X (by exact_mod_cast hf) (by exact_mod_cast hf') -/
/-   simp_rw [show (fun n => c n * f ↑n) = (fun n : ℕ => f ↑n) by simp, cast_one, sum_one] at hs -/
/-   conv => rhs ; rhs ; rhs ; ext; rw [div_eq_mul_one_div] -/
/-   exact hs -/

/- example : True := by -/
/-   let f : ℕ → ℕ := fun x => x -/
/-   let g : (ℕ → ℕ) → (ℕ → ℕ) := fun y => (fun x => Nat.floor ((cos (sin ↑x)) ^ 2 / 5)) -- complicated things -/
/-   have h : g (fun x => 2 * f x) = g (fun x => x * 2) + g (fun _ => 0) := by -/
/-     dsimp only -/

/-
-- Proposition 1.3.2
lemma sum_log_asymptotic : (fun X => (summatory (fun x => Real.log x) 1 X - (X * log X - X))) =O[atTop] log := by
  let c : ℕ → 𝕜 := fun n => if n = 0 then 0 else 1
  have hc : ∀ j < 1, c j = 0 := by intro j ; by_cases j = 0 <;> simp [*]
  have hf : ∀ x ∈ Icc 1 X, HasDerivAt f 
  /- have hf : ∀ x ∈ Icc ↑1 -/

-- log n!
theorem log_factorial_asymptotic :
  (fun x : ℝ => (∑ k in Icc 1 ⌊x⌋₊, log (k : ℝ)) - (x * log x - x)) =O[atTop] log :=
by
  sorry

-- Stating that sum(log p / p, p ≤ n) = log n + O(1)
theorem one_four_three :
  (fun x : ℝ => ∑ p in (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, log (p : ℝ) / p - log x) =O[atTop] (fun _ => (1 : ℝ)) :=
by
  sorry
-/

end NT2

-----------------------

section RD

open Set Function List Embedding

variable {α : Type*} [Finite α]

theorem injective_map_thing {s t : List ℤ} (f : ℤ → α) (hf : Injective f) :
  (map f s = map f t) ↔ (s = t) := (map_injective_iff.mpr hf).eq_iff

variable {f g}
#check @schroeder_bernstein _ _ f g

#check surjOn_iff_exists_map_subtype

theorem special_case {f : α → β} {s : Set α} {t : Set β}
  (h : ∃ g : s → t, Surjective g ∧ ∀ x : s, f x = g x) :
    SurjOn f s t :=
by
  apply surjOn_iff_exists_map_subtype.mpr
  let ⟨g, hg⟩ := h
  use t
  use g

example {k : ℕ} : ∃ n : ℕ, ∃ f : List α → List (Fin n),
  BijOn f {l : List α | l.length = k} {l : List (Fin n) | l.length = k} :=
by
  let ⟨n, hα⟩ := Finite.exists_equiv_fin α
  use n
  let f : α ≃ Fin n := Classical.choice hα
  use List.map f
  have := f.bijective
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [mem_setOf_eq, length_map, cast mem_setOf_eq hx]
  · intro x hx y hy hxy
    exact map_injective_iff.mpr (f.injective) hxy
  · apply special_case
    

example {n : ℕ} : {l : List α | l.length ≤ n}.Finite := by
  let Sk (k : Fin n) : Set (List α) := {l : List α | l.length = k}
  have h1 : {l : List α | l.length ≤ n} = ⋃ (k : Fin n), Sk k := by sorry
  have h2 : ∀ k, (Sk k).Finite := by
    intro k
    dsimp
    done
  rw [h1]
  exact Set.finite_iUnion h2

end RD
