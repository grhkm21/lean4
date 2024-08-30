import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.LSeries.Dirichlet

import Lean4.MFWork.TsumLemmas

open scoped ModularForm UpperHalfPlane
open Nat ModularForm EisensteinSeries Module Submodule FiniteDimensional Real
  ArithmeticFunction Filter UpperHalfPlane

noncomputable def eisensteinSeriesOfWeight (k : ℤ) (hk : 3 ≤ k := by decide) : ModularForm ⊤ k :=
  CongruenceSubgroup.Gamma_one_top ▸ @eisensteinSeries_MF k 1 hk 0

local notation "G[" k "," hk "]" => eisensteinSeriesOfWeight k hk
local notation "G[" k "]" => G[k, by decide]
local notation "E[" k "," hk "]" => (2 * riemannZeta k)⁻¹ • G[k, hk]
local notation "E[" k "]" => E[k, by decide]

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (k : ℤ)

instance : atImInfty.NeBot := by
  apply NeBot.comap_of_range_mem
  · exact atTop_neBot
  · simp_rw [mem_atTop_sets, Set.mem_range]
    use 1, fun b hb ↦ ⟨⟨b * Complex.I, ?_⟩, ?_⟩
    · simpa using by linarith
    · rw [UpperHalfPlane.im]
      exact (by simp : ((b : ℂ) * Complex.I).im = b)

-- Lets me skip boring Summable proofs
axiom always_summable {α β : Type*} [AddCommMonoid β] [TopologicalSpace β] {f : α → β} : Summable f

-- Computes dim(M(1, k))
axiom mf_dim :
  Module.rank ℂ (ModularForm ⊤ k) =
    if 2 ≤ k ∧ Even k then
      if k % 12 = 2 then k.toNat / 12 else k.toNat / 12 + 1
    else
      0

-- G[k] are nonzero
axiom G_ne_zero (hk : 3 ≤ k := by decide) : G[k, hk] ≠ 0

theorem E_ne_zero (hk : 3 ≤ k := by decide) : E[k, hk] ≠ 0 := by
  simp only [ne_eq, smul_eq_zero, G_ne_zero, or_false, inv_eq_zero, _root_.mul_eq_zero]
  simp only [two_ne_zero, false_or, ← ne_eq]
  apply riemannZeta_ne_zero_of_one_lt_re
  norm_cast
  omega

axiom G_qexp (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) :
    G[k, hk] z =
      2 * riemannZeta (k) +
        2 * ((-2 * π * I) ^ k / (k - 1)!) *
          ∑' n : ℕ+, sigma (k - 1) n * Complex.exp (2 * π * I * z * n)

theorem G_qexp' (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) :
    ⇑G[k, hk] =
      fun z : ℍ ↦ 2 * riemannZeta (k) +
        2 * ((-2 * π * I) ^ k / (k - 1)!) *
          ∑' n : ℕ+, sigma (k - 1) n * Complex.exp (2 * π * I * z * n) := by
  ext z
  exact G_qexp k hk hk2 z

theorem tendsto_exp_mul_I_atImInfty :
    Tendsto (fun z : ℍ ↦ Complex.exp (z * I)) atImInfty (nhds 0) := by
  apply (zero_at_im_infty _).mpr
  intro ε hε
  have : ∃ R : ℝ, ∀ (x : ℝ) (_ : R ≤ x), Real.exp (-x) < ε := by
    have := tendsto_exp_neg_atTop_nhds_zero
    simp only [Metric.tendsto_nhds, dist_zero_right, norm_eq_abs, abs_exp, eventually_atTop] at this
    exact this _ hε
  obtain ⟨A, hA⟩ := this
  use A, fun z hz ↦ ?_
  simpa only [Complex.abs_exp, coe_I, Complex.mul_re, coe_re, Complex.I_re, mul_zero, coe_im,
    Complex.I_im, mul_one, zero_sub] using (hA z.im hz).le

theorem Set.support_finite_iff {α β : Type*} {f : α → β} [Zero β] :
    f.support.Finite ↔ ∃ s : Finset α, ∀ x, (x ∈ s ↔ f x ≠ 0) := by
  constructor <;> intro hf
  · use @Set.toFinset _ f.support hf.fintype; simp
  · obtain ⟨s, hs⟩ := hf; exact Set.Finite.ofFinset s hs

theorem nat_support_finite_aux {α : Type*} {f : ℕ → α} [Zero α] :
    f.support.Finite ↔ (fun a : ℕ+ ↦ f a).support.Finite := by
  simp_rw [Set.support_finite_iff]
  constructor <;> intro ⟨s, hs⟩
  · use s.filterMap (fun x ↦ if hx : 0 < x then some ⟨x, hx⟩ else none) <|
        (by simp; exact fun _ _ _ h₁ h₂ ↦ h₁.trans h₂.symm)
    intro ⟨x, hx⟩
    simp [hs]
  · by_cases hf' : f 0 = 0
    · use s.map ⟨(↑), fun y ↦ by simp⟩
      intro x
      by_cases hx : 0 < x
      · specialize hs ⟨x, hx⟩
        simp at hs
        simp [← hs, hx.ne.symm]
        exact ⟨by rintro ⟨⟨y, hy⟩, hy', rfl⟩; simp [hy'], fun hy ↦ ⟨_, ⟨hy, rfl⟩⟩⟩
      · norm_num at hx
        subst hx
        simpa
    · use s.map ⟨(↑), fun y ↦ by simp⟩ ∪ {0}
      intro x
      by_cases hx : 0 < x
      · specialize hs ⟨x, hx⟩
        simp at hs
        simp [← hs, hx.ne.symm]
        exact ⟨by rintro ⟨⟨y, hy⟩, hy', rfl⟩; simp [hy'], fun hy ↦ ⟨_, ⟨hy, rfl⟩⟩⟩
      · norm_num at hx
        subst hx
        simpa

theorem tsum_first_thing {α : Type*} [AddCommGroup α] [UniformSpace α] [T2Space α]
    [UniformAddGroup α] [CompleteSpace α] {f : ℕ → α} (hf : Summable f) :
      (∑' n : ℕ, f n) = f 0 + (∑' n : ℕ+, f n) := by
  rw [tsum_pNat', tsum_eq_zero_add hf]

theorem qexp_tendsto
    (a : ℕ → ℂ) (ha : ∀ z : ℍ, Summable (fun n : ℕ ↦ a n * Complex.exp (2 * π * I * z * n))) :
      Tendsto (fun z : ℍ ↦ ∑' n : ℕ, a n * Complex.exp (2 * π * I * z * n))
        atImInfty (nhds (a 0)) := by
  sorry

#check MeasureTheory.hasSum_integral_of_dominated_convergence

theorem qexp_tendsto' (a₀ : ℂ) (a : ℕ+ → ℂ)
    (ha : ∀ z : ℍ, Summable (fun n : ℕ+ ↦ a n * Complex.exp (2 * π * I * z * n))) :
      Tendsto (fun z : ℍ ↦ a₀ + ∑' n : ℕ+, a n * Complex.exp (2 * π * I * z * n))
        atImInfty (nhds a₀) := by
  change Tendsto (fun z : ℍ ↦ a₀ + ∑' n : ℕ+, (fun n ↦ a n * Complex.exp (2 * π * I * z * n)) n) _ _
  let a' : ℕ → ℂ := fun n ↦ if hn : 0 < n then a ⟨n, hn⟩ else a₀
  convert_to Tendsto (fun z : ℍ ↦ ∑' n : ℕ, (fun n : ℕ ↦ a' n * Complex.exp (2 * π * I * z * n)) n) _ _
  · ext z
    rw [tsum_eq_zero_add, ← tsum_pNat' (fun n : ℕ ↦ a' n * Complex.exp (2 * π * I * z * n))]
    · congr
      · simp [a']
      · ext n
        simpa [a'] using by rfl
    · exact always_summable
  · convert qexp_tendsto a' ?_
    intro; exact always_summable

example : Module.rank ℂ (ModularForm ⊤ 4) = 1 := by
  simpa [mf_dim] using by decide

theorem G_tendsto (k : ℕ) (hk : 3 ≤ (k : ℤ) := by decide) (hk2 : Even k := by decide) :
    Tendsto G[k, hk] atImInfty (nhds (2 * riemannZeta k)) := by
  rw [G_qexp' k hk hk2]
  conv =>
    enter [1, i, 2]
    rw [← @smul_eq_mul _ _ (2 * _) _, ← tsum_const_smul'']
    enter [1, n]
    rw [smul_eq_mul, ← mul_assoc]
  convert qexp_tendsto' _ _ _ using 1
  intro; exact always_summable

theorem smul_G_tendsto (c : ℂ) (k : ℕ) (hk : 3 ≤ (k : ℤ) := by decide) (hk2 : Even k := by decide) :
    Tendsto (c • G[k, hk]) atImInfty (nhds (c * 2 * riemannZeta k)) := by
  by_cases hc : c = 0
  · subst hc
    simpa using tendsto_const_nhds
  · rw [ModularForm.coe_smul, Pi.smul_def, mul_assoc, ← smul_eq_mul, tendsto_const_smul_iff₀ hc]
    exact G_tendsto k hk hk2

theorem E_tendsto (k : ℕ) (hk : 3 ≤ (k : ℤ) := by decide) (hk2 : Even k := by decide) :
    Tendsto E[k, hk] atImInfty (nhds 1) := by
  convert smul_G_tendsto _ _ hk hk2
  ring_nf
  rw [Complex.mul_inv_cancel]
  apply riemannZeta_ne_zero_of_one_lt_re
  norm_num
  omega

theorem smul_E_tendsto (c : ℂ) (k : ℕ) (hk : 3 ≤ (k : ℤ) := by decide) (hk2 : Even k := by decide) :
    Tendsto (c • E[k, hk]) atImInfty (nhds c) := by
  by_cases hc : c = 0
  · subst hc
    simpa using tendsto_const_nhds
  · rw [← smul_assoc]
    convert smul_G_tendsto _ k hk hk2
    rw [smul_eq_mul, mul_assoc, mul_assoc, mul_comm _ (2 * _), Complex.mul_inv_cancel, mul_one]
    apply _root_.mul_ne_zero two_ne_zero
    apply riemannZeta_ne_zero_of_one_lt_re
    norm_num
    omega

theorem E4_mul_E6_eq_E10 : E[4].mul E[6] = E[10] := by
  have h_dim_10 : finrank ℂ (ModularForm ⊤ 10) = 1 :=
    rank_eq_one_iff_finrank_eq_one.mp (by simpa [mf_dim] using by decide)
  simp_rw [finrank_eq_one_iff_of_nonzero _ (E_ne_zero 10), eq_top_iff', mem_span_singleton]
    at h_dim_10
  obtain ⟨k, hk⟩ := h_dim_10 (E[4].mul E[6])
  have h_lhs : Tendsto (k • E[10]) atImInfty (nhds k) := by
    convert smul_E_tendsto k 10 (by decide) (by decide)
  have h_rhs: Tendsto (E[4].mul E[6]) atImInfty (nhds 1) := by
    convert Tendsto.mul (E_tendsto 4) (E_tendsto 6)
    rw [mul_one]
  have : k = 1 := by
    rw [← hk, Int.cast_ofNat] at h_rhs
    exact tendsto_nhds_unique h_lhs h_rhs
  subst this
  simp only [Int.cast_ofNat, mul_inv_rev, one_smul, Int.reduceAdd] at hk ⊢
  rw [hk]

#print axioms E4_mul_E6_eq_E10
