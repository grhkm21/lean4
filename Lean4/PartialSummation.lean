import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Measure.AEDisjoint
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.FundThmCalculus

open Nat Set Real BigOperators MeasureTheory Filter

variable {M : Type*} [AddCommMonoid M] (a : ℕ → M)

noncomputable def summatory (a : ℕ → M) (k : ℕ) (x : ℝ) : M :=
  ∑ n in Finset.Icc k ⌊x⌋₊, a n

lemma summatory_nat (k n : ℕ) :
  summatory a k n = ∑ n in Finset.Icc k n, a n :=
by
  simp only [summatory, floor_coe n]

lemma summatory_eq_floor {k : ℕ} (x : ℝ) :
  summatory a k x = summatory a k ⌊x⌋₊ :=
by
  rw [summatory, summatory, floor_coe]

lemma summatory_eq_of_Ico {n k : ℕ} {x : ℝ}
  (hx : x ∈ Ico (n : ℝ) (n + 1)) :
  summatory a k x = summatory a k n :=
by
  rw [summatory_eq_floor, floor_eq_on_Ico' _ _ hx]

lemma summatory_succ (k n : ℕ) (hk : k ≤ n + 1) :
  summatory a k (n + 1) = a (n + 1) + summatory a k n :=
by
  rw [summatory_nat, ←cast_add_one, summatory_nat, ←Ico_succ_right, @add_comm M,
  Finset.sum_Ico_succ_top hk, Ico_succ_right]

variable {M : Type*} (a : ℕ → M)

@[measurability] lemma measurable_summatory [AddCommMonoid M] [MeasurableSpace M] {k : ℕ} :
  Measurable (summatory a k) :=
by
  change Measurable ((fun y => ∑ i in Finset.Icc k y, a i) ∘ _)
  exact measurable_from_nat.comp measurable_floor


lemma abs_summatory_le_sum [h : SeminormedAddCommGroup M] (a : ℕ → M) {k : ℕ} {x : ℝ} :
  ‖summatory a k x‖ ≤ ∑ i in Finset.Icc k ⌊x⌋₊, ‖a i‖ :=
by
  rw [summatory]
  exact @norm_sum_le _ _ h _ _

lemma abs_summatory_bound [h : SeminormedAddCommGroup M] (k z : ℕ)
  {x : ℝ} (hx : x ≤ z) : ‖summatory a k x‖ ≤ ∑ i in Finset.Icc k z, ‖a i‖ :=
(abs_summatory_le_sum a).trans
  (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc le_rfl (floor_le_of_le hx)) (by simp))

lemma partial_summation_integrable {𝕜 : Type*} [IsROrC 𝕜] (a : ℕ → 𝕜) {f : ℝ → 𝕜} {x y : ℝ}
  {k : ℕ} (hf' : IntegrableOn f (Icc x y)) :
  IntegrableOn (summatory a k * f) (Icc x y) :=
by
  let b := ∑ i in Finset.Icc k ⌈y⌉₊, norm (a i)
  /- have : IntegrableOn (b • f) (Icc x y) := integrable.smul b hf' -/
  have : IntegrableOn (b • f) (Icc x y) := by exact Integrable.smul b hf'
  /- refine this.integrable.mono (measurable_summatory.ae_strongly_measurable.mul hf'.1) _? -/
  refine this.integrable.mono ?_ ?_
  · exact AEStronglyMeasurable.mul (measurable_summatory a).aestronglyMeasurable hf'.1
  /- rw [ae_restrict_iff' (measurable_set_Icc : measurable_set (Icc x _))] -/
  · rw [ae_restrict_iff' (measurableSet_Icc : MeasurableSet (Icc x _))]
  /- refine eventually_of_forall (fun z hz ↦ _) -/
    refine eventually_of_forall (fun z hz ↦ ?_)
  /- rw [pi.mul_apply, norm_mul, pi.smul_apply, norm_smul] -/
    rw [Pi.mul_apply, norm_mul, Pi.smul_apply, norm_smul]
  /- refine mul_le_mul_of_nonneg_right ((abs_summatory_bound _ _ ⌈y⌉₊ _).trans _) (norm_nonneg _) -/
    refine mul_le_mul_of_nonneg_right ((abs_summatory_bound _ _ ⌈y⌉₊ ?_).trans ?_) (norm_nonneg _)
  /- { exact hz.2.trans (nat.le_ceil y) } -/
    · exact hz.2.trans (le_ceil y)
  /- rw [norm_eq_abs] -/
    · rw [norm_eq_abs]
      exact le_abs_self b
  /- exact le_abs_self b -/

lemma myLemma {a b : ℝ} (h : x ∈ uIcc a b) (h' : a ≤ b) : a ≤ x ∧ x ≤ b := by
  cases' mem_uIcc.mp h with hx hx
  · exact hx
  · by_cases h'' : a = b
    · rwa [h''] at hx ⊢
    · replace h' := lt_of_le_of_ne h' h''
      linarith [h'']

theorem partial_summation_nat {𝕜 : Type*} [IsROrC 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
  {k : ℕ} {N : ℕ} (hN : k ≤ N)
  (hf : ∀ i ∈ Icc (k : ℝ) N, HasDerivAt f (f' i) i)
  (hf' : IntegrableOn f' (Icc k N)):
  ∑ n in Finset.Icc k N, a n * f n =
    summatory a k N * f N - ∫ t in Icc (k : ℝ) N, summatory a k t * f' t :=
by
  /- rw ←nat.Ico_succ_right, -/
  rw [←Nat.Ico_succ_right]
  /- revert hf hf', -/
  revert hf hf'
  /- refine nat.le_induction _ _ _ hN, -/
  refine le_induction ?_ ?_ N hN
  /- { simp }, -/
  · intro _ _
    simp [summatory_nat]
  /- intros N hN' ih hf hf', -/
  · intro N hN₁ ih hf hf'
  /- have hN'' : (N:ℝ) ≤ N + 1 := by simp only [zero_le_one, le_add_iff_nonneg_right], -/
    have hN₂ : (N : ℝ) ≤ N + 1 := le_of_lt $ lt_add_one _
  /- have : Icc (k:ℝ) (N+1) = Icc k N ∪ Icc N (N+1), -/
  /- { refine (Icc_union_Icc_eq_Icc _ hN'').symm, -/
  /-   rwa nat.cast_le }, -/
    have : Icc (k : ℝ) (N + 1) = Icc (k : ℝ) N ∪ Icc N (N + 1) :=
      (Icc_union_Icc_eq_Icc (cast_le.mpr hN₁) hN₂).symm
  /- simp only [nat.cast_succ, this, mem_union_eq, or_imp_distrib, forall_and_distrib, -/
  /-   integrable_on_union] at ih hf hf' ⊢, -/
    simp [this, or_imp, forall_and] at ih hf hf' ⊢
  /- replace ih := ih hf.1 hf'.1, -/
    replace ih := ih hf.1 hf'.1
  /- have hN''' := hN'.trans le_self_add, -/
    have hN₃ := hN₁.trans (@le_self_add _ _ _ 1)
  /-
  rw [finset.sum_Ico_succ_top hN''', ih, summatory_succ _ _ _ hN''', add_mul, add_sub_assoc,
    add_comm, nat.cast_add_one, add_right_inj, eq_comm, sub_eq_sub_iff_sub_eq_sub, ←mul_sub,
    integral_union_ae, add_sub_cancel',
    ←set_integral_congr_set_ae (Ico_ae_eq_Icc' volume_singleton)],
  -/
    rw [Finset.sum_Ico_succ_top hN₃, ih, summatory_succ _ _ _ hN₃, add_mul, add_sub_assoc,
         add_comm, cast_add_one, add_right_inj, eq_comm, sub_eq_sub_iff_sub_eq_sub, ←mul_sub,
         integral_union_ae, add_sub_cancel',
         ←set_integral_congr_set_ae (Ico_ae_eq_Icc' volume_singleton)]
  /- rotate, -- the first goal is the only hard one -/
    rotate_left
  /- { rw [ae_disjoint, Icc_inter_Icc_eq_singleton _ hN'', volume_singleton], -/
  /-   rwa nat.cast_le }, -/
    · rw [AEDisjoint, Icc_inter_Icc_eq_singleton _ hN₂, volume_singleton]
      rwa [cast_le]
  /- { exact measurable_set_Icc.null_measurable_set }, -/
    · exact measurableSet_Icc.nullMeasurableSet
  /- { exact partial_summation_integrable a hf'.1 }, -/
    · exact partial_summation_integrable a hf'.left
  /- { exact partial_summation_integrable a hf'.2 }, -/
    · exact partial_summation_integrable a hf'.right
  /- have : eq_on (λ x, summatory a k x * f' x) (λ x, summatory a k N • f' x) (Ico N (N+1)) := -/
  /-     λ x hx, congr_arg2 (*) (summatory_eq_of_Ico _ hx) rfl, -/
    · have : EqOn (fun x => summatory a k x * f' x)
        (fun x => summatory a k N • f' x) (Ico N (N + 1)) :=
      by
        intro x hx
        /- fun x hx => congr_arg2 (*) (summatory_eq_of_Ico _ hx) rfl -/
        apply congr_arg₂
        · apply summatory_eq_of_Ico _ hx
        · rfl
  /- rw [set_integral_congr measurable_set_Ico this, integral_smul, algebra.id.smul_eq_mul, -/
  /-     set_integral_congr_set_ae (Ico_ae_eq_Ioc' volume_singleton volume_singleton), -/
  /-     ←interval_integral.integral_of_le hN'', interval_integral.integral_eq_sub_of_has_deriv_at], -/
      rw [set_integral_congr measurableSet_Ico this, integral_smul, Algebra.id.smul_eq_mul,
          set_integral_congr_set_ae (Ico_ae_eq_Ioc' volume_singleton volume_singleton),
          ←intervalIntegral.integral_of_le hN₂, intervalIntegral.integral_eq_sub_of_hasDerivAt]
  /- { rw interval_of_le hN'', exact hf.2 }, -/
      · intro x hx
        replace hx := myLemma hx hN₂
        apply hf.right <;> linarith
  /- { exact (interval_integrable_iff_integrable_Icc_of_le hN'').2 hf'.2 }, -/
      · exact (intervalIntegrable_iff_integrable_Icc_of_le hN₂).mpr hf'.right

