import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Measure.AEDisjoint
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Tactic
import Lean4.setm.Setm

open Nat Set Real BigOperators MeasureTheory Filter

variable {M : Type*} [AddCommMonoid M] (a : ℕ → M)

/-- sum of a n for k ≤ n ≤ x -/
noncomputable def summatory (a : ℕ → M) (k : ℕ) (x : ℝ) : M :=
  ∑ n in Finset.Icc k ⌊x⌋₊, a n

lemma summatory_nat (k n : ℕ) :
    summatory a k n = ∑ n in Finset.Icc k n, a n := by
  simp only [summatory, floor_coe n]

lemma summatory_eq_floor {k : ℕ} (x : ℝ) :
    summatory a k x = summatory a k ⌊x⌋₊ := by
  rw [summatory, summatory, floor_coe]

lemma summatory_eq_of_Ico {n k : ℕ} {x : ℝ}
    (hx : x ∈ Ico (n : ℝ) (n + 1)) :
    summatory a k x = summatory a k n := by
  rw [summatory_eq_floor, floor_eq_on_Ico' _ _ hx]

lemma summatory_succ (k n : ℕ) (hk : k ≤ n + 1) :
    summatory a k (n + 1) = a (n + 1) + summatory a k n := by
  rw [summatory_nat, ←cast_add_one, summatory_nat, ←Ico_succ_right, @add_comm M,
  Finset.sum_Ico_succ_top hk, Ico_succ_right]

lemma summatory_one {𝕜 : Type*} [IsROrC 𝕜] (k : ℕ) (n : ℝ) (h : k ≤ n) :
    summatory (fun _ ↦ (1 : 𝕜)) k n = ⌊n⌋₊ - k + 1 := by
  rw [summatory, Finset.sum_const, nsmul_eq_mul, mul_one, card_Icc, cast_sub, cast_add, cast_one,
      add_sub_right_comm]
  rw [← floor_add_one, le_floor_iff] <;> linarith

@[measurability] lemma measurable_summatory [AddCommMonoid M] [MeasurableSpace M] {k : ℕ} :
    Measurable (summatory a k) := by
  change Measurable ((fun y => ∑ i in Finset.Icc k y, a i) ∘ _)
  exact measurable_from_nat.comp measurable_floor

lemma abs_summatory_le_sum {M : Type*} [h : SeminormedAddCommGroup M] (a : ℕ → M) {k : ℕ} {x : ℝ} :
    ‖summatory a k x‖ ≤ ∑ i in Finset.Icc k ⌊x⌋₊, ‖a i‖ := by
  rw [summatory]
  exact @norm_sum_le _ _ h _ _

lemma abs_summatory_bound {M : Type*} [h : SeminormedAddCommGroup M] (a : ℕ → M) (k z : ℕ)
    {x : ℝ} (hx : x ≤ z) : ‖summatory a k x‖ ≤ ∑ i in Finset.Icc k z, ‖a i‖ :=
  (abs_summatory_le_sum a).trans
    (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc le_rfl (floor_le_of_le hx)) (by simp))

lemma partial_summation_integrable_Ioc {𝕜 : Type*} [IsROrC 𝕜] (a : ℕ → 𝕜) {f : ℝ → 𝕜} {x y : ℝ}
    {k : ℕ} (hf' : IntegrableOn f (Ioc x y)) :
    IntegrableOn (summatory a k * f) (Ioc x y) := by
  let b := ∑ i in Finset.Icc k ⌈y⌉₊, norm (a i)
  have : IntegrableOn (b • f) (Ioc x y) := by exact Integrable.smul b hf'
  refine this.integrable.mono ?_ ?_
  · exact AEStronglyMeasurable.mul (measurable_summatory a).aestronglyMeasurable hf'.1
  · rw [ae_restrict_iff' (measurableSet_Ioc : MeasurableSet (Ioc x _))]
    refine eventually_of_forall (fun z hz ↦ ?_)
    rw [Pi.mul_apply, norm_mul, Pi.smul_apply, norm_smul]
    refine mul_le_mul_of_nonneg_right ((abs_summatory_bound _ _ ⌈y⌉₊ ?_).trans ?_) (norm_nonneg _)
    · exact hz.2.trans (le_ceil y)
    · apply le_norm_self

lemma partial_summation_integrable_Ico {𝕜 : Type*} [IsROrC 𝕜] (a : ℕ → 𝕜) {f : ℝ → 𝕜} {x y : ℝ}
    {k : ℕ} (hf' : IntegrableOn f (Ico x y)) :
    IntegrableOn (summatory a k * f) (Ico x y) := by
  let b := ∑ i in Finset.Icc k ⌈y⌉₊, norm (a i)
  have : IntegrableOn (b • f) (Ico x y) := by exact Integrable.smul b hf'
  refine this.integrable.mono ?_ ?_
  · exact AEStronglyMeasurable.mul (measurable_summatory a).aestronglyMeasurable hf'.1
  · rw [ae_restrict_iff' (measurableSet_Ico)]
    refine eventually_of_forall (fun z hz ↦ ?_)
    rw [Pi.mul_apply, norm_mul, Pi.smul_apply, norm_smul]
    refine mul_le_mul_of_nonneg_right ((abs_summatory_bound _ _ ⌈y⌉₊ ?_).trans ?_) (norm_nonneg _)
    · exact le_trans hz.2.le (le_ceil y)
    · apply le_norm_self

lemma summatory_floor_self {𝕜 : Type*} [IsROrC 𝕜] (a : ℕ → 𝕜) (k : ℕ) : summatory a k k = a k := by
  rw [summatory, floor_coe, Finset.Icc_self, Finset.sum_singleton]

/- Add to Mathlib -/
lemma eqOn_mul_right [Mul β] {f g : α → β} (h : α → β) (h' : EqOn f g S) : EqOn (f * h) (g * h) S :=
  fun _ hx ↦ by simp only [Pi.mul_apply, h' hx]

theorem sum_integral_Ioc
    {𝕜 : Type*} [IsROrC 𝕜]
    {k N : ℕ} (hN : k ≤ N)
    (f : ℝ → 𝕜) (hf : IntegrableOn f (Ioc k N)) :
    ∑ x in Finset.Ico k N, ∫ t in Ioc (x : ℝ) (x + 1), f t = ∫ t in Ioc (k : ℝ) N, f t := by
  revert hf
  refine le_induction ?_ ?_ N hN
  · intro
    rw [Finset.Ico_self, Ioc_self, integral_empty]
    rfl
  · intro n h hf hi
    have h₁ : (k : ℝ) ≤ (n : ℝ) := by norm_cast
    have h₂ : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have h₃ := IntegrableOn.mono_set hi $ Ioc_subset_Ioc_right $ (@cast_add_one ℝ _ n).symm ▸ h₂
    have h₄ := IntegrableOn.mono_set hi $ Ioc_subset_Ioc_left h₁
    rw [Finset.sum_Ico_succ_top h, hf h₃, ← integral_union_ae]
    · rw [Ioc_union_Ioc_eq_Ioc, cast_add, cast_one] ; all_goals try simp only [h₁, h₂, h]
    · rw [AEDisjoint, Ioc_inter_Ioc, sup_eq_right.mpr h₁, inf_eq_left.mpr h₂, Ioc_self,
          measure_empty]
    · measurability
    · exact h₃
    · exact_mod_cast h₄

theorem sum_integral_Ico
    {𝕜 : Type*} [IsROrC 𝕜]
    {k N : ℕ} (hN : k ≤ N)
    (f : ℝ → 𝕜) (hf : IntegrableOn f (Ico k N)) :
    ∑ x in Finset.Ico k N, ∫ t in Ico (x : ℝ) (x + 1), f t = ∫ t in Ico (k : ℝ) N, f t := by
  revert hf
  refine le_induction ?_ ?_ N hN
  · intro
    rw [Finset.Ico_self, Ico_self, integral_empty]
    rfl
  · intro n h hf hi
    have h₁ : (k : ℝ) ≤ (n : ℝ) := by norm_cast
    have h₂ : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have h₃ := IntegrableOn.mono_set hi $ Ico_subset_Ico_right $ (@cast_add_one ℝ _ n).symm ▸ h₂
    have h₄ := IntegrableOn.mono_set hi $ Ico_subset_Ico_left h₁
    rw [Finset.sum_Ico_succ_top h, hf h₃, ← integral_union_ae]
    · rw [Ico_union_Ico_eq_Ico, cast_add, cast_one] ; all_goals try simp only [h₁, h₂, h]
    · rw [AEDisjoint, Ico_inter_Ico, sup_eq_right.mpr h₁, inf_eq_left.mpr h₂, Ico_self,
          measure_empty]
    · measurability
    · exact h₃
    · exact_mod_cast h₄

theorem partial_summation_nat_Ioc {𝕜 : Type*} [IsROrC 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
    {k : ℕ} {N : ℕ} (hN : k ≤ N)
    (hf : ∀ i ∈ Icc (k : ℝ) N, HasDerivAt f (f' i) i)
    (hf' : IntegrableOn f' (Ioc k N)) :
    ∑ n in Finset.Icc k N, a n * f n =
      summatory a k N * f N - ∫ t in Ioc (k : ℝ) N, summatory a k t * f' t := by
  rw [←Nat.Ico_succ_right]
  revert hf hf'
  refine le_induction ?_ ?_ N hN
  · intro _ _
    simp [summatory_nat]
  · intro N hN₁ ih hf hf'
    have hN₂ : (N : ℝ) ≤ N + 1 := le_of_lt $ lt_add_one _
    have ih₁ : Icc (k : ℝ) (N + 1) = Icc (k : ℝ) N ∪ Icc N (N + 1) :=
      (Icc_union_Icc_eq_Icc (cast_le.mpr hN₁) hN₂).symm
    have ih₂ : Ioc (k : ℝ) (N + 1) = Ioc (k : ℝ) N ∪ Ioc N (N + 1) :=
      (Ioc_union_Ioc_eq_Ioc (cast_le.mpr hN₁) hN₂).symm
    simp [ih₁, ih₂, or_imp, forall_and] at ih hf hf' ⊢
    specialize ih hf.1 hf'.1
    have hN₃ := hN₁.trans (@le_self_add _ _ _ 1)
    rw [Finset.sum_Ico_succ_top hN₃, ih, summatory_succ _ _ _ hN₃, add_mul, add_sub_assoc,
         add_comm, cast_add_one, add_right_inj, eq_comm, sub_eq_sub_iff_sub_eq_sub, ←mul_sub,
         integral_union_ae, add_sub_cancel']
    rotate_left
    · rw [AEDisjoint, Ioc_inter_Ioc, sup_eq_right.mpr, inf_eq_left.mpr, Ioc_self, measure_empty]
      all_goals norm_cast
      linarith
    · exact measurableSet_Ioc.nullMeasurableSet
    · exact partial_summation_integrable_Ioc a hf'.left
    · exact partial_summation_integrable_Ioc a hf'.right
    · have : EqOn (fun x => summatory a k x * f' x)
        (fun x => summatory a k N • f' x) (Ico N (N + 1)) :=
      by
        intro x hx
        apply congrArg₂
        · apply summatory_eq_of_Ico _ hx
        · rfl
      rw [set_integral_congr_set_ae (Ico_ae_eq_Ioc' volume_singleton volume_singleton).symm,
          set_integral_congr measurableSet_Ico this, integral_smul, Algebra.id.smul_eq_mul,
          set_integral_congr_set_ae (Ico_ae_eq_Ioc' volume_singleton volume_singleton),
          ←intervalIntegral.integral_of_le hN₂, intervalIntegral.integral_eq_sub_of_hasDerivAt]
      · rw [uIcc_of_le hN₂]
        exact fun x hx ↦ hf.right x hx.left hx.right
      · exact (intervalIntegrable_iff_integrable_Ioc_of_le hN₂).mpr hf'.right

/- Alternate proof -/
@[deprecated] theorem partial_summation_nat_Ioc' {𝕜 : Type*} [IsROrC 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
    {k : ℕ} {N : ℕ} (hN : k ≤ N)
    (hf : ∀ i ∈ Icc (k : ℝ) N, HasDerivAt f (f' i) i)
    (hf' : IntegrableOn f' (Ioc k N)) :
    ∑ n in Finset.Icc k N, a n * f n =
      summatory a k N * f N - ∫ t in Ioc (k : ℝ) N, summatory a k t * f' t := by
  by_cases hk : k = N <;> simp [hk, summatory]

  /- Shift index -/
  rw [←Ico_succ_right, Finset.sum_eq_sum_Ico_succ_bot $ lt_succ_of_le hN]
  have : ∀ n, n ∈ Finset.Ico k N →
      a (n + 1) * f ↑(n + 1) = (summatory a k (n + 1) - summatory a k n) * f (n + 1) := by
    intro n hn
    have : k ≤ n + 1 := (Finset.mem_Ico.mp hn).left.trans $ by linarith
    rw [cast_add, cast_one, summatory_succ _ _ _ this, add_comm, add_sub_cancel]
  rw [←Finset.sum_Ico_add']
  /- Write a n = S (n + 1) - S n, then split sum -/
  rw [Finset.sum_congr rfl this]
  clear this
  simp only [sub_mul, Finset.sum_sub_distrib, show ∀ x : ℕ, ((x : ℝ) + 1) = (x + 1 : ℕ) by simp]
  /- Shift index for telescoping -/
  rw [Finset.sum_Ico_add' (fun (x : ℕ) ↦ summatory a k ↑x * f ↑x)]
  /- Isolating start / end terms -/
  have hk' : k + 1 ≤ N := succ_le_of_lt $ lt_of_le_of_ne hN hk
  rw [Finset.sum_Ico_succ_top hk', Finset.sum_eq_sum_Ico_succ_bot hk', summatory_floor_self]
  rw [show ∀ A B C D E : 𝕜, A + (B + C - (D + E)) = C - ((D - A) + (E - B)) by intros ; ring_nf]

  simp only [←Finset.sum_sub_distrib, ←mul_sub]
  have ih : ∀ (h : ℕ → 𝕜) (x : ℕ), x ∈ Finset.Ico k N →
      h x * (f ↑(x + 1) - f ↑x) = h x * ∫ t in Ioc (x : ℝ) (x + 1), f' t := by
    simp_rw [Finset.mem_Ico]
    intro h x ⟨hx₁, hx₂⟩
    rw [cast_add, cast_one]
    rw [←intervalIntegral.integral_of_le (le_of_lt $ lt_add_one _)]
    congr 1
    have hx₁' : (k : ℝ) ≤ x := cast_le.mpr hx₁
    have hx₂' : (x + 1 : ℝ) ≤ N := by exact_mod_cast cast_le.mpr hx₂
    refine (intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ ?_).symm
    · intro t ht
      rw [uIcc_eq_union, Icc_eq_empty (not_le.mpr $ lt_add_one _), union_empty] at ht
      exact hf t ⟨by linarith [ht.left], by linarith [ht.right]⟩
    · refine (intervalIntegrable_iff_integrable_Icc_of_le $ le_of_lt $ lt_add_one _).mpr ?_
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact IntegrableOn.mono_set hf' $ Ioc_subset_Ioc hx₁' hx₂'
  /- ∫ (t : ℝ) in Ico (↑x) (↑x + 1), summatory a k ↑x * f' t -/
  have hs : ∀ (x : ℕ) ⦃t : ℝ⦄, t ∈ Ico (x : ℝ) (x + 1) → summatory a k x = summatory a k t := by
    intro x t ht
    rw [summatory, summatory, Nat.floor_coe, (floor_eq_on_Ico _ _ ht).symm]
  congr
  · rw [summatory, floor_coe, Ico_succ_right]
  · rw [←summatory_floor_self a k]
    rw [←Finset.sum_eq_sum_Ico_succ_bot hk' (fun x : ℕ ↦ summatory a k x * (f ↑(x + 1) - f x))]
    rw [Finset.sum_congr rfl $ ih _]
    simp_rw [←summatory_nat]
    rw [show (fun x => a x) = a by trivial] /- not needed -/
    /- Multiply that step function into the integral -/
    simp_rw [←integral_mul_left]
    /- ... -/
    rw [←integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ico]
    conv =>
      lhs ; arg 2 ; ext x
      rw [←integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ico]
      conv => arg 2 ; change (fun _ ↦ summatory a k ↑x) * f'
      rw [set_integral_congr measurableSet_Ico (eqOn_mul_right f' $ hs x)]
    rw [sum_integral_Ico hN _]
    · refine congrArg₂ _ rfl ?_
      ext
      rw [Pi.mul_apply, summatory_eq_floor]
    · apply partial_summation_integrable_Ico a
      exact integrableOn_Icc_iff_integrableOn_Ico.mp $ integrableOn_Icc_iff_integrableOn_Ioc.mpr hf'
  done

/- I think there might be some symmetry proof, but it probably requires change of variables -/
theorem partial_summation_nat_Ico {𝕜 : Type*} [IsROrC 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
    {k : ℕ} {N : ℕ} (hN : k ≤ N)
    (hf : ∀ i ∈ Icc (k : ℝ) N, HasDerivAt f (f' i) i)
    (hf' : IntegrableOn f' (Ico k N)) :
    ∑ n in Finset.Icc k N, a n * f n =
      summatory a k N * f N - ∫ t in Ico (k : ℝ) N, summatory a k t * f' t := by
  rw [←Nat.Ico_succ_right]
  revert hf hf'
  refine le_induction ?_ ?_ N hN
  · intro _ _
    simp [summatory_nat]
  · intro N hN₁ ih hf hf'
    have hN₂ : (N : ℝ) ≤ N + 1 := le_of_lt $ lt_add_one _
    have ih₁ : Icc (k : ℝ) (N + 1) = Icc (k : ℝ) N ∪ Icc N (N + 1) :=
      (Icc_union_Icc_eq_Icc (cast_le.mpr hN₁) hN₂).symm
    have ih₂ : Ico (k : ℝ) (N + 1) = Ico (k : ℝ) N ∪ Ico N (N + 1) :=
      (Ico_union_Ico_eq_Ico (cast_le.mpr hN₁) hN₂).symm
    simp [ih₁, ih₂, or_imp, forall_and] at ih hf hf' ⊢
    specialize ih hf.1 hf'.1
    have hN₃ := hN₁.trans (@le_self_add _ _ _ 1)
    rw [Finset.sum_Ico_succ_top hN₃, ih, summatory_succ _ _ _ hN₃, add_mul, add_sub_assoc,
         add_comm, cast_add_one, add_right_inj, eq_comm, sub_eq_sub_iff_sub_eq_sub, ←mul_sub,
         integral_union_ae, add_sub_cancel']
    rotate_left
    · rw [AEDisjoint, Ico_inter_Ico, sup_eq_right.mpr, inf_eq_left.mpr, Ico_self, measure_empty]
      all_goals norm_cast
      linarith
    · exact measurableSet_Ico.nullMeasurableSet
    · exact partial_summation_integrable_Ico a hf'.left
    · exact partial_summation_integrable_Ico a hf'.right
    · have : EqOn (fun x => summatory a k x * f' x)
          (fun x => summatory a k N • f' x) (Ico N (N + 1)) := by
        intro x hx
        apply congrArg₂
        · apply summatory_eq_of_Ico _ hx
        · rfl
      rw [set_integral_congr measurableSet_Ico this, integral_smul, Algebra.id.smul_eq_mul,
          set_integral_congr_set_ae (Ico_ae_eq_Ioc' volume_singleton volume_singleton),
          ←intervalIntegral.integral_of_le hN₂, intervalIntegral.integral_eq_sub_of_hasDerivAt]
      · rw [uIcc_of_le hN₂]
        exact fun x hx ↦ hf.right x hx.left hx.right
      · apply (intervalIntegrable_iff_integrable_Icc_of_le hN₂).mpr
        exact integrableOn_Icc_iff_integrableOn_Ico.mpr hf'.right

theorem partial_summation_real_Ioc {𝕜 : Type*} [IsROrC 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
    {k : ℕ} {N : ℝ} (hN : k ≤ N)
    (hf : ∀ i ∈ Icc (k : ℝ) N, HasDerivAt f (f' i) i)
    (hf' : IntegrableOn f' (Ioc k N)) :
    ∑ n in Finset.Icc k ⌊N⌋₊, a n * f n =
      summatory a k N * f N - ∫ t in Ioc (k : ℝ) N, summatory a k t * f' t := by
  sorry

theorem partial_summation_real_Ico {𝕜 : Type*} [IsROrC 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
    {k : ℕ} {N : ℝ} (hN : k ≤ N)
    (hf : ∀ i ∈ Icc (k : ℝ) N, HasDerivAt f (f' i) i)
    (hf' : IntegrableOn f' (Ico k N)) :
    ∑ n in Finset.Icc k ⌊N⌋₊, a n * f n =
      summatory a k N * f N - ∫ t in Ico (k : ℝ) N, summatory a k t * f' t := by
  sorry

theorem partial_summation_coef_one_Ioc {𝕜 : Type*} [IsROrC 𝕜] (f f' : ℝ → 𝕜)
    {k : ℕ} {N : ℝ} (hN : k ≤ N)
    (hf : ∀ i ∈ Icc (k : ℝ) N, HasDerivAt f (f' i) i)
    (hf' : IntegrableOn f' (Ioc k N)) :
    ∑ n in Finset.Icc k ⌊N⌋₊, f n =
      (⌊N⌋₊ - k + 1) * f N - ∫ t in Ioc (k : ℝ) N, (⌊t⌋₊ - k + 1) * f' t := by
  have := partial_summation_real_Ioc (fun _ ↦ (1 : 𝕜)) f f' hN hf hf'
  simp only [one_mul] at this
  rw [this, summatory_one k N hN]
  congr 1
  apply set_integral_congr
  · measurability
  · intro t ht
    beta_reduce
    rw [summatory_one _ _ $ le_of_lt ht.left]

theorem partial_summation_coef_one_Ico {𝕜 : Type*} [IsROrC 𝕜] (f f' : ℝ → 𝕜)
    {k : ℕ} {N : ℝ} (hN : k ≤ N)
    (hf : ∀ i ∈ Icc (k : ℝ) N, HasDerivAt f (f' i) i)
    (hf' : IntegrableOn f' (Ico k N)) :
    ∑ n in Finset.Icc k ⌊N⌋₊, f n =
      (⌊N⌋₊ - k + 1) * f N - ∫ t in Ico (k : ℝ) N, (⌊t⌋₊ - k + 1) * f' t := by
  have := partial_summation_real_Ico (fun _ ↦ (1 : 𝕜)) f f' hN hf hf'
  simp only [one_mul] at this
  rw [this, summatory_one k N hN]
  congr 1
  apply set_integral_congr
  · measurability
  · intro t ht
    beta_reduce
    rw [summatory_one _ _ ht.left]
