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

variable {M : Type*} (a : ℕ → M)

@[measurability] lemma measurable_summatory [AddCommMonoid M] [MeasurableSpace M] {k : ℕ} :
    Measurable (summatory a k) := by
  change Measurable ((fun y => ∑ i in Finset.Icc k y, a i) ∘ _)
  exact measurable_from_nat.comp measurable_floor

lemma abs_summatory_le_sum [h : SeminormedAddCommGroup M] (a : ℕ → M) {k : ℕ} {x : ℝ} :
    ‖summatory a k x‖ ≤ ∑ i in Finset.Icc k ⌊x⌋₊, ‖a i‖ := by
  rw [summatory]
  exact @norm_sum_le _ _ h _ _

lemma abs_summatory_bound [h : SeminormedAddCommGroup M] (k z : ℕ)
    {x : ℝ} (hx : x ≤ z) : ‖summatory a k x‖ ≤ ∑ i in Finset.Icc k z, ‖a i‖ :=
  (abs_summatory_le_sum a).trans
    (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc le_rfl (floor_le_of_le hx)) (by simp))

lemma partial_summation_integrable {𝕜 : Type*} [IsROrC 𝕜] (a : ℕ → 𝕜) {f : ℝ → 𝕜} {x y : ℝ}
    {k : ℕ} (hf' : IntegrableOn f (Icc x y)) :
    IntegrableOn (summatory a k * f) (Icc x y) := by
  let b := ∑ i in Finset.Icc k ⌈y⌉₊, norm (a i)
  have : IntegrableOn (b • f) (Icc x y) := by exact Integrable.smul b hf'
  refine this.integrable.mono ?_ ?_
  · exact AEStronglyMeasurable.mul (measurable_summatory a).aestronglyMeasurable hf'.1
  · rw [ae_restrict_iff' (measurableSet_Icc : MeasurableSet (Icc x _))]
    refine eventually_of_forall (fun z hz ↦ ?_)
    rw [Pi.mul_apply, norm_mul, Pi.smul_apply, norm_smul]
    refine mul_le_mul_of_nonneg_right ((abs_summatory_bound _ _ ⌈y⌉₊ ?_).trans ?_) (norm_nonneg _)
    · exact hz.2.trans (le_ceil y)
    · rw [norm_eq_abs]
      exact le_abs_self b

lemma myLemma {a b : ℝ} (h : x ∈ uIcc a b) (h' : a ≤ b) : a ≤ x ∧ x ≤ b := by
  rw [uIcc_eq_union, mem_union] at h
  cases' h with h h
  · exact h
  · constructor <;> linarith [h.left, h.right]
  done

lemma summatory_floor_self {𝕜 : Type*} [IsROrC 𝕜] (a : ℕ → 𝕜) (k : ℕ) : summatory a k k = a k := by
  rw [summatory, floor_coe, Finset.Icc_self, Finset.sum_singleton]

/- Add to Mathlib -/
lemma eqOn_mul_right [Mul β] {f g : α → β} (h : α → β) (h' : EqOn f g S) : EqOn (f * h) (g * h) S :=
  fun _ hx ↦ by simp only [Pi.mul_apply, h' hx]

/- ∑ x in Finset.Ico k N, ∫ (x : ℝ) in Ico (↑x) (↑x + 1), f x -/
theorem sum_integral_Ico
    {𝕜 : Type*} [IsROrC 𝕜]
    {k N : ℕ} (hN : k ≤ N)
    (f : ℝ → 𝕜) (hf : IntegrableOn f (Icc k N)) :
    ∑ x in Finset.Ico k N, ∫ t in Icc (x : ℝ) (x + 1), f t = ∫ t in Icc (k : ℝ) N, f t := by
  revert hf
  refine le_induction ?_ ?_ N hN
  · intro
    rw [Finset.Ico_self, Icc_self, integral_singleton, volume_singleton, ENNReal.zero_toReal,
        zero_smul]
    rfl
  · intro n h hf hi
    have h₁ : (k : ℝ) ≤ (n : ℝ) := by norm_cast
    have h₂ : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have h₃ := IntegrableOn.mono_set hi $ Icc_subset_Icc_right $ (@cast_add_one ℝ _ n).symm ▸ h₂
    have h₄ := IntegrableOn.mono_set hi $ Icc_subset_Icc_left h₁
    rw [Finset.sum_Ico_succ_top h, hf h₃, ← integral_union_ae]
    save
    · rw [Icc_union_Icc_eq_Icc, cast_add, cast_one] ; all_goals try simp only [h₁, h₂, h]
    · rw [AEDisjoint, Icc_inter_Icc_eq_singleton h₁ h₂, volume_singleton]
    · measurability
    · exact h₃
    · exact_mod_cast h₄

set_option profiler true
set_option trace.profiler true

theorem partial_summation_nat {𝕜 : Type*} [IsROrC 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
    {k : ℕ} {N : ℕ} (hN : k ≤ N)
    (hf : ∀ i ∈ Icc (k : ℝ) N, HasDerivAt f (f' i) i)
    (hf' : IntegrableOn f' (Icc k N)) :
    ∑ n in Finset.Icc k N, a n * f n =
      summatory a k N * f N - ∫ t in Icc (k : ℝ) N, summatory a k t * f' t := by
  rw [←Nat.Ico_succ_right]
  revert hf hf'
  refine le_induction ?_ ?_ N hN
  · intro _ _
    simp [summatory_nat]
  · intro N hN₁ ih hf hf'
    have hN₂ : (N : ℝ) ≤ N + 1 := le_of_lt $ lt_add_one _
    have : Icc (k : ℝ) (N + 1) = Icc (k : ℝ) N ∪ Icc N (N + 1) :=
      (Icc_union_Icc_eq_Icc (cast_le.mpr hN₁) hN₂).symm
    simp [this, or_imp, forall_and] at ih hf hf' ⊢
    specialize ih hf.1 hf'.1
    have hN₃ := hN₁.trans (@le_self_add _ _ _ 1)
    rw [Finset.sum_Ico_succ_top hN₃, ih, summatory_succ _ _ _ hN₃, add_mul, add_sub_assoc,
         add_comm, cast_add_one, add_right_inj, eq_comm, sub_eq_sub_iff_sub_eq_sub, ←mul_sub,
         integral_union_ae, add_sub_cancel',
         ←set_integral_congr_set_ae (Ico_ae_eq_Icc' volume_singleton)]
    rotate_left
    · rw [AEDisjoint, Icc_inter_Icc_eq_singleton _ hN₂, volume_singleton]
      rwa [cast_le]
    · exact measurableSet_Icc.nullMeasurableSet
    · exact partial_summation_integrable a hf'.left
    · exact partial_summation_integrable a hf'.right
    · have : EqOn (fun x => summatory a k x * f' x)
        (fun x => summatory a k N • f' x) (Ico N (N + 1)) :=
      by
        intro x hx
        apply congrArg₂
        · apply summatory_eq_of_Ico _ hx
        · rfl
      rw [set_integral_congr measurableSet_Ico this, integral_smul, Algebra.id.smul_eq_mul,
          set_integral_congr_set_ae (Ico_ae_eq_Ioc' volume_singleton volume_singleton),
          ←intervalIntegral.integral_of_le hN₂, intervalIntegral.integral_eq_sub_of_hasDerivAt]
      · rw [uIcc_of_le hN₂]
        exact fun x hx ↦ hf.right x hx.left hx.right
      · exact (intervalIntegrable_iff_integrable_Icc_of_le hN₂).mpr hf'.right

theorem partial_summation_nat' {𝕜 : Type*} [IsROrC 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
    {k : ℕ} {N : ℕ} (hN : k ≤ N)
    (hf : ∀ i ∈ Icc (k : ℝ) N, HasDerivAt f (f' i) i)
    (hf' : IntegrableOn f' (Icc k N)) :
    ∑ n in Finset.Icc k N, a n * f n =
      summatory a k N * f N - ∫ t in Icc (k : ℝ) N, summatory a k t * f' t := by
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

  have ok : ∀ x : ℝ, x ≤ x + 1 := fun x ↦ le_of_lt $ lt_add_one x
  simp only [←Finset.sum_sub_distrib, ←mul_sub]
  have ih : ∀ (h : ℕ → 𝕜) (x : ℕ), x ∈ Finset.Ico k N →
      h x * (f ↑(x + 1) - f ↑x) = h x * ∫ t in Ico (x : ℝ) (x + 1), f' t := by
    simp_rw [Finset.mem_Ico]
    intro h x ⟨hx₁, hx₂⟩
    rw [cast_add, cast_one]
    rw [set_integral_congr_set_ae (Ico_ae_eq_Ioc' volume_singleton volume_singleton)]
    rw [←intervalIntegral.integral_of_le (ok x)]
    congr 1
    have hx₁' : (k : ℝ) ≤ x := cast_le.mpr hx₁
    have hx₂' : (x + 1 : ℝ) ≤ N := by exact_mod_cast cast_le.mpr hx₂
    refine (intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ ?_).symm
    · intro t ht
      rw [uIcc_eq_union, Icc_eq_empty (not_le.mpr $ lt_add_one _), union_empty] at ht
      exact hf t ⟨by linarith [ht.left], by linarith [ht.right]⟩
    · refine (intervalIntegrable_iff_integrable_Icc_of_le $ ok x).mpr ?_
      exact IntegrableOn.mono_set hf' $ Icc_subset_Icc hx₁' hx₂'
  /- done -/
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
    conv =>
      lhs ; arg 2 ; ext x
      conv => arg 2 ; change (fun _ ↦ summatory a k ↑x) * f'
      rw [set_integral_congr measurableSet_Ico (eqOn_mul_right f' $ hs x),
          ←integral_Icc_eq_integral_Ico]
    rw [sum_integral_Ico hN _ (partial_summation_integrable a hf')]
    refine congrArg₂ _ rfl ?_
    ext
    rw [Pi.mul_apply, summatory_eq_floor]
  done

#check Nat.cast_le
