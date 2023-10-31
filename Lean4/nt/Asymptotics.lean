import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic

import Lean4.nt.PartialSummation

open Nat hiding log
open Set Real BigOperators MeasureTheory Filter Asymptotics

lemma h₁ {x : ℝ} {a : ℕ} (h : a ≤ x) : x = a + ∫ (t : ℝ) in Ioc (a : ℝ) x, 1 := by
  rw [integral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, volume_Ioc,
      smul_eq_mul, mul_one, ENNReal.toReal_ofReal] <;> linarith

lemma h₂ {x : ℝ} (ha : 0 < x) : 1 - ⌊x⌋₊ / x = (Int.fract x) / x := by
  rw [Int.fract, sub_div, div_self, cast_floor_eq_cast_int_floor] <;> linarith

lemma h₃ {x : ℝ} (hx : 0 < x) : Int.fract x / x ≤ 1 / x := by
  rw [div_le_div_right (by linarith)]
  exact (Int.fract_lt_one _).le

lemma h₄ {x : ℝ} (hx : 0 < x) : |Int.fract x / x| ≤ 1 / x := by
  rw [abs_of_nonneg]
  · exact h₃ hx
  · rw [le_div_iff, zero_mul, Int.fract] <;> linarith [Int.floor_le x]

lemma integrableOn_Ioc_one_div (x y : ℝ) (h : 0 < x) (h' : x ≤ y) :
    IntegrableOn (fun a => 1 / a) (Ioc x y) := by
  have h : Ioc x y = uIoc x y := by
    rw [uIoc, min_eq_left, max_eq_right] <;> linarith
  rw [h]
  apply intervalIntegrable_iff.mp
  apply intervalIntegral.intervalIntegrable_one_div _ continuousOn_id
  intro t ht
  rw [id]
  rw [uIcc, sup_eq_right.mpr, inf_eq_left.mpr] at ht <;> linarith [ht.left]

lemma integrableOn_Ioc_inv (x y : ℝ) (h : 0 < x) (h' : x ≤ y) :
    IntegrableOn (fun a => a⁻¹) (Ioc x y) := by
  simp_rw [←one_div, integrableOn_Ioc_one_div x y h h']

lemma integrableOn_Ioc_fract_div (x y : ℝ) (h : 0 < x) (h' : x ≤ y) :
    IntegrableOn (fun a => Int.fract a / a) (Ioc x y) := by
  have := (intervalIntegrable_iff_integrable_Ioc_of_le h').mpr
    (integrableOn_Ioc_one_div _ _ h h')
  refine (IntervalIntegrable.mono_fun' this ?_ ?_).left
  · exact Measurable.aestronglyMeasurable (Measurable.mul measurable_fract measurable_inv)
  · rw [EventuallyLE, ae_restrict_iff']
    · apply eventually_of_forall
      simp_rw [uIoc_of_le h']
      intro t ⟨ht, _⟩
      rw [norm_eq_abs]
      exact h₄ $ h.trans ht
    · exact measurableSet_uIoc

lemma integrableOn_Ioc_floor_div (x y : ℝ) (h : 0 < x) (h' : x ≤ y) :
    IntegrableOn (fun t : ℝ => ⌊t⌋₊ / t) (Ioc x y) := by
  rw [IntegrableOn, @integrable_congr _ _ _ _ _ _ (fun a : ℝ ↦ 1 - Int.fract a / a)]
  · apply Integrable.sub
    · exact integrable_const 1
    · rw [←IntegrableOn]
      exact integrableOn_Ioc_fract_div _ _ h h'
  · rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    apply eventually_of_forall
    intro t ⟨ht, _⟩
    rw [←h₂ $ h.trans ht]
    ring

lemma integrableOn_Ioc_one_sub_floor_div (x y : ℝ) (h : 0 < x) (h' : x ≤ y) :
    IntegrableOn (fun t : ℝ => 1 - ⌊t⌋₊ / t) (Ioc x y) := by
  rw [IntegrableOn]
  apply (integrable_congr _).mp $ integrableOn_Ioc_fract_div _ _ h h'
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  apply eventually_of_forall
  intro t ⟨ht, _⟩
  rw [h₂ $ h.trans ht]

lemma aux0 (x y : ℝ) (h : 0 < x) (h' : x ≤ y) :
    0 ≤ (∫ (t : ℝ) in Ioc x y, 1) - ∫ (t : ℝ) in Ioc x y, ↑⌊t⌋₊ / t := by
  rw [←integral_sub (integrable_const _) (integrableOn_Ioc_floor_div _ _ h h')]
  apply integral_nonneg_of_ae
  rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
  apply eventually_of_forall
  intro t ⟨ht, _⟩
  rw [h₂ $ h.trans ht, le_div_iff (by linarith), Pi.zero_apply, zero_mul]
  exact Int.fract_nonneg t

lemma aux0' (x y : ℝ) (h : 0 < x) (h' : x ≤ y) :
    0 ≤ (y - x) - ∫ (t : ℝ) in Ioc x y, ↑⌊t⌋₊ / t := by
  convert aux0 x y h h'
  rw [integral_const 1, Measure.restrict_apply MeasurableSet.univ, univ_inter, volume_Ioc,
      smul_eq_mul, mul_one, ENNReal.toReal_ofReal (by linarith)]

lemma aux1 : IsBigOWith 1 atTop (fun (x : ℝ) ↦ ⌊x⌋₊ - x) (fun _ ↦ (1 : ℝ)) := by
  rw [isBigOWith_iff, eventually_atTop]
  use 1
  intro x hx
  rw [norm_eq_abs, norm_one, mul_one, abs_le]
  constructor
  · rw [le_sub_iff_add_le', ←sub_eq_add_neg, tsub_le_iff_right]
    exact (lt_floor_add_one _).le
  · linarith [floor_le (show 0 ≤ x by linarith)]

lemma aux2 : IsBigOWith 1 atTop (fun x ↦ (⌊x⌋₊ * log x) - (x * log x)) log := by
  simp_rw [← sub_mul]
  convert IsBigOWith.mul aux1 $ isBigOWith_refl log atTop using 2
  all_goals rw [one_mul]

/- Note: Use Ioc for integrals -/
lemma aux3 (x : ℝ) (a : ℕ) (ha : 0 < a) (hx : a ≤ x) :
    ∫ (t : ℝ) in Ioc (a : ℝ) x, Int.fract t / t ≤ log x - log a := by
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  rw [←log_div, ←integral_inv_of_pos, intervalIntegral.intervalIntegral_eq_integral_uIoc, if_pos,
      uIoc_of_le, one_smul]
  apply set_integral_mono_on
  all_goals try linarith
  · exact integrableOn_Ioc_fract_div _ _ ha' hx
  · exact integrableOn_Ioc_inv _ _ ha' hx
  · exact measurableSet_Ioc
  · intro t ⟨ht, _⟩
    rw [←one_div]
    exact h₃ (by linarith)

lemma aux4 (x : ℝ) (a : ℕ) (ha : 1 ≤ a) (hx : a ≤ x) :
    x - a - ∫ (t : ℝ) in Ioc (a : ℝ) x, ⌊t⌋₊ / t ≤ log x - log a := by
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  nth_rw 1 [h₁ hx, show ∀ a b c : ℝ, (a + b) - a - c = b - c by intro _ _ _ ; ring_nf]
  rw [←integral_sub (integrable_const 1) (integrableOn_Ioc_floor_div _ _ ha' hx)]
  convert aux3 x a ha hx using 1
  rw [set_integral_congr measurableSet_Ioc]
  intro t ⟨ht, _⟩
  beta_reduce
  exact h₂ $ ha'.trans ht

lemma aux5 : IsBigOWith 1 atTop (fun x ↦ x - 1 - ∫ (t : ℝ) in Ioc 1 x, ↑⌊t⌋₊ / t) log := by
  rw [isBigOWith_iff, eventually_atTop]
  use 1
  intro x hx
  rw [norm_of_nonneg $ log_nonneg hx, one_mul, norm_of_nonneg $ aux0' 1 x zero_lt_one hx]
  · convert aux3 x 1 (le_refl _) (by exact_mod_cast hx) using 1
    · rw [cast_one]
    · rw [cast_one, log_one, sub_zero]

lemma aux6 (n : ℕ) : ∫ (x : ℝ) in Ioc (1 : ℝ) ↑(n + 1), ⌊x⌋₊ / x =
    n * (log ↑(n + 1) - log n) + ∫ (x : ℝ) in Ioc (1 : ℝ) n, ⌊x⌋₊ / x := by
  by_cases hn : n = 0
  · simp only [hn] ; norm_num
  · replace hn := one_le_iff_ne_zero.mpr hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast cast_le.mpr hn
    have : Ioc (1 : ℝ) (n + 1) = Ioc (1 : ℝ) n ∪ Ioc n (n + 1) := by
      rw [Ioc_union_Ioc_eq_Ioc hn' (by linarith)]
    rw [←log_div, ←integral_inv_of_pos, intervalIntegral.intervalIntegral_eq_integral_uIoc, if_pos,
        uIoc_of_le, one_smul]
    simp_rw [←one_div, ←integral_mul_left, mul_one_div]
    push_cast
    rw [this, integral_union Ioc_disjoint_Ioc_same measurableSet_Ioc, add_comm, add_left_inj]
    iterate 2 rw [integral_Ioc_eq_integral_Ioo, ←integral_Ico_eq_integral_Ioo]
    · apply integral_congr_ae
      rw [EventuallyEq, ae_restrict_iff' measurableSet_Ico]
      apply eventually_of_forall
      intro x ⟨hx₁, hx₂⟩
      congr
      rw [(floor_eq_iff _).mpr ⟨hx₁, hx₂⟩]
      linarith
    all_goals try apply integrableOn_Ioc_floor_div
    all_goals push_cast
    all_goals norm_cast
    all_goals try linarith

lemma aux7 (n : ℕ) : ∫ (x : ℝ) in Ioc (1 : ℝ) ↑(n + 1), ⌊x⌋₊ / x =
    ∑ t in Finset.Icc 1 n, t * (log ↑(t + 1) - log t) := by
  induction' n with n hn
  · norm_num
  · rw [aux6 _, hn]
    push_cast
    conv =>
      rhs
      rw [←Ico_succ_right, Finset.sum_Ico_succ_top (by linarith), Ico_succ_right]
    push_cast
    ring_nf
    congr
    funext x
    rw [mul_sub, add_comm]

set_option profiler true
set_option trace.profiler true

lemma aux8 : 0 ≤ (∫ (x : ℝ) in Ioc 1 7, ↑⌊x⌋₊ / x) - 7 + log 7 := by
  have h₁ := aux7 6
  norm_num at h₁
  rw [h₁]
  simp [show Finset.Icc (1 : ℕ) 6 = {1, 2, 3, 4, 5, 6} by rfl]
  ring_nf
  rw [add_sub, add_sub]
  repeat rw [←sub_eq_add_neg]
  iterate 4 rw [sub_sub, ←log_mul]
  nth_rw 3 [show (7 : ℝ) = (7 : ℕ) by rfl]
  rw [mul_comm (log _) _, add_comm_sub, ←Real.log_pow, ←log_div]
  all_goals try norm_num
  rw [le_log_iff_exp_le]
  /- annoying issue: There's both (a : ℝ) ^ (b : ℕ) and (a : ℝ) ^ (b : ℝ) -/
  let h := @rpow_le_rpow _ _ (7 : ℕ) ?_ (tsub_le_iff_left.mp $ (abs_le.mp exp_one_near_10).right) ?_
  rw [exp_one_rpow, rpow_nat_cast] at h
  apply h.trans
  all_goals norm_num
  exact le_of_lt $ exp_pos 1

lemma aux9 : IsBigOWith 1 atTop (fun x ↦ x - ∫ (t : ℝ) in Ioc 1 x, ↑⌊t⌋₊ / t) log := by
  simp_rw [isBigOWith_iff, eventually_atTop, one_mul]
  use 7
  intro x hx
  have i₁ : Ioc 1 x = (Ioc 1 7) ∪ (Ioc 7 x) := by rw [Ioc_union_Ioc_eq_Ioc] <;> linarith
  have i₃ : Ioc 1 7 ⊆ Ioc 1 x := Ioc_subset_Ioc_right hx
  have i₄ : Ioc 7 x ⊆ Ioc 1 x := Ioc_subset_Ioc_left (by linarith)
  have i₅ : (1 : ℝ) ≤ 7 := by norm_num
  rw [norm_of_nonneg $ log_nonneg (by linarith), norm_of_nonneg]
  · suffices h : x - 7 - ∫ (t : ℝ) in Ioc 7 x, ⌊t⌋₊ / t ≤ log x - log 7
    · replace h := _root_.le_sub_iff_add_le.mp h
      apply le_trans _ h
      rw [i₁, integral_union Ioc_disjoint_Ioc_same measurableSet_Ioc]
      · rw [←sub_sub]
        have h : ∀ A B C D E : ℝ, A - B - C ≤ A - D - C + E ↔ 0 ≤ B - D + E := by
          intro A B C D E ; constructor <;> intro h <;> linarith [h]
        rw [h]
        exact aux8
      all_goals
        apply IntegrableOn.mono_set $ integrableOn_Ioc_floor_div _ _ zero_lt_one $ i₅.trans hx
      exact i₃
      exact i₄
    apply aux4
    · linarith
    · exact_mod_cast hx
  · apply (aux0' 1 x zero_lt_one _).trans
    all_goals linarith
  done

theorem log_asympt_eff :
    IsBigOWith 2 atTop (fun x ↦ (summatory (fun n ↦ log n) 1 x) - (x * log x - x)) log := by
  rw [isBigOWith_iff, eventually_atTop]
  simp_rw [norm_eq_abs] /- not required -/
  use 100
  intro x hx
  rw [summatory, partial_summation_coef_one log (fun x ↦ x⁻¹)]
  all_goals push_cast at *
  · simp only [cast_one, sub_add_cancel, ←one_div, mul_one_div]
    sorry
  · linarith
  · intro t ⟨ht, _⟩
    exact hasDerivAt_log (by linarith)
  /- · apply integrableOn_Ioc_inv -/
