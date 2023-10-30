import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Function.Floor
import Lean4.nt.PartialSummation

open Nat hiding log
open Set Real BigOperators MeasureTheory Filter Asymptotics

#check intervalIntegral.intervalIntegrable_inv
#check intervalIntegrable_iff

lemma h₁ (x : ℝ) (h : 1 ≤ x) : x = 1 + ∫ (t : ℝ) in Ioc 1 x, 1 := by
  rw [integral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, volume_Ioc,
      smul_eq_mul, mul_one, ENNReal.toReal_ofReal] <;> linarith

lemma h₂ (x : ℝ) (ha : 0 < x) : 1 - ⌊x⌋₊ / x = (Int.fract x) / x := by
  rw [Int.fract, sub_div, div_self, cast_floor_eq_cast_int_floor] <;> linarith

lemma h₃ (x : ℝ) (hx : 0 < x) : Int.fract x / x ≤ 1 / x := by
  rw [div_le_div_right (by linarith)]
  exact (Int.fract_lt_one _).le

lemma h₄ (x : ℝ) (hx : 0 < x) : |Int.fract x / x| ≤ 1 / x := by
  rw [abs_of_nonneg]
  · exact h₃ _ hx
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

lemma integrableOn_Ioc_frac_div (x y : ℝ) (h : 0 < x) (h' : x ≤ y) :
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
      exact h₄ t $ h.trans ht
    · exact measurableSet_uIoc

lemma integrableOn_Ioc_floor_div (x y : ℝ) (h : 0 < x) (h' : x ≤ y) :
    IntegrableOn (fun t : ℝ => ⌊t⌋₊ / t) (Ioc x y) := by
  rw [IntegrableOn, @integrable_congr _ _ _ _ _ _ (fun a : ℝ ↦ 1 - Int.fract a / a)]
  · apply Integrable.sub
    · exact integrable_const 1
    · rw [←IntegrableOn]
      exact integrableOn_Ioc_frac_div _ _ h h'
  · rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    apply eventually_of_forall
    intro t ⟨ht, _⟩
    rw [←h₂ t $ h.trans ht]
    ring

lemma integrableOn_Ioc_one_sub_floor_div (x y : ℝ) (h : 0 < x) (h' : x ≤ y) :
    IntegrableOn (fun t : ℝ => 1 - ⌊t⌋₊ / t) (Ioc x y) := by
  rw [IntegrableOn]
  apply (integrable_congr _).mp $ integrableOn_Ioc_frac_div _ _ h h'
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  apply eventually_of_forall
  intro t ⟨ht, _⟩
  rw [h₂ _ $ h.trans ht]

lemma aux0 (x y : ℝ) (h : 0 < x) (h' : x ≤ y) :
    0 ≤ (∫ (t : ℝ) in Ioc x y, 1) - ∫ (t : ℝ) in Ioc x y, ↑⌊t⌋₊ / t := by
  rw [←integral_sub (integrable_const _) (integrableOn_Ioc_floor_div _ _ h h')]
  apply integral_nonneg_of_ae
  rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
  apply eventually_of_forall
  intro t ⟨ht, _⟩
  rw [h₂ t $ h.trans ht, le_div_iff (by linarith), Pi.zero_apply, zero_mul]
  exact Int.fract_nonneg t

lemma aux1 : IsBigOWith 1 atTop (fun (x : ℝ) ↦ ⌊x⌋₊ - x) (fun _ ↦ (1 : ℝ)) := by
  rw [isBigOWith_iff, eventually_atTop]
  use 1
  intro x hx
  rw [norm_eq_abs, norm_one, mul_one, abs_le]
  constructor
  · rw [le_sub_iff_add_le', ←sub_eq_add_neg, tsub_le_iff_right]
    exact (lt_floor_add_one _).le
  · linarith [floor_le (show 0 ≤ x by linarith)]

lemma aux : IsBigOWith 1 atTop (fun x ↦ (⌊x⌋₊ * log x) - (x * log x)) log := by
  simp_rw [← sub_mul]
  convert IsBigOWith.mul aux1 $ isBigOWith_refl log atTop using 2
  all_goals rw [one_mul]

/- Note: Use Ioc for integrals -/
/- TODO: Change Ioc 1 x to Ioc a x for any a ∈ ℕ -/
lemma aux2 : IsBigOWith 1 atTop (fun x ↦ x - 1 - ∫ (t : ℝ) in Ioc 1 x, ↑⌊t⌋₊ / t) log := by
  rw [isBigOWith_iff, eventually_atTop]
  use 1
  intro x hx
  rw [norm_of_nonneg $ log_nonneg hx, one_mul]
  nth_rw 1 [h₁ x hx, show ∀ a b c : ℝ, (a + b) - a - c = b - c by intro _ _ _ ; ring_nf]
  rw [norm_of_nonneg,
      ←integral_sub (integrable_const 1) (integrableOn_Ioc_floor_div _ _ _ hx),
      ←div_one x, ←integral_inv_of_pos _ _,
      intervalIntegral.intervalIntegral_eq_integral_uIoc,
      if_pos hx, uIoc_of_le hx, div_one, one_smul]
  apply set_integral_mono_on
    (integrableOn_Ioc_one_sub_floor_div _ _ _ hx) (integrableOn_Ioc_inv _ _ _ hx) measurableSet_Ioc
  all_goals try linarith
  · intro t ⟨ht, _⟩
    rw [h₂ t, ←one_div]
    apply h₃ t
    all_goals linarith
  · rw [←integral_sub (integrable_const _) $ integrableOn_Ioc_floor_div _ _ zero_lt_one hx]
    apply integral_nonneg_of_ae
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    apply eventually_of_forall
    intro t ⟨ht, _⟩
    rw [h₂ t, le_div_iff, Pi.zero_apply, zero_mul]
    exact Int.fract_nonneg t
    all_goals linarith

lemma aux3 : IsBigOWith 1 atTop (fun x ↦ x - ∫ (t : ℝ) in Ioc 1 x, ↑⌊t⌋₊ / t) log := by
  simp_rw [isBigOWith_iff, eventually_atTop, one_mul]
  use 3
  intro x hx
  have i₁ : Ioc 1 x = (Ioc 1 3) ∪ (Ioc 3 x) := by rw [Ioc_union_Ioc_eq_Ioc] <;> linarith
  have i₂ : Disjoint (Ioc 1 3) (Ioc 3 x) := by sorry
  have i₃ : Ioc 1 3 ⊆ Ioc 1 x := Ioc_subset_Ioc_right hx
  have i₄ : Ioc 3 x ⊆ Ioc 1 x := Ioc_subset_Ioc_left (by linarith)
  rw [norm_of_nonneg $ log_nonneg (by linarith), norm_of_nonneg]
  · done
  /- · exact? -/
  · save
    nth_rw 1 [h₁ x, add_sub_assoc]
    rw [i₁, integral_union i₂, integral_union i₂]
    all_goals
      try linarith
      try exact measurableSet_Ioc
    · done
    · exact IntegrableOn.mono_set (integrableOn_Ioc_floor_div 1 x zero_lt_one (by linarith)) i₃
    · exact IntegrableOn.mono_set (integrableOn_Ioc_floor_div 1 x zero_lt_one (by linarith)) i₄
    · exact IntegrableOn.mono_set (integrable_const 1) i₃
    · exact IntegrableOn.mono_set (integrable_const 1) i₄
  done

#exit

example (f : ℝ → ℝ) (x : ℝ) (hx : 3 ≤ x) (hf : IntegrableOn f (Ioc 1 x)) :
    ∫ t in Ioc 1 x, f t = (∫ t in Ioc 1 3, f t) + ∫ t in Ioc 3 x, f t := by
  rw [←integral_union, Ioc_union_Ioc_eq_Ioc (by linarith) hx]
  · rw [Disjoint]
    exact Ioc_disjoint_Ioc_same
  · measurability
  all_goals apply IntegrableOn.mono_set hf
  exact Ioc_subset_Ioc_right hx
  exact Ioc_subset_Ioc_left (by norm_num)

theorem log_asympt_eff :
    IsBigOWith 2 atTop (fun x ↦ (summatory (fun n ↦ log n) 1 x) - (x * log x - x)) log := by
  sorry

example {a b c : ℝ} : |a + b + c| ≤ |a| + |b| + |c| := by exact?
