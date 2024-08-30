import Mathlib.Tactic

open Real Filter Topology Set

#check Set.Unbounded
-- too lazy to find in Mathlib
lemma aux (f : ℝ → ℝ) (s : Set ℝ) (hs_unbounded : s.Unbounded (· < ·))
    (c : ℝ) (hf_anti : AntitoneOn f s) (hf_lim : Tendsto f atTop (𝓝 c)) :
    ∀ x, (∃ y ∈ s, y ≤ x) → f x ≥ c := by
  rw [tendsto_atTop_nhds] at hf_lim
  rintro x ⟨y, hy, hy'⟩
  apply le_of_forall_lt
  intro d hd
  obtain ⟨N, hN⟩ := hf_lim (Metric.ball c |c - d|) (by simp [sub_eq_zero]; exact hd.ne.symm)
    Metric.isOpen_ball
  specialize hN x

lemma le_log_one_add_inv {x : ℝ} (hx : 0 < x) : (1 + x)⁻¹ ≤ log (1 + x⁻¹) := by
  let f := fun x : ℝ ↦ log (1 + x⁻¹) - (1 + x)⁻¹
  have h_deriv (y : ℝ) (hy : 0 < y) :
      deriv f y = (-y ^ (-2 : ℤ)) / (1 + y⁻¹) + (1 + y) ^ (-2 : ℤ) := by
    simp_rw [f]
    rw [deriv_sub]
    · -- deriv, algebra
      sorry
    · -- differentiableat
      sorry
    · -- differentiableat
      sorry
  have h_antitone : AntitoneOn f (Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos
    · exact convex_Ioi _
    · have h₁ : ContinuousOn (fun x : ℝ ↦ x⁻¹) (Ioi (0 : ℝ)) := by
        apply continuousOn_inv₀.mono
        simp
      have h₂ : ContinuousOn (fun x : ℝ ↦ (1 + x)⁻¹) (Ioi (0 : ℝ)) :=
         (continuous_const.add continuous_id).continuousOn.inv₀ ?_
      apply ((continuous_const.continuousOn.add h₁).log ?_).sub h₂
      simp
      intro x hx
      have := inv_pos.mpr hx
      linarith
      simp
      intro x hx
      linarith
    · rw [interior_Ioi]
      -- differentiableon
      sorry
    · simp only [interior_Ioi, mem_Ioi]
      intro x hx
      rw [h_deriv x hx, neg_div, neg_add_le_iff_le_add, add_zero, zpow_neg x, ← one_div, div_div,
        ← one_div, mul_add, mul_one, mul_one_div, zpow_two, mul_div_cancel_right₀ _ hx.ne.symm,
        zpow_neg, ← one_div, zpow_two, ← sq, add_sq, one_pow, mul_one, sq]
      apply (one_div_le_one_div (by positivity) (by positivity)).mpr
      linarith
  have h_tendsto : Tendsto f atTop (𝓝 0) := by
    simp_rw [f]
    have h₁ := (tendsto_inv_atTop_zero.const_add (1 : ℝ)).log (by simp)
    have h₂ := tendsto_atTop_add_const_left _ (1 : ℝ) tendsto_id
    convert h₁.sub (b := 0) (tendsto_inv_atTop_zero.comp h₂) using 1
    simp
  have := aux f _ ?_ 0 h_antitone h_tendsto
  · have := this x (by simp [hx])
    simp_rw [f] at this
    exact sub_nonneg.mp this
  · intro x
    use max x 1
    simp
