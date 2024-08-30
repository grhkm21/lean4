import Mathlib.Tactic

open Real

lemma forall_pos {p : ℝ → Prop} : (∀ x > 0, p x) ↔ (∀ x > 0, p x⁻¹) := by
  constructor <;> intro h
  · intro x hx; apply h _ (by simp [hx])
  · intro x hx; rw [← inv_inv x]; apply h _ (by simp [hx])

lemma le_log_one_add_inv {x : ℝ} (hx : 0 < x) : (log (1 + x⁻¹))⁻¹ ≤ x + 2⁻¹ := by
  revert x
  rw [forall_pos]
  intro x hx
  rw [inv_inv, inv_le (by apply log_pos; linarith) (by positivity), ← one_div, ← one_div, ← one_div,
    div_add_div _ _ hx.ne.symm two_ne_zero, one_mul, mul_one, one_div_div, div_le_iff (by linarith),
    ← sub_nonneg]
  let h : ℝ → ℝ := fun x ↦ log (1 + x) * (2 + x) - x * 2
  let h' : ℝ → ℝ := fun x ↦ log (1 + x) + 1 / (1 + x) - 1
  let h'' : ℝ → ℝ := fun x ↦ 1 / (1 + x) - 1 / (1 + x) ^ 2
  have h_zero : h 0 = 0 := by
    simp [h]
  have h_deriv (x : ℝ) (hx : 0 ≤ x) : HasDerivAt h (h' x) x := by
    simp_rw [h, h']
    have h₁ : HasDerivAt (fun y ↦ log (1 + y)) (1 / (1 + x)) x :=
      ((hasDerivAt_id x).const_add 1).log (by simp; linarith)
    have h₂ : HasDerivAt (fun y ↦ 2 + y) 1 x := (hasDerivAt_id x).const_add 2
    have h₃ : HasDerivAt (fun y ↦ y * 2) 2 x := by simpa using (hasDerivAt_id x).mul_const 2
    convert (h₁.mul h₂).sub h₃ using 1
    rw [eq_comm, add_comm, div_mul_comm, mul_one, mul_one]
    calc
      _ = log (1 + x) + ((1 + x) + 1) / (1 + x) - 2 := by rw [add_right_comm 1 _ 1]; norm_num
      _ = _ := by rw [same_add_div, add_comm 1 (1 / _), ← add_assoc] <;> linarith
  have h'_zero : h' 0 = 0 := by simp [h']
  have h'_deriv (x : ℝ) (hx : 0 ≤ x) : HasDerivAt h' (h'' x) x := by
    simp_rw [h', h'']
    have h₁ : HasDerivAt (fun y ↦ log (1 + y)) (1 / (1 + x)) x :=
      ((hasDerivAt_id x).const_add 1).log (by simp; linarith)
    have h₂ : HasDerivAt (fun y ↦ 1 / (1 + y)) (-1 / (1 + x) ^ 2) x := by
      simpa using ((hasDerivAt_id x).const_add 1).inv (by simp; linarith)
    convert (h₁.add h₂).sub_const 1 using 1
    ring_nf
  have h'_continuousOn : ContinuousOn h' (Set.Ici 0) := by
    simp_rw [h']
    repeat apply ContinuousOn.add
    · apply ContinuousOn.comp continuousOn_log
      · exact (continuous_add_left 1).continuousOn
      · intro x hx
        simp at hx ⊢
        linarith
    · simp_rw [one_div]
      apply ContinuousOn.comp (continuousOn_inv₀)
      · exact (continuous_add_left 1).continuousOn
      · intro x hx
        simp at hx ⊢
        linarith
    · exact continuousOn_const
  have h''_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ h'' x := by
    simp_rw [h'', sub_nonneg]
    rw [one_div_le_one_div]
    · rw [← sub_nonneg, add_sq]
      ring_nf
      apply add_nonneg hx (sq_nonneg x)
    · apply sq_pos_of_pos
      linarith
    · linarith
  have h'_deriv_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ deriv h' x := by
    simp [(h'_deriv x hx).deriv, h''_nonneg x hx]
  have h'_monotoneOn : MonotoneOn h' (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) h'_continuousOn ?_ ?_
    · simp_rw [interior_Ici' Set.nonempty_Iio, h']
      repeat apply DifferentiableOn.add
      · apply (differentiableOn_id.const_add 1).log
        intro x hx
        simp at hx ⊢
        linarith
      · simp_rw [one_div]
        apply (differentiableOn_id.const_add 1).inv
        intro x hx
        simp at hx ⊢
        linarith
      · exact differentiableOn_const (-1)
    · simpa using fun x hx ↦ h'_deriv_nonneg x hx.le
  have h'_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ h' x := by
    convert @h'_monotoneOn 0 (by simp) x hx hx
    rw [h'_zero]
  have h_continuousOn : ContinuousOn h (Set.Ici 0) := by
    simp_rw [h]
    apply ContinuousOn.sub
    · apply ContinuousOn.mul
      · apply ContinuousOn.comp continuousOn_log
        · exact (continuous_add_left 1).continuousOn
        · intro x hx
          simp at hx ⊢
          linarith
      · exact (continuous_add_left 2).continuousOn
    · exact (continuous_mul_right 2).continuousOn
  have h_deriv_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ deriv h x := by
    simp [(h_deriv x hx).deriv, h'_nonneg x hx]
  have h_monotoneOn (x : ℝ) : MonotoneOn h (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) h_continuousOn ?_ ?_
    · simp_rw [interior_Ici' Set.nonempty_Iio, h]
      apply DifferentiableOn.sub
      · apply DifferentiableOn.mul
        · apply (differentiableOn_id.const_add 1).log
          intro x hx
          simp at hx ⊢
          linarith
        · exact differentiableOn_id.const_add 2
      · exact (differentiableOn_id).mul_const 2
    · simpa using fun x hx ↦ h_deriv_nonneg x hx.le
  rw [← h_zero]
  exact @h_monotoneOn x hx.le 0 (by simp) x (by simpa using hx.le) hx.le

#check HasDerivWithinAt.log
