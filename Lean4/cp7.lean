import Mathlib.Tactic

open ModularGroup

lemma Matrix.fin_two_def {α : Type*} (M : Matrix (Fin 2) (Fin 2) α) :
    ∃ a b c d : α, M = !![a, b; c, d] := by
  use M 0 0, M 0 1, M 1 0, M 1 1
  ext i j
  fin_cases i <;> fin_cases j<;> simp

protected theorem Int.strong_induction_on {p : Int → Prop} (n : Int)
    (h : ∀ n, (∀ m, |m| < |n| → p m) → p n) : p n := by
  sorry

lemma S_pow_mem_closure {n : ℤ} : S ^ n ∈ Subgroup.closure {S, T} :=
  zpow_mem (Subgroup.subset_closure <| Set.mem_insert _ _) n

lemma T_pow_mem_closure {n : ℤ} : T ^ n ∈ Subgroup.closure {S, T} :=
  zpow_mem (Subgroup.subset_closure <| Set.mem_insert_of_mem _ (by rfl)) n

example : Subgroup.closure {S, T} = ⊤ := by
  ext ⟨γ, hγ⟩
  simp_rw [Subgroup.mem_top, iff_true]
  obtain ⟨a, b, c, d, rfl⟩ := Matrix.fin_two_def γ
  replace hγ : a * d - b * c = 1 := by simp [Matrix.det_fin_two] at hγ; exact hγ
  revert a b d
  apply Int.strong_induction_on c
  intro c ih a b d _ hγ
  by_cases hc : c = 0
  · subst hc
    have h_ad : (a = 1 ∧ d = 1) ∨ (a = -1 ∧ d = -1) := by
      rw [mul_zero, sub_zero] at hγ
      have : a ∣ 1 := by
        rw [← hγ]
        exact Int.dvd_mul_right a d
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hγ with (rfl | rfl)
      <;> simpa [neg_eq_iff_eq_neg] using hγ
    rcases h_ad with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · simp_rw [← coe_T_zpow, Subtype.coe_eta]
      apply Set.mem_of_subset_of_mem (Subgroup.closure_mono (h := {T}) (by simp))
      exact Subgroup.mem_closure_singleton.mpr ⟨b, rfl⟩
    · have : S ^ (2 : ℤ) = -1 := by ext i j; fin_cases i <;> fin_cases j <;> rfl
      convert_to S ^ (2 : ℤ) * T ^ (-b) ∈ Subgroup.closure {S, T}
      · rw [← SetCoe.ext_iff]
        simp [coe_T_zpow, this]
      · exact mul_mem S_pow_mem_closure T_pow_mem_closure
  · obtain ⟨q, r, ha, hr⟩ : ∃ q r : ℤ, a = c * q + r ∧ |r| < |c| := by
      use a / c, a % c, (Int.ediv_add_emod _ _).symm
      rw [abs_eq_self.mpr ?_]
      · exact Int.emod_lt _ hc
      · exact Int.emod_nonneg _ hc
    specialize ih r hr (-c) (-d) (b - q * d) ?_ ?_
    · convert hγ
      rw [ha, Matrix.det_fin_two_of]
      ring_nf
    · convert hγ using 1
      rw [ha]
      ring_nf
    · have : T ^ q * S ^ (3 : ℤ) ∈ Subgroup.closure {S, T} :=
        mul_mem T_pow_mem_closure S_pow_mem_closure
      convert mul_mem this ih
      rw [← SetCoe.ext_iff]
      simp_rw [Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, S, zpow_ofNat, pow_three]
      simp
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, mul_comm]
