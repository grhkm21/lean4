import Mathlib

open Pell IsFundamental in
theorem Pell.infinite_of_not_isSquare {d : ℤ} (hd_pos : 0 < d) (hd_sq₁ : ¬IsSquare d) :
    {x : ℤ × ℤ | x.fst ^ 2 - d * x.snd ^ 2 = 1}.Infinite := by
  let ⟨sol, h_fund⟩ := IsFundamental.exists_of_not_isSquare hd_pos hd_sq₁
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℤ ↦ ((sol ^ n).x, (sol ^ n).y))
  · intro n₁ n₂ h_eq
    rw [Prod.mk.injEq] at h_eq
    let ⟨_, hy_eq⟩ := h_eq
    exact h_fund.y_strictMono.injective hy_eq
  · intro n
    rw [Set.mem_setOf_eq]
    exact Solution₁.prop (sol ^ n)
