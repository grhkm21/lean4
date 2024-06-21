import Mathlib.NumberTheory.NumberField.Embeddings
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding
import Mathlib.NumberTheory.Pell
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Trace
/- Experimental file for number field related stuff -/

open NumberField canonicalEmbedding Pell IsFundamental

#check canonicalEmbedding
#check integerLattice
#check ringOfIntegers

/-
  Find trace of element
  Construct ℚ(√2) and prove it has degree 2?
  Define orthogonal matrices
-/

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

/- If √-d ∈ R, then there are infinitely many solutions to x^2 + y^2 = 1 -/
example (K : Type*) [Field K] [CharZero K]
    {d : ℤ} (hd_pos : 0 < d) (hd_sq₁ : ¬IsSquare d) (hd_sq₂ : ∃ r : K, r ^ 2 = - d) :
    {x : K × K | x.fst ^ 2 + x.snd ^ 2 = 1}.Infinite := by
  let ⟨r, hr⟩ := hd_sq₂
  refine @Set.infinite_of_injective_forall_mem _ _
    (Set.infinite_coe_iff.mpr $ Pell.infinite_of_not_isSquare hd_pos hd_sq₁)
    _ (fun x ↦ (x.val.fst, x.val.snd * r)) ?_ ?_
  · intro x₁ x₂ h_eq
    simp only [Set.mem_setOf_eq, Prod.mk.injEq, Int.cast_inj] at h_eq
    ext
    · tauto
    · replace h_eq := h_eq.right
      have hr : r ≠ 0 := by
        contrapose! hr
        simp [hr, hd_pos, Int.ne_of_gt]
      exact Int.cast_inj.mp $ (mul_left_inj' hr).mp h_eq
  · intro ⟨(x, y), hx⟩
    simp only [Set.mem_setOf_eq, mul_pow, hr, mul_neg, ←sub_eq_add_neg, mul_comm, neg_mul] at hx ⊢
    norm_cast


