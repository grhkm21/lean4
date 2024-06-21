import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Lean4.Continuity

/- I want to try to prove Fourier expansion of Eisenstein series,
  following Diamond & Shurmand p.5 -/

open scoped Real Complex Finset UpperHalfPlane
open Filter Complex Topology BigOperators Finset

#check π

theorem asdf (z : ℂ) :
    Tendsto (fun n ↦ π * z * ∏ j in Finset.range n, (1 - z ^ 2 / (j + 1) ^ 2))
      atTop (𝓝 <| sin (π * z)) := by
  exact tendsto_euler_sin_prod _

/- I think this should be a Complex lemma -/
theorem Complex.abs_nonpos_iff {z : ℂ} : abs z ≤ 0 ↔ z = 0 :=
  norm_le_zero_iff (a := z)

/- This won't work since log's arg might wrap around -/
/- theorem Complex.log_prod {α : Type*} (s : Finset α) (f : α → ℂ) (hf : ∀ x ∈ s, f x ≠ 0) : -/
/-     log (∏ i ∈ s, f i) = ∑ i ∈ s, log (f i) := by -/

local notation "f" => fun z ↦ π * cot (π * z)
local notation "g" z => fun n : ℤ ↦ 1 / z + ∑ i ∈ range n, (1 / (z - (i + 1)) + 1 / (z + (i + 1)))

-- https://math.stackexchange.com/a/581206/948125
-- Note: We only need when z ∈ ℍ
theorem aux (z : ℂ) (hz : ∀ n : ℤ, z ≠ n) : sin (π * z) ≠ 0 := by
  apply sin_eq_zero_iff.not.mpr
  push_neg
  intro m
  contrapose! hz
  rw [mul_right_cancel₀ (by norm_cast; exact Real.pi_ne_zero) ((mul_comm z _).trans hz)]
  use m

theorem g_hasSum (z : ℂ) (hz : 0 < z.im) :
    Summable (fun i : ℕ ↦ 1 / (z - (i + 1)) + 1 / (z + (i + 1))) := by
  simp_rw [div_add_div]

theorem pt1_f (z : ℂ) (hz : ∀ n : ℤ, z ≠ n) : ContinuousAt f z :=
  ((continuous_cos.continuousAt.div continuous_sin.continuousAt $ aux _ hz).comp
    <| continuousAt_id.const_mul _).const_mul _


theorem final (z : ℂ) (hz : ∀ n : ℤ, z ≠ n) : Tendsto (g z) atTop (𝓝 <|f z) := by
  done
