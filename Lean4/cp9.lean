import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open scoped UpperHalfPlane Real
open UpperHalfPlane hiding I
open Filter Complex Topology

#check Set
lemma Complex.norm_exp_mul_I (z : ℂ) : ‖cexp (z * I)‖ = rexp (-z.im) := by
  sorry

example {α : Type*} (A : Set α) : (fun x ↦ x ∈ A) = A := rfl

example (h : ℝ) (h' : 0 < h) : Tendsto (fun z : ℍ ↦ exp (2 * π * I * z / h)) atImInfty (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [mul_right_comm _ I, mul_div_right_comm _ I, norm_exp_mul_I]
  have : Tendsto UpperHalfPlane.im atImInfty atTop := tendsto_iff_comap.mpr fun ⦃U⦄ a => a
  have : Tendsto (fun x : UpperHalfPlane ↦ 2 * π * x.im / h) atImInfty atTop :=
    ((tendsto_id.const_mul_atTop (show 0 < 2 * π by positivity)).atTop_div_const h').comp this
  simpa using this
