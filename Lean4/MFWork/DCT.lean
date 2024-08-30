import Mathlib

open Filter Topology intervalIntegral MeasureTheory Measure

example {α : Type*} {β : Type*} [NormedAddCommGroup α]
    (f_N : β → ℕ → α) (g : β → α) (f : β → α)
    (dom : ∀ x N, ‖f_N x N‖ ≤ ‖g x‖) (hg : Summable g) (h : ∀ x, Tendsto (f_N x) atTop (𝓝 (f x))) :
    HasSum (fun n ↦ ∑' x, f_N x n) (∑' x, f x) := by
  have := MeasureTheory.hasSum_integral_of_dominated_convergence

#check sum
#check count
#check lintegral
#check integral
#check lintegral_count
#check lintegral_coe_eq_integral

open MeasureTheory.Measure in
example (f : ℝ → ℝ) : ∫ x in (0 : ℝ)..1, f x ∂((count : Measure ℕ) : Measure ℝ) = 0 := by
  /- have := lintegral_count -/

#check MeasureTheory.Measure.count
#check PMF.integral_eq_tsum
#check MeasureTheory.hasSum_integral_of_dominated_convergence
