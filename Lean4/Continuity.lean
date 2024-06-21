import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd

open scoped Real
open Filter Complex Topology BigOperators

theorem ContinuousOn.ofReal {f : ℂ → ℝ} {s : Set ℂ} (hf : ContinuousOn f s) :
    ContinuousOn (ofReal' ∘ f) s :=
  continuous_ofReal.continuousOn.comp hf (s.mapsTo_image f)

theorem ContinuousOn.re {f : ℂ → ℂ} {s : Set ℂ} (hf : ContinuousOn f s) : ContinuousOn (re ∘ f) s :=
  fun z hz ↦ continuous_re.continuousWithinAt.comp (hf z hz) (s.mapsTo_image _)

theorem ContinuousOn.im {f : ℂ → ℂ} {s : Set ℂ} (hf : ContinuousOn f s) : ContinuousOn (im ∘ f) s :=
  fun z hz ↦ continuous_im.continuousWithinAt.comp (hf z hz) (s.mapsTo_image _)

theorem ContinuousOn.complex_iff {f : ℂ → ℂ} {s : Set ℂ} :
    ContinuousOn f s ↔ ContinuousOn (Complex.re ∘ f) s ∧ ContinuousOn (Complex.im ∘ f) s :=
  ⟨fun h ↦ ⟨h.re, h.im⟩, fun ⟨h₁, h₂⟩ z hz ↦ by
    convert (h₁.ofReal z hz).add $ (h₂.ofReal z hz).mul_const I using 1; simp [re_add_im]⟩

example {f : ℂ → ℂ} {s : Set ℂ} (z : ℂ) (hz : z ∈ s) (h : ContinuousAt f z) :
    ContinuousWithinAt f s z := by
  exact?
