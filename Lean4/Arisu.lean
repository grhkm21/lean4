import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

theorem q7 :
  ¬ (∀ ε : ℝ, ε > 0 →
     ∀ δ : ℝ, δ > 0 →
     (∀ x : ℝ, 0 < |x| → |x| < δ → |Real.sqrt (abs x)| < ε) →
     (∀ x : ℝ ,0 < |x| → |x| < δ/2 → |Real.sqrt (abs x)| < ε/2)) := by
  push_neg
  use 1/2, by norm_num, 1/4, by norm_num
  refine ⟨?_, ?_⟩
  · sorry
  · sorry
