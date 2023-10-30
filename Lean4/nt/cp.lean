import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Function.Floor

open Nat hiding log
open Set Real BigOperators MeasureTheory Filter Asymptotics

lemma aux : IsBigOWith 1 atTop (fun x ↦ x - 1 - ∫ (t : ℝ) in Ioc 1 x, ↑⌊t⌋₊ / t) log := by
  sorry

lemma aux2 : IsBigOWith 1 atTop (fun x ↦ x - ∫ (t : ℝ) in Ioc 1 x, ↑⌊t⌋₊ / t) log := by
  sorry
