import Mathlib.Data.Nat.Basic

theorem rangeDecompose (start mid stop : ℕ) (hs : start ≤ mid ∧ mid ≤ stop)
  {f : ℕ → β → Id (ForInStep β)} :
  STD.forIn (mkRange' start stop) init f =
    STD.forIn (mkRange' mid stop) (Id.run (STD.forIn (mkRange' start mid) init f)) f := by
  sorry