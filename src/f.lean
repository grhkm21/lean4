import Mathlib.Data.Nat.Basic

variables {β : Type u} {m : Type u → Type v} [Monad m]

theorem emptyStep' {k : ℕ} {init : β} {f : ℕ → β → Id (ForInStep β)} :
  Std.Range.forIn.loop f k k k 1 init = init := by
  simp [Std.Range.forIn.loop]