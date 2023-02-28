import Mathlib.Data.Nat.Basic

/-
A summary of this file (28 Feb 2023):
+ Add some results about internals of Range and For to aid proofs
-/

open Std Std.Range Std.Range.forIn

variable {β : Type u} {m : Type u → Type v} [Monad m]

namespace ForInStep

/- Boolean version of .isDone -/
def isDone : ForInStep α → Bool
  | .done _ => true
  | _       => false

/- Boolean version of .isYield -/
def isYield : ForInStep α → Bool
  | .yield _ => true
  | _        => false

/- Propositional version of .isDone -/
def isDone' : ForInStep α → Prop := λ s => s.isDone

/- Propositional version of .isYield -/
def isYield' : ForInStep α → Prop := λ s => s.isYield

def extractStep : ForInStep β → m β
  | .done b  => pure b
  | .yield b => pure b

theorem isDoneEqIsDone' (s : ForInStep β) : s.isDone = s.isDone' := rfl

theorem isYieldEqIsYield' (s : ForInStep β) : s.isYield = s.isYield' := rfl

theorem isDoneOrIsYield (s : ForInStep β) : s.isDone ∨ s.isYield := by
  cases s <;> simp [isDone, isYield]

theorem notIsDoneAndIsYield (s : ForInStep β) : ¬(s.isDone ∧ s.isYield) := by
  cases s <;> simp [isDone, isYield]

end ForInStep

namespace Std.Range

/-
Results about `loop`
-/

theorem emptyStep' {start stop : ℕ} {init : β} {f : ℕ → β → Id (ForInStep β)} (hs : stop ≤ start) :
  loop f fuel start stop 1 init = init := by
  cases start <;> cases fuel <;> simp [loop, not_lt_of_ge hs]
  simp [Nat.le_zero.1 hs]

theorem emptyStep {k : ℕ} {init : β} {f : ℕ → β → Id (ForInStep β)} :
  Range.forIn [k : k] init f = init := emptyStep' Nat.le.refl

-- We can decompose a for loop range into two parts and execute them separately
-- The results are only stated for `Id` monad, not sure how to generalise
theorem rangeDecompose [Monad m] [LawfulMonad m]
  (start mid stop : ℕ) (hs : start ≤ mid ∧ mid ≤ stop)
  {f : ℕ → β → m (ForInStep β)} (hf : ∀ i r, SatisfiesM ForInStep.isYield' (f i r)) :
  Range.forIn [start:stop] init f =
    Range.forIn [start:mid] init f >>= λ b => Range.forIn [mid:stop] b f := by
  sorry

-- The results are only stated for `Id` monad, not sure how to generalise
-- theorem singleStep (start stop : ℕ) (hs : start ≤ stop) {f : ℕ → β → Id (ForInStep β)} :
--   Range.forIn (mkRange' start stop.succ) init f =
--     f stop (Id.run (Range.forIn (mkRange' start mid) init f)) := by
--   sorry

end Std.Range

private def ff := λ i r => if i ≥ 100 then ForInStep.done (r + 1) else ForInStep.yield (r + 1)

#eval Id.run (Range.forIn { start := 3, stop := 13 } 5 ff)
#eval Id.run (Range.forIn { start := 93, stop := 103 } 5 ff)