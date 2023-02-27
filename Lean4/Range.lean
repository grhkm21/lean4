import Mathlib.Data.Nat.Basic

/-
A summary of this file (27 Feb 2023):
* Rewrite `Std.Range.forIn` to remove `fuel` variable
* Change the result of a for-range loop with `step := 0` to do nothing
  * It used to run the loop `stop - start` times, which makes no sense
* Add some results about internals of Range and For to aid proofs
-/

open Std Std.Range

variable {β : Type u} {m : Type u → Type v} [Monad m]

def mkRange (start stop step : ℕ) : Range := { start := start, stop := stop, step := step }

def mkRange' (start stop : ℕ) : Range := { start := start, stop := stop }

def ForInStep.isDone (range : ForInStep β) : Bool :=
match range with
| .done _ => true
| _ => false

def ForInStep.isYield (range : ForInStep β) : Bool :=
match range with
| .yield _ => true
| _ => false

def ForInStep.extractStep (s : ForInStep β) : m β :=
  match s with
    | ForInStep.done b => pure b
    | ForInStep.yield b => pure b

theorem ForInStep.isDoneOrIsYield (range : ForInStep β) : range.isDone ∨ range.isYield := by
  cases range <;> simp [isDone, isYield]

theorem ForInStep.notIsDoneAndIsYield (range : ForInStep β) : ¬(range.isDone ∧ range.isYield) := by
  cases range <;> simp [isDone, isYield]

namespace STD

-- Syntax: `loop f i stop step b hs`
def loop (f : Nat → β → m (ForInStep β))
  (i stop step : Nat) (b : β) (hs : 0 < step) : m β := do
  if h : stop ≤ i then
    return b
  else
    have : stop - (i + step) < stop - i := by
      rw [← Nat.sub_sub]
      apply Nat.sub_lt _ hs
      exact Nat.zero_lt_sub_of_lt (lt_of_not_ge h)
    match (← f i b) with
    | ForInStep.done b  => pure b
    | ForInStep.yield b => loop f (i + step) stop step b hs
  termination_by _ => stop - i

-- Syntax: `forIn range init f`
protected def forIn (range : Range) (init : β)
  (f : Nat → β → m (ForInStep β)) : m β := do
  if hs : range.step = 0 then
    return init
  else
    loop f range.start range.stop range.step init (Nat.pos_iff_ne_zero.2 hs)

/-
Results about `loop`
-/
theorem emptyStep' {start stop : ℕ} {init : β} {f : ℕ → β → Id (ForInStep β)} (hs : stop ≤ start) :
  loop f start stop 1 init (Nat.zero_lt_one) = init := by
  cases start <;> rw [loop]
  simp [hs, Nat.le_zero.1 hs]
  simp [hs]

theorem emptyStep {k : ℕ} {init : β} {f : ℕ → β → Id (ForInStep β)} :
  STD.forIn (mkRange' k k) init f = init := emptyStep' Nat.le.refl

-- We can decompose a for loop range into two parts and execute them separately
-- The results are only stated for `Id` monad, not sure how to generalise
-- This only holds for if the loop 
theorem rangeDecompose (start mid stop : ℕ) (hs : start ≤ mid ∧ mid ≤ stop)
  {f : ℕ → β → Id (ForInStep β)} (hf : ∀ i r, (f i r).isYield) :
  STD.forIn (mkRange' start stop) init f =
    STD.forIn (mkRange' mid stop) (Id.run (STD.forIn (mkRange' start mid) init f)) f := by
  sorry

-- The results are only stated for `Id` monad, not sure how to generalise
-- theorem singleStep (start stop : ℕ) (hs : start ≤ stop) {f : ℕ → β → Id (ForInStep β)} :
--   STD.forIn (mkRange' start stop.succ) init f =
--     f stop (Id.run (STD.forIn (mkRange' start mid) init f)) := by
--   sorry

def ff := λ i r => if i ≥ 100 then ForInStep.done (r + 1) else ForInStep.yield (r + 1)

#eval Id.run (STD.forIn { start := 3, stop := 13 } 5 ff)
#eval Id.run (STD.forIn { start := 93, stop := 103 } 5 ff)

end STD