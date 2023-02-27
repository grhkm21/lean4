import Mathlib.Data.Nat.Basic

namespace STD

structure Range where
  start : Nat := 0
  stop  : Nat
  step  : Nat := 1

/-
Setup notation
-/

syntax : max (name := Range1) "[" withoutPosition(":" term) "]" : term
syntax : max (name := Range2) "[" withoutPosition(term ":" term) "]" : term
syntax : max (name := Range3) "[" withoutPosition(":" term ":" term) "]" : term
syntax : max (name := Range4) "[" withoutPosition(term ":" term ":" term) "]" : term

macro_rules (kind := Range1)
  | `([ : $stop]) => `({ stop := $stop : Range })
macro_rules (kind := Range2)
  | `([ $start : $stop ]) => `({ start := $start, stop := $stop : Range })
macro_rules (kind := Range3)
  | `([ : $stop : $step ]) => `({ stop := $stop, step := $step : Range })
macro_rules (kind := Range4)
  | `([ $start : $stop : $step ]) => `({ start := $start, stop := $stop, step := $step : Range })

def mkRange (start stop step : ℕ) : Range := { start := start, stop := stop, step := step }

def mkRange' (start stop : ℕ) : Range := { start := start, stop := stop }

-- Syntax: `loop f i stop step b hs`
def loop {β : Type u} {m : Type u → Type v} [Monad m] (f : Nat → β → m (ForInStep β))
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
protected def forIn {β : Type u} {m : Type u → Type v} [Monad m] (range : Range) (init : β)
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
-- Only succ is specified here
theorem rangeDecompose (start mid stop : ℕ) :
  STD.forIn (mkRange' start stop) init f =
    STD.forIn (mkRange' mid stop) (Id.run (STD.forIn (mkRange' start mid) init f)) f := by
  sorry

theorem singleStep (start mid stop : ℕ) :
  STD.forIn (mkRange' start stop) init f =
    STD.forIn (mkRange' mid stop) (Id.run (STD.forIn (mkRange' start mid) init f)) f := by
  sorry

#eval Id.run (STD.forIn { start := 3, stop := 13 } 5 (λ _ r => ForInStep.yield (r + 1)))

end STD