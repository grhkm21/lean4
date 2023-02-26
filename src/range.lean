import Mathlib.Data.Nat.Basic

namespace Std'

structure Range where
  start : Nat := 0
  stop  : Nat
  step  : Nat := 1

def loop {β : Type u} {m : Type u → Type v} [Monad m] (i stop step : Nat) (b : β) (f : Nat → β → m (ForInStep β)) (hs : 0 < step) : m β := do
  if h : i ≥ stop then
    return b
  else
    have : stop - (i + step) < stop - i := by
      rw [← Nat.sub_sub]
      apply Nat.sub_lt _ hs
      exact Nat.zero_lt_sub_of_lt (lt_of_not_ge h)
    match (← f i b) with
    | ForInStep.done b  => pure b
    | ForInStep.yield b => loop (i + step) stop step b f hs
  termination_by _ => stop - i

def forIn {β : Type u} {m : Type u → Type v} [Monad m] (range : Range) (init : β)
  (f : Nat → β → m (ForInStep β)): m β := do

  if hs : range.step = 0 then
    return init
  else
    loop range.start range.stop range.step init f (Nat.pos_iff_ne_zero.2 hs)

-- pls check this is 15
def incStep : ℕ → ℕ → Id (ForInStep ℕ) := λ _ r => ForInStep.yield (r + 1)

#eval Id.run (forIn { start := 3, stop := 13 } 5 incStep)