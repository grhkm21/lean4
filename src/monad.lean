import Mathlib.Data.Nat.Basic

open Std.Range Std.Range.forIn

def ff (n : ℕ) : ℕ := Id.run do
  let mut r := 0
  for _ in [: n] do
    r ← r + 1
  return r

variable {m : Type u → Type v} [Monad m]

def mkRange (start stop step : ℕ) : Std.Range := { start := start, stop := stop, step := step }

def mkRange' (start stop : ℕ) : Std.Range := { start := start, stop := stop, step := 1 }

def extractStep (s : ForInStep β) : m β :=
  match s with
    | ForInStep.done b => pure b
    | ForInStep.yield b => pure b

-- For a function that's independent of the loop variable
-- The result only depends on the number of iterations
-- Notes: In `f i r`, `i` is the loop variable and `r` is the "program state"
-- Notes: `Std.Range.forIn range init f`
theorem succ_invariant {k : ℕ} {init : β} {f : ℕ → β → m (ForInStep β)}
  (hf : ∀ i j : ℕ, f i = f j) :
  Std.Range.forIn (mkRange' 0 k) init f
  = Std.Range.forIn (mkRange' 1 k.succ) init f := by
  sorry

-- We can decompose a for loop range into two parts and execute them separately
-- Only succ is specified here
theorem range_decompose {start mid stop : ℕ} :
  Std.Range.forIn (mkRange' start stop) init f =
    Std.Range.forIn (mkRange' mid stop) (Id.run (Std.Range.forIn (mkRange' start mid) init f)) f := by
  sorry

def incStep : ℕ → ℕ → Id (ForInStep ℕ) := λ _ r => ForInStep.yield (r + 1)

-- set_option pp.all true

-- Interesting technicality - since the definition of `loop` depends on 0 < fuel, we have to cases
theorem emptyStep' {k : ℕ} {init : β} {f : ℕ → β → Id (ForInStep β)} :
  loop f fuel k k 1 init = init := by
    cases k <;> cases fuel <;> simp [loop]

theorem emptyStep {k : ℕ} {init : β} {f : ℕ → β → Id (ForInStep β)} :
  Std.Range.forIn (mkRange' k k) init f = init := emptyStep'

theorem singleIncStep {k : ℕ} : Std.Range.forIn (mkRange' k k.succ) init incStep = init + 1 := by
  simp [mkRange', Std.Range.forIn, loop, incStep, Nat.succ_eq_add_one,
        show (Nat.succ k ≤ k) = False by simp]
  exact emptyStep'

theorem incStep_succ_invariant : ∀ i j : ℕ, incStep i = incStep j := by simp [incStep]

-- This is kind of an ad-hoc theorem for the simple program
-- Also, I have a question: `s` is a Nat here and the loop (RHS) is a `Id Nat`
-- How do they compare?
theorem state_invariant {n : ℕ} (init : ℕ) :
  Id.run (Std.Range.forIn (mkRange' 0 n) init incStep) + 1
  = Std.Range.forIn (mkRange' 0 n.succ) init incStep := by
  induction' n with k hk
  -- n = 0
  simp [Id.run, Std.Range.forIn, incStep, loop]
  -- n = k → n = k + 1
  simp [Id.run] at *
  rw [@range_decompose _ _ _ _ k.succ k.succ.succ, Id.run, ← hk, singleIncStep]

theorem ff' : ff n = n := by
  induction' n with k hk
  simp
  let h := (@state_invariant k 0)
  simp [ff, Id.run, forIn, Std.Range.forIn, loop, ← succ_invariant] at *
  simp [Id.run, incStep, mkRange', Std.Range.forIn] at h
  conv_rhs => rw [← hk, Nat.succ_eq_add_one, h]

example : ff 5 = 5 := ff'