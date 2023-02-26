import Mathlib.Data.Nat.Basic

open Std.Range Std.Range.forIn

def ff (n : ℕ) : ℕ := Id.run do
  let mut r := 0
  for _ in [: n] do
    r ← r + 1
  return r

def incStep : ℕ → ℕ → Id (ForInStep ℕ) := λ _ r => ForInStep.yield (r + 1)

variable {m : Type u → Type v} [Monad m]

def mkRange (start stop step : ℕ) : Std.Range := { start := start, stop := stop, step := step }

def mkRange' (start stop : ℕ) : Std.Range := { start := start, stop := stop, step := 1 }

def extractStep (s : ForInStep β) : m β :=
  match s with
    | ForInStep.done b => pure b
    | ForInStep.yield b => pure b

-- We can decompose a for loop range into two parts and execute them separately
-- Only succ is specified here
theorem rangeDecompose (start mid stop : ℕ) :
  Std.Range.forIn (mkRange' start stop) init f =
    Std.Range.forIn (mkRange' mid stop) (Id.run (Std.Range.forIn (mkRange' start mid) init f)) f := by
  sorry

theorem singleStep (start mid stop : ℕ) :
  Std.Range.forIn (mkRange' start stop) init f =
    Std.Range.forIn (mkRange' mid stop) (Id.run (Std.Range.forIn (mkRange' start mid) init f)) f := by
  sorry

-- Interesting technicality - since the definition of `loop` depends on 0 < fuel, we have to cases
theorem emptyStep' {start stop : ℕ} {init : β} {f : ℕ → β → Id (ForInStep β)} (hs : stop ≤ start) :
  loop f fuel start stop 1 init = init := by
  cases start <;> cases fuel <;> simp [loop]
  intro hs'
  exfalso
  exact hs' (Nat.le_zero.1 hs)
  intro hs'
  exfalso
  exact (Nat.not_lt_of_le hs) hs'

theorem emptyStep {k : ℕ} {init : β} {f : ℕ → β → Id (ForInStep β)} :
  Std.Range.forIn (mkRange' k k) init f = init := emptyStep' Nat.le.refl

theorem singleIncStep {k : ℕ} : Std.Range.forIn (mkRange' k k.succ) init incStep = init + 1 := by
  simp [mkRange', Std.Range.forIn, loop, incStep, Nat.succ_eq_add_one,
        show (Nat.succ k ≤ k) = False by simp]
  exact emptyStep' Nat.le.refl

-- For a function that's independent of the loop variable
-- The result only depends on the number of iterations
-- Notes: In `f i r`, `i` is the loop variable and `r` is the "program state"
-- Notes: `Std.Range.forIn range init f`
-- TODO: Generalise `f` to `ℕ → β → Id (ForInStep β)` (I do not know how to do this)
theorem succInvariantLt {k : ℕ} {init : β} {f : ℕ → β → Id (ForInStep β)} (start stop skip : ℕ)
  (hf : ∀ i j : ℕ, f i = f j) (hs : start ≤ stop) : Std.Range.forIn (mkRange' start stop) init f
    = Std.Range.forIn (mkRange' (start + skip) (stop + skip)) init f := by
  cases' Nat.exists_eq_add_of_le hs with k hk
  rw [hk]
  induction k
  simp [emptyStep]
  simp [Nat.add_succ, Nat.succ_add]
  sorry

theorem succInvariant {k : ℕ} {init : β} {f : ℕ → β → Id (ForInStep β)} (start stop skip : ℕ)
  (hf : ∀ i j : ℕ, f i = f j) : Std.Range.forIn (mkRange' start stop) init f
    = Std.Range.forIn (mkRange' (start + skip) (stop + skip)) init f := by
  by_cases h : start < stop
  exact @succInvariantLt _ k init f start stop skip hf (Nat.le_of_lt h)
  simp [Std.Range.forIn, mkRange', emptyStep' (Nat.ge_of_not_lt h),
        emptyStep' (Nat.add_le_add_right (Nat.ge_of_not_lt h) skip)]

-- This is kind of an ad-hoc theorem for the simple program
-- Also, I have a question: `s` is a Nat here and the loop (RHS) is a `Id Nat`
-- How do they compare?
theorem stateInvariant {n : ℕ} (init : ℕ) :
  Id.run (Std.Range.forIn (mkRange' 0 n) init incStep) + 1
  = Std.Range.forIn (mkRange' 0 n.succ) init incStep := by
  induction' n with k hk
  -- n = 0
  simp [Id.run, Std.Range.forIn, incStep, loop]
  -- n = k → n = k + 1
  simp [Id.run] at *
  rw [rangeDecompose _ k.succ k.succ.succ, Id.run, ← hk, singleIncStep]

theorem ff' : ff n = n := by
  induction' n with k hk
  simp
  let h := (@stateInvariant k 0)
  simp [ff, Id.run, forIn, Std.Range.forIn, loop, ← succInvariant] at *
  simp [Id.run, incStep, mkRange', Std.Range.forIn] at h
  conv_rhs => rw [← hk, Nat.succ_eq_add_one, h]

example : ff 5 = 5 := ff'

#eval Id.run $ Std.Range.forIn { start := 0, stop := 200, step := 0 } 5 incStep