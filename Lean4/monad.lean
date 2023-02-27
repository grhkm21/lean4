import Mathlib.Data.Nat.Basic
import Lean4.Range

open Std STD

def ff (n : ℕ) : ℕ := Id.run do
  let mut r := 0
  for _ in [: n] do
    r ← r + 1
  return r

def incStep : ℕ → ℕ → Id (ForInStep ℕ) := λ _ r => ForInStep.yield (r + 1)

variable {m : Type u → Type v} [Monad m]

#print loop
-- loop f start stop 1 init (Nat.zero_lt_one) = init
theorem singleIncStep {k : ℕ} : STD.forIn (mkRange' k k.succ) init incStep = init + 1 := by
  simp [mkRange']
  rw [STD.forIn]
  simp
  rw [loop]
  simp [incStep, eq_false (Nat.not_succ_le_self k)]
  exact emptyStep' Nat.le.refl

-- For a function that's independent of the loop variable
-- The result only depends on the number of iterations
-- Notes: In `f i r`, `i` is the loop variable and `r` is the "program state"
-- Notes: `Std.Range.forIn range init f`
-- TODO: Generalise `f` to `ℕ → β → Id (ForInStep β)` (I do not know how to do this)
theorem succInvariantLt {k : ℕ} {init : β} {f : ℕ → β → Id (ForInStep β)} (start stop skip : ℕ)
  (hf : ∀ i j : ℕ, f i = f j) (hs : start ≤ stop) : STD.forIn (mkRange' start stop) init f
    = STD.forIn (mkRange' (start + skip) (stop + skip)) init f := by
  -- Proof idea: define new function g that's independent of index, then prove they're equivalent
  -- Then just prove it's the g applied stop - start times by induction
  let g := f 0
  have hf' : f = λ _ r => g r := by
    funext
    rw [hf _ 0]  
  cases' Nat.exists_eq_add_of_le hs with k hk
  rw [hk]
  induction' k with t ht
  simp [emptyStep]

  sorry

theorem succInvariant {k : ℕ} {init : β} {f : ℕ → β → Id (ForInStep β)} (start stop skip : ℕ)
  (hf : ∀ i j : ℕ, f i = f j) : STD.forIn (mkRange' start stop) init f
    = STD.forIn (mkRange' (start + skip) (stop + skip)) init f := by
  by_cases h : start < stop
  exact @succInvariantLt _ k init f start stop skip hf (Nat.le_of_lt h)
  simp [STD.forIn, mkRange', emptyStep' (Nat.ge_of_not_lt h),
        emptyStep' (Nat.add_le_add_right (Nat.ge_of_not_lt h) skip)]

-- This is kind of an ad-hoc theorem for the simple program
-- Also, I have a question: `s` is a Nat here and the loop (RHS) is a `Id Nat`
-- How do they compare?
theorem stateInvariant {n : ℕ} (init : ℕ) :
  Id.run (STD.forIn (mkRange' 0 n) init incStep) + 1
  = STD.forIn (mkRange' 0 n.succ) init incStep := by
  induction' n with k hk
  -- n = 0
  simp [Id.run, STD.forIn, incStep, mkRange']
  rw [loop, loop]
  simp [Id.run, STD.forIn, incStep, Nat.one_eq_succ_zero]
  rw [emptyStep' Nat.le.refl]
  -- n = k → n = k + 1
  simp [Id.run] at *
  rw [rangeDecompose _ k.succ k.succ.succ, Id.run, ← hk, singleIncStep]

theorem ff' : ff n = n := by
  induction' n with k hk
  simp
  let h := (@stateInvariant k 0)
  simp [ff, Id.run, STD.forIn, loop, ← succInvariant] at *
  simp [Id.run, incStep, mkRange', STD.forIn] at h
  conv_rhs => rw [← hk, Nat.succ_eq_add_one]
  sorry

example : ff 5 = 5 := ff'

#eval Id.run $ STD.forIn { start := 0, stop := 200, step := 0 } 5 incStep
#eval Id.run $ STD.forIn { start := 0, stop := 200, step := 1 } 5 incStep

def fff (n : ℕ) : ℕ := Id.run do
  let mut r := 0
  for _ in [0 : n : 0] do
    r ← r + 1
  return r
#eval fff 5

/-
**Test Functions**

Below are a bunch of test functions to ensure correctness - I hope.
-/
def f1 (n : ℕ) : ℕ := Id.run do
  let mut r := 0
  for i in [: 2 * n] do
    if i % 2 = 0 then
      continue
    if i = 2 * n then
      break
    r ← r + i
  return r

/-
forIn RANGE r fun i r =>
  let r := r;
  let __do_jp := fun r y =>
    let __do_jp := fun r y => do
      let r ← r + i
      let r : ℕ := r
      pure PUnit.unit
      pure (ForInStep.yield r);
    if i = 2 * n then pure (ForInStep.done r) -- `break`
    else do
      let y ← pure PUnit.unit
      __do_jp r y;
  if i % 2 = 0 then pure (ForInStep.yield r)  -- `continue`
  else do
    let y ← pure PUnit.unit
    __do_jp r y
-/

#print f1
#eval f1 50