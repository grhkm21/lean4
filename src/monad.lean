import Mathlib.Data.Nat.Basic

def ff (n : ℕ) : ℕ := Id.run do
  let mut r := 0
  for _ in [: n] do
    r ← r + 1
  return r

-- For a function that's independent of the loop variable
-- The result only depends on the number of iterations
-- Notes: In `f i r`, `i` is the loop variable and `r` is the "program state"
-- Notes: `Std.Range.forIn.loop f fuel i stop step b`
theorem succ_invariant {β : Type u} {m : Type u → Type v} {b : β} [Monad m]
(f : ℕ → β → m (ForInStep β)) (hf : ∀ i j : ℕ, f i = f j) :
  Std.Range.forIn.loop f k 0 k 1 b = Std.Range.forIn.loop f k 1 (k + 1) 1 b := by
  sorry

def incStep : ℕ → ℕ → Id (ForInStep ℕ) := λ _ r => ForInStep.yield (r + 1)

-- This is kind of an ad-hoc theorem for the simple program
-- Also, I have a question: `s` is a Nat here and the loop (RHS) is a `Id Nat`
-- How do they compare?
theorem state_invariant {s : ℕ} (h : s = Std.Range.forIn.loop incStep k 0 k 1 0) :
  s + 1 = Std.Range.forIn.loop incStep k 0 k 1 1 := by
  sorry

theorem ff' : ff n = n := by
  induction' n with k hk
  simp
  simp [ff, Id.run, forIn, Std.Range.forIn, Std.Range.forIn.loop, ← succ_invariant] at *
  exact (state_invariant hk.symm).symm