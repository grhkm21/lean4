import Std.Data.Nat.Lemmas
import Mathlib.Data.Nat.Basic
import Lean.Meta
/- import Lean4.Test3 -/
/- import Lean4.cp -/
import Lean4.Tactic
/- import Lean4.IUM2023.Sheet1 -/
/- import Lean4.IUM2023.cp -/

def f (n : ℕ) : ℕ := Id.run do
  let mut r := 0
  for _ in [:n] do
    r ← r + 1
  return r

-- f fuel i stop step (ret val)
theorem f' (n : ℕ) : f n = n := by
  simp [f, forIn, Std.Range.forIn]
  let rec thm : ∀ fuel i k : ℕ, fuel + i = k →
    Id.run (Std.Range.forIn.loop (fun x r => ForInStep.yield (r + 1)) fuel i k 1 i) = k
  | 0, a, h₀=> by
    intro h'
    simp [h', Std.Range.forIn.loop, Id.run]
    rw [← h', Nat.zero_add a, Eq.refl a]
  | fuel+1, a, h₀ => by
    simp [Std.Range.forIn.loop]; split
    {
      intro h'
      have h₁ : ∀ x y z : ℕ, x + y = z → y ≤ z := by simp [Nat.le_add_left]
      simp [Id.run, le_antisymm (h₁ (fuel + 1) a h₀ h'), *]
    }
    {
      intro h'
      push_neg at *
      rw [← Nat.add_right_comm, Nat.add_assoc] at h'
      exact thm fuel (a + 1) _ h'
    }
  exact thm n 0 n (by simp)


def g : Std.Range := { start := 0, stop := 1, step := 1 }

#print f
#print g
#print Std.Range.forIn.loop

def main (args : List String) : IO Unit :=
  IO.println args
