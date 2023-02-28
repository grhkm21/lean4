import Mathlib.Data.Nat.Basic

def ff (n : ℕ) : ℕ := Id.run do
  let mut r := 0
  for _ in [: n] do
    r ← r + 1
  return r

theorem ff' : ff n = n := by
  simp [ff, forIn, Std.Range.forIn]
  let rec foo : ∀ fuel a, fuel + a = n →
      Id.run (Std.Range.forIn.loop (fun x r => ForInStep.yield (r + 1)) fuel a n 1 a) = n
  | 0, a, h => by simp [Std.Range.forIn.loop]; rwa [Nat.zero_add] at h
  | fuel+1, a, h => by
    simp [Std.Range.forIn.loop]; split
    · next h' => exact le_antisymm (h ▸ Nat.le_add_left ..) h'
    · next h' => rw [← Nat.add_right_comm] at h; exact foo _ _ h
  exact foo _ _ rfl

theorem ff'' : ff n = n := by
  simp [ff, forIn, Std.Range.forIn]
  sorry