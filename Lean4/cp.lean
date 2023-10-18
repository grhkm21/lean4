import Mathlib.Tactic

theorem thm1 {ι : Type*} [SeminormedAddCommGroup ι] : 1 = 0 := sorry

/-
▶ 5:86-5:90: error:
typeclass instance problem is stuck, it is often due to metavariables
  SeminormedAddCommGroup ?m.131
-/
example {ι : Type*} [h : SeminormedAddCommGroup ι] (f : ℕ → ι) : f 1 = f 0 := by rw [thm1]

/- Works -/
example {ι : Type*} [h : SeminormedAddCommGroup ι] (f : ℕ → ι) : f 1 = f 0 := by rw [@thm1 _ h]
