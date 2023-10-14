import Mathlib.Tactic

example (p q r : Prop) (hpqr : p ∧ q ∧ r) : r ∧ q ∧ p := by
  have hp : p := hpqr.left
  have hq : q := hpqr.right.left
  have hr : r := hpqr.right.right
  exact And.intro hr (And.intro hq hp)

example (p q r : Prop) (hpqr : p ∧ q ∧ r) : r ∧ q ∧ p := by
  have hp : p := hpqr.left
  have hq : q := hpqr.right.left
  have hr : r := hpqr.right.right
  apply And.intro
  · exact hr
  · apply And.intro
    · exact hq
    · exact hp

example (p q r : Prop) (hpqr : p ∧ q ∧ r) : r ∧ q ∧ p := ⟨hpqr.2.2, hpqr.2.1, hpqr.1⟩

/- example {P : ℕ → Prop} (hP :  -/

example {h : ℕ → Prop} (hh : h 0) (hind : ∀ n, h n → h (n + 1)) : ∀ n, h n := by
  intro n
  induction' n with n hn
  · exact hh
  · specialize hind n hn
    exact hind
