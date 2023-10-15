import Mathlib.Tactic

def f (α : Type) := ∀ a : α, a = a

noncomputable instance [DecidableEq α] : Decidable (f α) := Classical.dec (f α)

instance [DecidableEq α] [Fintype α] : Decidable (f α) := inferInstanceAs (Decidable (∀ _, _))

#eval f ℚ
#eval f ({1, 2, 3} : Finset ℤ)
