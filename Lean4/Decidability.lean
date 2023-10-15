import Mathlib.Tactic

variable (α : Type*) [DecidableEq α] [LinearOrder α] [Coe α ℚ] [Fintype α]

def MyProp : Prop := ∀ a : α, (0 : ℚ) < a

instance : Decidable (MyProp α) := inferInstanceAs (Decidable (∀ _, _))

def S : Finset ℚ := {0, 2, 4, 6, 8}

/- Works -/
instance : Coe S ℚ where
  coe := fun x => x

/- Errors -/
instance ApparentlyICanNameThis {T : Finset ℚ} : Coe T ℚ where
  coe := fun x => x

#check ApparentlyICanNameThis

#eval MyProp S
#eval MyProp ({1, 2, 3, 4, 5} : Finset ℚ)
