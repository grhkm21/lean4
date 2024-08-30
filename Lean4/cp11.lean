import Mathlib.Tactic
import Mathlib.ModelTheory.Order

open FirstOrder Language

variable {L : Language} {α : Type*}

#check Uncountable
example (f : α → ℕ) : L.Term α → ℕ
  | .var a => f a
  | .func _ _ => 0 -- can ignore

noncomputable example [Countable α] : α ↪ ℕ :=
  ⟨Classical.choose (Countable.exists_injective_nat α),
    Classical.choose_spec (Countable.exists_injective_nat α)⟩

noncomputable example [Fintype α] : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
