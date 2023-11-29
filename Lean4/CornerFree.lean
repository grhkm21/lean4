import Mathlib.Tactic

open Nat hiding log

open Finset Real

open scoped BigOperators

namespace BenGreen

variable {α : Type*} [DecidableEq α] [CommGroup α] {s t : Finset α}

@[to_additive "poggers"]
def MulCornerFree (s : Set (α × α)) : Prop :=
  ∀ x y d, (x, y) ∈ s → (x * d, y) ∈ s → (x, y * d) ∈ s → d = 1

-- This is not computable, but is decidable
@[to_additive "poggie"]
def MulCornerFree' (s : Set (α × α)) : Prop :=
  ∀ x y x' y' d, (x, y) ∈ s → (x', y) ∈ s → (x, y') ∈ s → x' = x * d → y' = y * d → d = 1

@[to_additive "poggies"]
theorem MulCornerFree_iff_MulCornerFree' (s : Set (α × α)) :
  MulCornerFree s ↔ MulCornerFree' s :=
by
  dsimp [MulCornerFree, MulCornerFree']
  exact ⟨fun h x y x' y' d h₁ h₂ h₃ hx hy ↦ h x y d h₁ (hx ▸ h₂) (hy ▸ h₃),
    fun h x y d h₁ h₂ h₃ ↦ h x y (x * d) (y * d) d h₁ h₂ h₃ rfl rfl⟩

@[to_additive]
instance (s : Finset (α × α)) [DecidableEq α] :
  Decidable (MulCornerFree' (s : Set (α × α))) :=
by
  sorry

@[to_additive]
instance (s : Finset (α × α)) [DecidableEq α] : Decidable (MulCornerFree (s : Set (α × α))) :=
  decidable_of_iff
    (MulCornerFree' (s : Set (α × α)))
    (MulCornerFree_iff_MulCornerFree' (s : Set (α × α))).symm

@[to_additive "also poggers"]
noncomputable def mulCornerFreeNumber (s : Finset (α × α)) : ℕ :=
  Nat.findGreatest (fun m => ∃ (t : _) (_ : t ⊆ s), t.card = m ∧ MulCornerFree (t : Set (α × α))) s.card

end BenGreen

section asdf

variable {α : Type*}

def MyProp (s : Finset α) : Prop := ∀ a : α, a ∈ s

end asdf

