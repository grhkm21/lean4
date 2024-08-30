import Mathlib.Tactic

variable {S G : Type*} [Group G] [SetLike S G]

/-- `GroupConeClass S G` says that `S` is a type of cones in `G`. -/
@[to_additive]
class GroupConeClass extends SubmonoidClass S G : Prop where
  -- eq_one_of_mem_of_inv_mem {C : S} {a : G} : a ∈ C → a⁻¹ ∈ C → a = 1
  asdf {C : S} {a : G} : a ∈ C → a⁻¹ ∈ C
