import Mathlib.Algebra.Category.FGModuleCat.Basic

open Polynomial

variable (F : Type*) [Field F]

theorem aux_poly (f : F[X]) : {x : F | f.eval x = (0 : F)}.Finite := by
  sorry

theorem aux_sq (f : F[X]) : {x : F | f.eval x = (0 : F)}.Finite := by
  sorry

theorem aux_preimage_finite {α β : Type*} (f : α → β) (hf : ∀ b, (f ⁻¹' {b}).Finite)
    (s : Set β) (hs : s.Finite) : (f ⁻¹' s).Finite := by
  sorry

theorem aux1 (x : F) : {y : F | y ^ 2 = x}.Finite := by
  convert_to {y | (X ^ 2 - C x).eval y = (0 : F)}.Finite
  · simp [sub_eq_zero]
  · exact aux_poly F _

theorem aux1' (x : F) : {y : F | y ^ 2 ∈ ({x} : Set F)}.Finite :=
  aux1 F x

theorem aux2 (s : Set F) (hs : s.Finite) : {y : F | y ^ 2 ∈ s}.Finite :=
  aux_preimage_finite _ (aux1' F) _ hs

theorem asdf (f : F[X]) : {p : F × F | f.eval p.fst = (0 : F) ∧ p.snd ^ 2 = p.fst ^ 3}.Finite := by
  let first_coordinate := {x : F | f.eval x = (0 : F)}
  have h₁_finite : first_coordinate.Finite := aux_poly F f

  let second_coordinate := {y : F | ∃ x ∈ first_coordinate, y ^ 2 = x ^ 3}
  have h₂_finite : second_coordinate.Finite := by
    convert_to ((fun y ↦ y ^ 2) ⁻¹' ((fun x ↦ x ^ 3) '' first_coordinate)).Finite
    · change second_coordinate = {y : F | y ^ 2 ∈ (fun x ↦ x ^ 3) '' first_coordinate}
      ext t
      simp [second_coordinate, eq_comm]
    · exact aux2 _ _ (h₁_finite.image _)

  have h₁₂_finite : (first_coordinate ×ˢ second_coordinate).Finite := h₁_finite.prod h₂_finite

  apply Set.Finite.subset h₁₂_finite
  intro ⟨x, y⟩ hxy
  simp [first_coordinate, second_coordinate] at hxy ⊢
  tauto

#print axioms asdf
