import Mathlib.RepresentationTheory.Character

open CategoryTheory Category BraidedCategory MonoidalCategory IsIso

universe u
variable {C : Type u} [Category C] [MonoidalCategory C] [BraidedCategory C]

/- yang baxter but with β_.inv instead of β_.hom.
Maybe there is a proof via duality, but proving it directly is just copy and pasting -/
theorem yang_baxter_inv (X Y Z : C) :
    (α_ X Y Z).inv ≫ (β_ Y X).inv ▷ Z ≫ (α_ Y X Z).hom
      ≫ Y ◁ (β_ Z X).inv ≫ (α_ Y Z X).inv ≫ (β_ Z Y).inv ▷ X ≫ (α_ Z Y X).hom
        = X ◁ (β_ Z Y).inv ≫ (α_ X Z Y).inv
          ≫ (β_ Z X).inv ▷ Y ≫ (α_ Z X Y).hom ≫ Z ◁ (β_ Y X).inv := by
  rw [← braiding_inv_tensor_left_assoc, ← cancel_mono (α_ Z Y X).inv]
  repeat rw [assoc]
  rw [Iso.hom_inv_id, comp_id, ← braiding_inv_naturality_right, braiding_inv_tensor_left]

theorem yang_baxter_inv' (X Y Z : C) :
    (β_ Y X).inv ▷ Z ⊗≫ Y ◁ (β_ Z X).inv ⊗≫ (β_ Z Y).inv ▷ X =
      𝟙 _ ⊗≫ (X ◁ (β_ Z Y).inv ⊗≫ (β_ Z X).inv ▷ Y ⊗≫ Z ◁ (β_ Y X).inv) ⊗≫ 𝟙 _ := by
  rw [← cancel_epi (α_ X Y Z).inv, ← cancel_mono (α_ Z Y X).hom]
  convert yang_baxter_inv X Y Z using 1
  all_goals coherence

/- Wow holy shit grhkm doing category theory -/
set_option maxHeartbeats 400000 in
example (X Y : C) [inst : ExactPairing X Y] : ExactPairing Y X where
  coevaluation' := η_ X Y ≫ (β_ Y X).inv
  evaluation' := (β_ X Y).hom ≫ ε_ X Y
  coevaluation_evaluation' := by
    /- Rearrange into _ = 𝟙 _ -/
    rw [Iso.eq_comp_inv, ← Iso.inv_comp_eq_id]
    /- Whitney trick transcribed: https://ncatlab.org/toddtrimble/published/Whitney+trick -/
    -- (ρ_ X).inv ≫ (X ◁ (η_ X Y ≫ (β_ Y X).inv) ≫ (α_ X Y X).inv ≫ ((β_ X Y).hom ≫ ε_ X Y) ▷ X) ≫ (λ_ X).hom
    /- calc -/
    /-   _ = (λ_ X).inv ≫ (β_ X (𝟙_ C)).inv ≫ X ◁ η_ X Y ⊗≫ (β_ X X).hom ▷ Y ≫ (β_ X X).inv ▷ Y ⊗≫ X ◁ (β_ Y X).inv ⊗≫ (β_ X Y).hom ▷ X ≫ ε_ X Y ▷ X ≫ (λ_ X).hom := by -/
    /-     simp [monoidalComp] -/
    /-   _ = (λ_ X).inv ≫ η_ X Y ▷ X ⊗≫ (X ◁ (β_ X Y).inv ⊗≫ (β_ X X).inv ▷ Y ⊗≫ X ◁ (β_ Y X).inv) ⊗≫ (β_ X Y).hom ▷ X ≫ ε_ X Y ▷ X ≫ (λ_ X).hom := by -/
    /-     rw [monoidalComp, ← braiding_inv_naturality_left_assoc _ X, braiding_inv_tensor_right] -/
    /-     simp -/
    /-     coherence -/
    /-   _ = (λ_ X).inv ≫ η_ X Y ▷ X ⊗≫ ((β_ Y X).inv ▷ X ⊗≫ Y ◁ (β_ X X).inv ⊗≫ (β_ X Y).inv ▷ X) ≫ (β_ X Y).hom ▷ X ≫ ε_ X Y ▷ X ≫ (λ_ X).hom := by -/
    /-     rw [yang_baxter_inv'] -/
    /-     simp [monoidalComp] -/
    /-   _ = (λ_ X).inv ≫ η_ X Y ▷ X ⊗≫ (β_ Y X).inv ▷ X ⊗≫ Y ◁ (β_ X X).inv ⊗≫ ((β_ X Y).inv ▷ X ≫ (β_ X Y).hom ▷ X) ≫ ε_ X Y ▷ X ≫ (λ_ X).hom := by -/
    /-     simp only [monoidalComp, assoc] -/
    /-   _ = (λ_ X).inv ≫ η_ X Y ▷ X ⊗≫ (X ◁ ε_ X Y ≫ (β_ (𝟙_ C) X).inv) ≫ (λ_ X).hom := by -/
    /-     rw [inv_hom_whiskerRight _ X, braiding_inv_naturality_right, braiding_inv_tensor_left] -/
    /-     coherence -/
    /-   _ = (λ_ X).inv ≫ η_ X Y ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ε_ X Y ≫ (ρ_ X).hom := by -/
    /-     rw [assoc, braiding_inv_tensorUnit_left, assoc, Iso.inv_hom_id, comp_id] -/
    /-     coherence -/
    /-   _ = _ := by -/
    /-     rw [inst.evaluation_coevaluation_assoc] -/
    /-     simp -/
    calc
      _ = 𝟙 X ⊗≫ X ◁ η_ X Y ⊗≫ (X ◁ (β_ Y X).inv ⊗≫ (β_ X Y).hom ▷ X) ⊗≫ ε_ X Y ▷ X ⊗≫ 𝟙 X := by
        coherence
      _ = 𝟙 X ⊗≫ X ◁ η_ X Y ⊗≫ (𝟙 (X ⊗ X ⊗ Y) ⊗≫ (β_ X X).hom ▷ Y ⊗≫ X ◁ (β_ X Y).hom ⊗≫ (β_ Y X).inv ▷ X ⊗≫ Y ◁ (β_ X X).inv ⊗≫ 𝟙 ((Y ⊗ X) ⊗ X)) ⊗≫ ε_ X Y ▷ X ⊗≫ 𝟙 X := by
        congr 3
        simp [monoidalComp]
        rw [← IsIso.eq_inv_comp]
        /- I can't rewrite f = g₁ ≫ g₂ ≫ g₃ ≫ h to f ≫ h.inv = ... because it's the "inner layer" -/
        repeat rw [← assoc]
        iterate 5 rw [← comp_inv_eq]
        simpa using yang_baxter _ _ _
      _ = (𝟙 X ⊗≫ X ◁ η_ X Y ⊗≫ (β_ X X).hom ▷ Y ⊗≫ X ◁ (β_ X Y).hom) ⊗≫ (β_ Y X).inv ▷ X ⊗≫ Y ◁ (β_ X X).inv ⊗≫ ε_ X Y ▷ X ⊗≫ 𝟙 X := by
        coherence
      _ = (𝟙 X ⊗≫ η_ X Y ▷ X ⊗≫ 𝟙 (X ⊗ Y ⊗ X)) ⊗≫ (β_ Y X).inv ▷ X ⊗≫ Y ◁ (β_ X X).inv ⊗≫ ε_ X Y ▷ X ⊗≫ 𝟙 X := by
        congr 1
        simp [monoidalComp]
        rw [← cancel_mono (α_ X Y X).inv]
        simp [assoc, ← braiding_tensor_right]
      _ = 𝟙 X ⊗≫ η_ X Y ▷ X ⊗≫ ((β_ (Y ⊗ X) X).inv ≫ ε_ X Y ▷ X) ⊗≫ 𝟙 X := by
        simp [monoidalComp]
      _ = _ := by
        rw [← braiding_inv_naturality_right]
        simp [monoidalComp]

  evaluation_coevaluation' := by
    /- Rearrange into _ = 𝟙 _ -/
    rw [Iso.eq_comp_inv, ← Iso.inv_comp_eq_id]
    -- (λ_ Y).inv ≫ ((η_ X Y ≫ (β_ Y X).inv) ▷ Y ≫ (α_ Y X Y).hom ≫ Y ◁ ((β_ X Y).hom ≫ ε_ X Y)) ≫ (ρ_ Y).hom
    calc
      _ = (λ_ Y).inv ≫ η_ X Y ▷ Y ≫ (β_ Y X).inv ▷ Y ⊗≫ Y ◁ (β_ X Y).hom ≫ Y ◁ ε_ X Y ≫ (ρ_ Y).hom := by
        simp [monoidalComp]
      _ = (ρ_ Y).inv ≫ (β_ Y (𝟙_ C)).hom ≫ η_ X Y ▷ Y ≫ (β_ Y X).inv ▷ Y ⊗≫ Y ◁ (β_ X Y).hom ≫ Y ◁ ε_ X Y ≫ (ρ_ Y).hom := by
        simp [monoidalComp]

#check braiding_inv_tensorUnit_left

example {α : Type*} {p q : α → Prop} (a : { x // p x }) : { x // p x ∨ q x } := by
  apply?

#check Subtype
