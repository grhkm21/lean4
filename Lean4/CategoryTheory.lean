import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Functor.Currying

open CategoryTheory Category Opposite Prod

variable {C D : Type*} [Category C] [Category D] {X Y : C} {F G : C ⥤ D}
theorem prod_type_eq {x y : C} {w z : D} : ((x ⟶ y) × (w ⟶ z)) = ((x, w) ⟶ (y, z)) := rfl

theorem aux (f : X ⟶ Y) : IsIso f ↔ ∀ c, Function.Bijective (fun (g : c ⟶ X) ↦ g ≫ f) := by
  constructor <;> intro h
  · intro c
    obtain ⟨inv, ⟨h_inv₁, h_inv₂⟩⟩ := h.out
    rw [Function.bijective_iff_has_inverse]
    use · ≫ inv, ?_, ?_
    · intro g; simp only; rw [assoc, h_inv₁, comp_id]
    · intro g; simp only; rw [assoc, h_inv₂, comp_id]
  · obtain ⟨inv, h_inv⟩ := (h _).surjective (𝟙 Y)
    use inv, ?_, h_inv
    simp only at h_inv
    rw [← (h _).injective.eq_iff, assoc, h_inv, comp_id, id_comp]

lemma aux13 {p : (X ⟶ Y) → Prop} : (∀ c, p c) ↔ (∀ c : (op Y ⟶ op X), p c.unop) := by
  exact { mp := fun a c => a c.unop, mpr := fun a c => a { unop := c } }

example {f : X ⟶ Y} : IsIso f ↔ (∀ c, Function.Bijective (fun (g : Y ⟶ c) ↦ f ≫ g)) := by
  convert (isIso_op_iff _).symm.trans (aux f.op)
  constructor <;> intro h c
  · specialize h (unop c)
    rw [Function.bijective_iff_has_inverse] at h ⊢
    obtain ⟨inv, ⟨h_inv₁, h_inv₂⟩⟩ := h
    use fun h ↦ (inv h.unop).op, ?_, ?_
    · intro h; simpa using op_eq_iff_eq_unop.mpr (h_inv₁ _)
    · intro h; simpa using op_eq_iff_eq_unop.mpr (h_inv₂ _)
  · specialize h (op c)
    rw [Function.bijective_iff_has_inverse] at h ⊢
    obtain ⟨inv, ⟨h_inv₁, h_inv₂⟩⟩ := h
    use fun h ↦ (inv h.op).unop, ?_, ?_
    · intro h; simpa using unop_eq_iff_eq_op.mpr (h_inv₁ _)
    · intro h; simpa using unop_eq_iff_eq_op.mpr (h_inv₂ _)

local notation "𝟚" => Fin 2

def ι : (0 : 𝟚) ⟶ 1 := homOfLE $ zero_le_one (α := ℕ)

theorem zero_to_one_uniq {f : (0 : 𝟚) ⟶ 1} : f = ι := rfl

theorem no_one_to_zero (f : (1 : 𝟚) ⟶ 0) : False :=
  False.elim (Nat.not_succ_le_self 0 (leOfHom f))

/- Lemma 1.5.1 -/
@[ext] structure AuxType (F G) where
  toFunc : C × 𝟚 ⥤ D
  left : F = sectl C 0 ⋙ toFunc
  right : G = sectl C 1 ⋙ toFunc

@[simp] def aux151_1 (α : F ⟶ G) : AuxType F G where
  toFunc := {
    obj := fun c ↦ match c with
    | ⟨c, 0⟩ => F.obj c
    | ⟨c, 1⟩ => G.obj c
    map := @fun c c' f ↦ match c, c' with
    | ⟨c, 0⟩, ⟨c', 0⟩ => F.map f.fst
    | ⟨c, 0⟩, ⟨c', 1⟩ => α.app c ≫ G.map f.fst
    | ⟨c, 1⟩, ⟨c', 0⟩ => False.elim $ no_one_to_zero f.snd
    | ⟨c, 1⟩, ⟨c', 1⟩ => G.map f.fst
    map_id := fun ⟨c, ⟨x, _⟩⟩ ↦ match x with | 0 | 1 => by simp
    map_comp := @fun ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ f g ↦
      match hx, hy, hz with
      | 0, 0, 0 | 0, 0, 1 | 0, 1, 1 | 1, 1, 1 => by simp
      | 1, 0, 0 | 1, 0, 1 => False.elim $ no_one_to_zero f.snd
      | 0, 1, 0 | 1, 1, 0 => False.elim $ no_one_to_zero g.snd
  }
  left := by refine CategoryTheory.Functor.ext ?_ ?_ <;> simp
  right := by refine CategoryTheory.Functor.ext ?_ ?_ <;> simp

@[simp] def aux151_2' (H : AuxType F G) : sectl C 0 ⋙ H.toFunc ⟶ sectl C 1 ⋙ H.toFunc where
  app := fun c ↦ H.toFunc.map (𝟙 c, ι)
  naturality := by simp [← H.toFunc.map_comp]

@[simp] def aux151_2 (H : AuxType F G) : F ⟶ G := by
  convert aux151_2' H
  · exact H.left
  · exact H.right

open Classical Function

theorem aux151_left_inverse : LeftInverse aux151_1 (aux151_2 (F := F) (G := G)) := by
  rintro ⟨H, rfl, rfl⟩
  simp
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro c
    match c with | ⟨c, 0⟩ | ⟨c, 1⟩ => rfl
  · intro ⟨c, x⟩ ⟨c', y⟩ ⟨f, g⟩
    match x, y with
    | 0, 0 => simp; congr!
    | 0, 1 => simp [← Functor.map_comp, zero_to_one_uniq]
    | 1, 0 => exact False.elim $ no_one_to_zero g
    | 1, 1 => simp; congr!

theorem aux151_right_inverse : RightInverse aux151_1 (aux151_2 (F := F) (G := G)) :=
  fun α ↦ by ext c; simp

noncomputable def aux151 : (F ⟶ G) ≃ AuxType F G where
  toFun := aux151_1
  invFun := aux151_2
  left_inv := aux151_right_inverse
  right_inv := aux151_left_inverse

theorem nonempty_equiv_of_exists_bijective
    {α β : Type*} (hf : ∃ f : α → β, Function.Bijective f) :
    Nonempty (α ≃ β) :=
  let ⟨_, hf⟩ := hf; ⟨Equiv.ofBijective _ hf⟩

/- Basically currying: (A × B) → C = (B × A) → C = B → (A → C) -/
def amelia_1 : C × 𝟚 ⥤ D ≌ 𝟚 ⥤ C ⥤ D := (braiding C 𝟚).congrLeft.trans currying.symm

/- Functors from 𝟚 to C basically is arrows of C -/
def amelia_2 : 𝟚 ⥤ C ≃ (Σ c d : C, c ⟶ d) where
  toFun := fun H ↦ ⟨H.obj 0, H.obj 1, H.map ι⟩
  invFun := fun ⟨c, d, F⟩ ↦ {
    obj := fun x ↦ match x with | 0 => c | 1 => d
    map := @fun x y h ↦ match x, y with
    | 0, 0 => 𝟙 c
    | 0, 1 => F
    | 1, 0 => False.elim $ no_one_to_zero h
    | 1, 1 => 𝟙 d
    map_id := fun x ↦ match x with | 0 | 1 => by simp
    map_comp := @fun X Y Z _ _ ↦ match X, Y, Z with
    | 0, 0, 0 | 0, 0, 1 | 0, 1, 1 | 1, 1, 1 => by simp
    | 1, 0, 0 | 1, 0, 1 | 0, 1, 0 | 1, 1, 0 => False.elim $ no_one_to_zero (by assumption)
  }
  left_inv := fun H ↦ by
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro c; match c with | 0 | 1 => simp
    · intro c d F; match c, d with
      | 0, 0 => simp [show F = 𝟙 0 by rfl]
      | 0, 1 => simp; congr!
      | 1, 0 => exact False.elim $ no_one_to_zero F
      | 1, 1 => simp [show F = 𝟙 1 by rfl]
  right_inv := fun ⟨c, d, F⟩ ↦ by simp

