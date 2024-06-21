import Mathlib.RepresentationTheory.Character
import Mathlib.RingTheory.SimpleModule
import Mathlib.RingTheory.RootsOfUnity.Basic

open LinearMap Module Submodule Representation FiniteDimensional Function Pointwise CategoryTheory
  MonoidAlgebra

variable (n : ℕ) (hn : 1 < n) {𝕜 : Type} [Field 𝕜] (ζ : primitiveRoots n 𝕜)

example {k : ℕ} : (FGModuleCat.of 𝕜 𝕜) → (FGModuleCat.of 𝕜 𝕜) :=
  -- Without the cast rfl it doesn't work, even when marking as (x : 𝕜)
  fun x ↦ (cast rfl x : 𝕜) * (ζ.val : 𝕜) ^ k

theorem aux (f : (FGModuleCat.of 𝕜 𝕜).obj →ₗ[𝕜] (FGModuleCat.of 𝕜 𝕜).obj) :
    f = (1 : End (FGModuleCat.of 𝕜 𝕜)) ↔ f.toFun = _root_.id := by
  constructor <;> intro h
  · subst h; ext; simp; exact CategoryTheory.id_apply _
  · ext; change f.toFun _ = _; rw [h]; rfl

@[ext] theorem af (f g : End (FGModuleCat.of 𝕜 𝕜)) (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; congr!; simpa using h

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

example : FdRep 𝕜 (Multiplicative (ZMod n)) where
  V := FGModuleCat.of 𝕜 𝕜
  ρ := by
    refine MonCat.ofHom <| MonoidHom.mk (OneHom.mk ?_ ?_) ?_
    · intro k
      refine ⟨⟨fun x ↦ (cast rfl x : 𝕜) * ζ.val ^ k.val, ?_⟩, ?_⟩
      · intros; simp [add_mul]
      · intros; simp [← mul_assoc]
    · have : (1 : Multiplicative (ZMod n)).val = 0 := (ZMod.val_eq_zero _).mpr rfl
      rw [aux]; ext; simp [this]
    · intro x y; ext z; simp
      sorry

