import Mathlib

open Module

universe u

example {R V W : Type u} [Ring R] [AddCommGroup V] [AddCommGroup W] [Module R V] [Module R W]
    (h : V ≃ₗ[R] W) : Submodule R V ≃ Submodule R W where
  toFun M := M.map h
  invFun M := M.map h.symm
  left_inv _ := (Submodule.map_symm_eq_iff h).mpr rfl
  right_inv _ := (Submodule.map_symm_eq_iff h).mp rfl

example {R V W : Type u} [Ring R] [AddCommGroup V] [AddCommGroup W] [Module R V] [Module R W]
    (h : V ≃ₗ[R] W) : Submodule R V ≃ Submodule R W :=
  Submodule.orderIsoMapComap h
