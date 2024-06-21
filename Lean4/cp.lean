/- import Mathlib -/
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Polynomial.Coeff
import Mathlib.RingTheory.Polynomial.Basic

example (R : Type*) [AddGroupWithOne R] [CharZero R] (a b : ℤ) (h : (a : R) = (b : R)) : a = b := by
  exact Int.cast_inj.mp h

example (a b c : ℝ) (hc : c ≠ 0) : a * c = b * c ↔ a = b := by
  exact mul_left_inj' hc

example {K : Type*} [Field K] (a b c : K) (h : a * c = b * c) (hc : c ≠ 0) : a = b := by
  exact (mul_left_inj' hc).mp h

#check Trunc
#check Quot.lift
#check Quot.recOn

example (f : α → β) [Subsingleton β] : Trunc α → β :=
  Quot.lift f (fun _ _ _ ↦ Subsingleton.allEq _ _)

example {P : Prop} : ¬(P ↔ ¬P) := fun ⟨f, g⟩ ↦ f (g fun p ↦ f p p) (g fun p ↦ f p p)

example : ∀ {x : ℕ}, x ^ 0 = 1 := by apply?
example : ∀ {x : ℕ}, x ^ 0 = 1 := by exact?
example : ∀ {x : ℕ}, x ^ 0 = 1 := exact?%

example {α : Type*} {motive : List α → Sort*}
    {xs : List α} (h : 0 < xs.length) (cons : ∀ a as, motive (a :: as)) : motive xs :=
  match xs with
  | [] => by simp at h
  | x :: xs => cons x xs
