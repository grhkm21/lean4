import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

def E₈ : Matrix (Fin 8) (Fin 8) ℚ := !![
1,-1,0,0,0,0,0,0;
0,1,-1,0,0,0,0,0;
0,0,1,-1,0,0,0,0;
0,0,0,1,-1,0,0,0;
0,0,0,0,1,-1,0,0;
0,0,0,0,0,1,1,0;
-1/2,-1/2,-1/2,-1/2,-1/2,-1/2,-1/2,-1/2;
0,0,0,0,0,1,-1,0
]

def F₈ : Matrix (Fin 8) (Fin 8) ℚ := !![
1,1,1,1,1,1/2,0,1/2;
0,1,1,1,1,1/2,0,1/2;
0,0,1,1,1,1/2,0,1/2;
0,0,0,1,1,1/2,0,1/2;
0,0,0,0,1,1/2,0,1/2;
0,0,0,0,0,1/2,0,1/2;
0,0,0,0,0,1/2,0,-1/2;
-1,-2,-3,-4,-5,-7/2,-2,-5/2
]

theorem E₈_mul_F₈_eq_thing : E₈ * F₈ = !![
    1,0,0,0,0,0,0,0;
    0,1,0,0,0,0,0,0;
    0,0,1,0,0,0,0,0;
    0,0,0,1,0,0,0,0;
    0,0,0,0,1,0,0,0;
    0,0,0,0,0,1,0,0;
    0,0,0,0,0,0,1,0;
    0,0,0,0,0,0,0,1;
    ] := by
  rw [E₈, F₈]
  norm_num

theorem E₈_mul_F₈_eq_one : E₈ * F₈ = 1 := by
  convert E₈_mul_F₈_eq_thing
  rw [← Matrix.diagonal_one]
  ext i j
  by_cases h : i = j
  · subst h
    fin_cases i <;> norm_num
  · rw [Matrix.diagonal_apply_ne _ h]
    fin_cases i <;> fin_cases j <;> norm_num at h ⊢

theorem F₈_mul_E₈_eq_one : F₈ * E₈ = 1 := by
  rw [Matrix.mul_eq_one_comm, E₈_mul_F₈_eq_one]
