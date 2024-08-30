import Mathlib.LinearAlgebra.Determinant

example : (1 : Matrix (Fin 8) (Fin 8) ℚ).det = 1 := by
  rw [Matrix.det_one]
