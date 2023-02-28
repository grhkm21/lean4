import Mathlib.Control.Random

def f1 := IO.runRand $ @Random.randFin _ 50 _
-- #eval (Array.range 100).map (λ k => IO.runRandWith k (@Random.randFin _ 100 _))