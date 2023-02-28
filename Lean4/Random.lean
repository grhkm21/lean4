import Mathlib.Control.Random

def f1 := Id.run do
  let r := (IO.runRand $ @Random.randFin _ 50 _).toIO
  return r

#eval f1
-- #eval (Array.range 100).map (λ k => IO.runRandWith k (@Random.randFin _ 100 _))