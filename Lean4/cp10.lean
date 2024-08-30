import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

open EisensteinSeries ModularForm UpperHalfPlane CongruenceSubgroup

noncomputable section

def E4 : ModularForm (Gamma 1) 4 := 60 • (eisensteinSeries_MF (N:= 1) (k := 4) (by decide) 0)

def E6 : ModularForm (Gamma 1) 6 := 140 • (eisensteinSeries_MF (N:= 1) (k := 6) (by decide) 0)

def e4 := DirectSum.of _ 4 E4

def e6 := DirectSum.of _ 6 E6

def delta := e4^3 - 27 • e6^2

