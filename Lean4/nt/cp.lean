import Mathlib.Tactic

open Nat ArithmeticFunction

example [Ring α] (f : ArithmeticFunction α) : f 0 = 0 :=
  by apply f.map_zero'
