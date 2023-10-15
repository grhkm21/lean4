import Mathlib.Tactic

open Nat

lemma l1 : List.map (xs.get) (List.finRange xs.length) = xs := by simp

example (xs : List ℕ) (f : ℕ → ℕ) :
  List.sum (List.map f xs) =
    List.sum ((List.finRange xs.length).map (f ∘ xs.get)) :=
by
  match xs with
  | [] => simp
  | x :: xs =>
      rw [List.map_cons, List.comp_map, l1, List.map_cons]

example : List.map (xs.get) (List.finRange xs.length) = xs := by simp

example [Ring α] {x : α} {xs : List α} : (x :: xs).sum = x + xs.sum := List.sum_cons
example : List.map (f ∘ g) ls = List.map f (List.map g ls) := List.comp_map f g ls

#eval List.map (Nat.add 1 ∘ Nat.mul 2) [1, 2, 3]
