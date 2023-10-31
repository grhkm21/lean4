import Mathlib.Tactic

instance KevinsDecidableInstance (n : ℕ) (R : ℕ → Prop) (h : ∀ a ≤ n, Decidable (R a)) : Decidable (∀ a ≤ n, R a) :=
match n, R, h with
| 0, _, h =>
  match h 0 $ Nat.le_refl 0 with
  | isFalse h' => isFalse (h' $ · 0 $ Nat.le_refl 0)
  | isTrue h' => isTrue (fun _ ha ↦ (Nat.le_zero.mp ha).symm ▸ h')
| (n + 1), R, h =>
  match KevinsDecidableInstance n R (fun a ha ↦ h a $ Nat.le_step ha) with
  | isFalse h' => isFalse fun ht ↦ h' fun a ha ↦ ht a $ Nat.le_step ha
  | isTrue h' =>
    match h (n + 1) $ Nat.le_refl _ with
    | isFalse p => isFalse fun ha ↦ p $ ha (n + 1) $ Nat.le_refl _
    | isTrue p => isTrue fun _ ha ↦ ha.lt_or_eq_dec.elim (h' _ $ Nat.le_of_lt_succ ·) (·.symm ▸ p)

/- instance decidableBallLT : -/
/-   ∀ (n : Nat) (P : ∀ k, k < n → Prop) [∀ n h, Decidable (P n h)], Decidable (∀ n h, P n h) -/
/- | 0, _, _ => isTrue fun _ => (by cases ·) -/
/- | (n+1), P, H => -/
/-   match decidableBallLT n (P · <| Nat.lt_succ_of_lt ·) with -/
/-   | isFalse h => isFalse (h fun _ _ => · _ _) -/
/-   | isTrue h => -/
/-     match H n Nat.le.refl with -/
/-     | isFalse p => isFalse (p <| · _ _) -/
/-     | isTrue p => isTrue fun _ h' => (Nat.le_of_lt_succ h').lt_or_eq_dec.elim (h _) (· ▸ p) -/

#check Nat.decidableForallFin
#check Nat.decidableBallLe
#check Nat.decidableBallLT
#check decidable_of_iff
#check decidable_of_decidable_of_iff
#check decidable_of_decidable_of_eq
