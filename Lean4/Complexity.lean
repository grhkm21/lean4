import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi

import Mathlib.Tactic.SlimCheck
import Mathlib.Testing.SlimCheck.Functions
import Lean4.Sampleable

open Finset

abbrev BooleanHypercube (n : Nat) : Type := Fin n → Bool

abbrev BooleanFunction (n : Nat) : Type := BooleanHypercube n → Bool

instance {n} : Zero (BooleanHypercube n) := ⟨fun _ ↦ false⟩
instance {n} : One (BooleanHypercube n) := ⟨fun _ ↦ true⟩
instance {n} : Zero (BooleanFunction n) := ⟨fun _ ↦ false⟩
instance {n} : One (BooleanFunction n) := ⟨fun _ ↦ true⟩

example {m : Nat} (g : BooleanFunction m) : g 0 = false := by
  slim_check

set_option trace.Meta.synthInstance true in
#synth SlimCheck.Testable (SlimCheck.NamedBinder "m"
  (∀ {m : ℕ}, SlimCheck.NamedBinder "g" (∀ (g : BooleanFunction m), g 0 = false)))

#sample 

variable {n : Nat} (f : BooleanFunction n) (X : BooleanHypercube n)

/- (Local) Certificate complexity: C(f, X) := smallest subset S ⊆ [n] such that
  if Y_i = X_i for all i ∈ S, then f(Y) = f(X) -/
abbrev Certificate (n : Nat) := Finset (Fin n)

def IsLocalCertificate (S : Certificate n) : Prop := ∀ Y, (∀ i ∈ S, Y i = X i) → f Y = f X

@[simp] theorem isLocalCertificate_def (S : Certificate n) :
    IsLocalCertificate f X S ↔ ∀ Y, (∀ i ∈ S, Y i = X i) → f Y = f X := by
  rfl

instance : DecidablePred (IsLocalCertificate f X) := by intro; simp; infer_instance

def LocalCertificateComplexity :=
    (((univ : Finset (Certificate n)).filter (IsLocalCertificate f X)).image card).min

set_option trace.Meta.synthInstance true in
example : LocalCertificateComplexity f X ≤ n := by
  slim_check

