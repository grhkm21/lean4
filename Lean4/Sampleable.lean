import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Testing.SlimCheck.Functions

open SlimCheck SampleableExt

variable {α : Type*} {β : α → Type*}

instance Finset.sampleableExt [DecidableEq α] [SampleableExt α] :
    SampleableExt (Finset α) where
  proxy := List (proxy α)
  sample := List.sampleableExt.sample
  interp := fun x ↦ (x.map interp).toFinset
