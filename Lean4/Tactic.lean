import Mathlib.Tactic

/- Implementing and_then -/
syntax tactic " and_then " tactic : tactic
macro_rules
| `(tactic| $a:tactic and_then $b:tactic) =>
    `(tactic| $a:tactic ; all_goals $b:tactic)

example : 1 = 1 ∧ 2 = 2 := by apply And.intro and_then rfl

/- Implementing sorry -/
elab "custom_sorry_0" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalDecl ← goal.getDecl
    let goalType := goalDecl.type
    dbg_trace f!"goal type: {goalType}"
    /- Fill sorry -/
    Lean.Elab.admitGoal goal
    return

example : 1 = 2 := by custom_sorry_0

/- Implementing assumption -/
open Lean.Elab.Tactic in
elab "custom_assump" : tactic =>
  withMainContext do
    let goal ← getMainGoal
    let goalType ← getMainTarget
    let ctx ← Lean.MonadLCtx.getLCtx
    let expr ← ctx.findDeclM? fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr
      let declType ← Lean.Meta.inferType declExpr
      if (← Lean.Meta.isExprDefEq declType goalType)
      then return some declExpr
      else return none
    match expr with
    | some e => closeMainGoal e
    | none =>
        Lean.Meta.throwTacticEx `custom_assump goal
          (m!"unable to find matching hypothesis of type ({goalType})")

example (H1 : 1 = 1) (H2 : 2 = 2) : 2 = 2 := by custom_assump
example (H1 : 1 = 1) : 2 = 2 := by custom_assump

/- Implementing let and have -/
open Lean.Elab.Tactic in
elab "custom_let " n:ident " : " t:term " := " v:term : tactic =>
  withMainContext do
    let t ← elabTerm t none
    let v ← elabTermEnsuringType v t
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.define n.getId t v
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

open Lean.Elab.Tactic in
elab "custom_have " n:ident " : " t:term " := " v:term : tactic =>
  withMainContext do
    let t ← elabTerm t none
    let v ← elabTermEnsuringType v t
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.assert n.getId t v
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

example : True := by
  custom_let n : ℕ := 5
  custom_have h : n = n := rfl
  trivial

/- Reversing the goals to demonstrate getGoals and setGoals -/
open Lean.Elab.Tactic in
elab "reverse_goals" : tactic => do
  let goals ← getGoals
  setGoals goals.reverse

example : (1 = 2 ∧ 3 = 4) ∧ 5 = 6 := by
  constructor
  constructor
  reverse_goals
  sorry

/- Write a tactic that expands everything -/
example {x : ℤ} : x * x + 2 * x + 1 = (x + 1) ^ 2 := by
  ring_nf
