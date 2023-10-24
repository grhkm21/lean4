import Mathlib.Tactic
import Lean.Meta.Basic
import Lean.Parser.Term

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
/- example (H1 : 1 = 1) : 2 = 2 := by custom_assump -/

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
  all_goals sorry

/- Write a tactic that expands everything -/
example {x : ℤ} : x * x + 2 * x + 1 = (x + 1) ^ 2 := by
  ring_nf


open Lean
def bv0 : Expr := .bvar 0
#eval bv0
#eval toExpr true

#check Expr.app
#check mkApp2
#check mkAppN
#check mkLambdaEx
#eval toExpr (1 + 1)

def doo : MetaM Expr := do
  let me <- Meta.mkFreshExprMVar none
  let m := Lean.Expr.mvarId! me
  Lean.MVarId.assign m (toExpr (3 + 3))
  Lean.instantiateMVars me

elab "doo" : term => do
  let a <- doo
  return a

#check doo

-------------------------------------------------------------------------------------------

section myTacticSection

open Lean Meta Elab Elab.Tactic Elab.Term Std.Tactic.TryThis Parser Parser.Tactic

/- syntax "myTactic" (ppSpace colGt term)? : tactic -/
/- elab_rules : tactic -/
/- | `(tactic|myTactic $[$sop:term]?) => withMainContext do -/
/-   let stx ← getRef -/
/-   let expr ← match sop with -/
/-     | none => getMainTarget -/
/-     | some sop => do -/
/-       let tgt ← getMainTarget -/
/-       let ex := elabTermEnsuringType sop (← inferType tgt) -/
/-       let ex ← withRef sop ex -/
/-       /- if !(← isDefEq ex tgt) then throwErrorAt sop "The term{indentD ex}\nis not defeq to the goal:{indentD tgt}" -/ -/
/-       dbg_trace f!"tgt : {←delabToRefinableSyntax tgt}\n" -/
/-       dbg_trace f!"ex : {←delabToRefinableSyntax ex}" -/
/-       instantiateMVars ex -/
/-   let dstx ← delabToRefinableSyntax expr -/
/-   dbg_trace f!"\n\ndstx : {dstx}" -/

#check isExprDefEq
#check Parser.Term.syntheticHole

syntax "change'" term (ppSpace colGt location)? : tactic

/-- my change! -/
macro "change'" e:term : tactic => `(tactic| refine_lift show $e from ?_)

def f := fun x ↦ x + 1
def g := fun x ↦ x + 1
/-
def refineCore (stx : Syntax) (tagSuffix : Name) (allowNaturalHoles : Bool) : TacticM Unit := do
  withMainContext do
    let (val, mvarIds') ← elabTermWithHoles stx (← getMainTarget) tagSuffix allowNaturalHoles
    let mvarId ← getMainGoal
    let val ← instantiateMVars val
    if val == mkMVar mvarId then
      /- `val == mkMVar mvarId` is `true` when we've refined the main goal. Refining the main goal
      (e.g. `refine ?a` when `?a` is the main goal) is an unlikely practice; further, it shouldn't
      be possible to create new mvarIds during elaboration when doing so. But in the rare event
      that somehow this happens, this is how we ought to handle it. -/
      replaceMainGoal (mvarId :: mvarIds')
    else
      /- Ensure that the main goal does not occur in `val`. -/
      if val.findMVar? (· == mvarId) matches some _ then
        throwError "'refine' tactic failed, value{indentExpr val}\ndepends on the main goal metavariable '{mkMVar mvarId}'"
      mvarId.assign val
      replaceMainGoal mvarIds'

-> refineCore e `refine (allowNaturalHoles := false)
-/
set_option trace.profiler false
set_option pp.rawOnError false

syntax "introNames" (ppSpace colGt term) : tactic
elab_rules : tactic
| `(tactic|introNames $e:term) =>
  withMainContext do
    /- let te ← elabTerm (mayPostpone := true) e none -/
    /- match te with -/
    /- | Expr.mvar mvarId => do -/
    /-   let name := ((←getMCtx).decls.find! mvarId).userName -/
    /-   let a : Ident := mkIdent name -/
    /-   let ha : Ident := mkIdent $ name.appendBefore "h" -/
    /-   let goal ← getMainGoal -/
    /-   let val ← getMainTarget -/
    /-   let (fvar, goal) ← (←goal.define "A" (←inferType val) val).intro1P -/
    /-   replaceMainGoal [goal] -/
    /-   evalTactic (← `(tactic| try rewrite [show $(←Term.exprToSyntax val) = $a from rfl] at *)) -/
    /-   evalTactic (← `(tactic| have $ha : $a = $(←Term.exprToSyntax val) := rfl)) -/
    /-   dbg_trace f!"POGGERS!" -/
    /- | _ => throwError "RHS is not a hole" -/
    let (expr, mvarIds) ← elabTermWithHoles e none "suffix" (allowNaturalHoles := true)
    dbg_trace f!"target : {←delabToRefinableSyntax (←getMainTarget)}"
    dbg_trace f!"expr : {←delabToRefinableSyntax expr} | {expr}"
    dbg_trace f!"mvarIds : {repr mvarIds}"
    let target ← getMainTarget
    let res ← isDefEq target expr
    dbg_trace f!"res : {res}"

#eval show MetaM Unit from do
  let a ← Lean.Meta.mkFreshExprMVar (Expr.const `Nat []) (userName := `a)
  let ee := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkNatLit 2, a]
  let ff := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkNatLit 2, Lean.mkNatLit 1]
  dbg_trace f!"ee : {ee}\nff : {ff}"
  let isEqual ← Lean.Meta.isDefEq ee ff
  IO.println isEqual

example : 1 + (2 * (5 - 3)) = 5 := by
  setm ?A + ?B = 5
  norm_num
  done

example : (1 + 1) + (2 + 2) + (3 + 3) + (4 + 4) = 20 := by
  /- change' (1 + 1) + ?_ + ?_ + ?_ = ?_ -/
  /- convert (1 + 1) + ?_ + ?_ + ?_ = ?_ -/
  /-
  Intended use case:
  myTactic ?A + ?B + ?C + ?D = ?E

  which then
  1. Introduces definitions like hA : A := 1 + 1
  2. replaces the goal with that
  -/
  setm (?A : ℕ) + ?B + ?C + ?D = ?E
  norm_num
  done

example : ∀ x : ℕ, x = x := by unhygienic
  intro
  rfl

example : true ∧ true := by constructor <;> trivial

/-
macro "refine_lift " e:term : tactic => `(tactic| focus (refine no_implicit_lambda% $e; rotate_right))
macro "have " d:haveDecl : tactic => `(tactic| refine_lift have $d:haveDecl; ?_)
-/

end myTacticSection
