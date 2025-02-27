import Lean
import Lean.Elab.Tactic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Defs

open Lean Elab Tactic

partial def generateSum {α : Expr} (n : Nat) : MetaM Expr := do
  -- Base case: if n = 1, return ?S1
  if n == 1 then
    Lean.Meta.mkFreshExprMVar α (userName := `S1)
  else
    -- Recursive case: generate ?S1 + ?S2 + ... + ?Sn
    let Sn ← Meta.mkFreshExprMVar α (userName := (s!"S{n}").toName)
    let prevSum ← @generateSum α (n - 1)
    Meta.mkAppM ``HAdd.hAdd #[prevSum, Sn]

partial def countAdditions (expr : Expr) : Nat :=
    match expr.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, instHAdd, addl, addr]) | (``Add.add, #[_, instAdd, addl, addr]) =>
      1 + countAdditions addl
    | _ => 1

partial def splitAdditions (β expr : Expr) (n : Nat) : TacticM Unit := do
    match expr.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, instHAdd, addl, .app fr _]) | (``Add.add, #[_, instAdd, addl, .app fr _]) =>

        let fll := match addl with
        | .app f _ => f
        | _ => Lean.Expr.lam `n β addl BinderInfo.default

        --logInfo m!"addl: {addl}"
        --logInfo m!"fll: {fll}"
        --logInfo m!"lambda: {Lean.Expr.lam `n β addl BinderInfo.default}"


        let frSyn ← Lean.Expr.toSyntax fr

        if n > 2 then
          let fl := Lean.Expr.lam `n β addl BinderInfo.default

          logInfo fl
          let flSyn ← Lean.Expr.toSyntax fl


          let hSnIdent := mkIdent s!"hS{n}".toName
          let SnIdent := mkIdent s!"S{n}".toName

          Lean.Elab.Tactic.evalTactic (←
          `(tactic| try first |
            refine HasSum.add (f := $flSyn) (g := $frSyn) (b := ?$SnIdent) ?_ ?$hSnIdent |
            convert HasSum.add (f := $flSyn) (g := $frSyn) (b := ?$SnIdent) ?_ ?$hSnIdent))
        else
          let .app fl _ := addl | return
          let flSyn ← Lean.Expr.toSyntax fl

          Lean.Elab.Tactic.evalTactic (←
          `(tactic| try first |
            refine HasSum.add (f := $flSyn) (g := $frSyn) (a := ?S1) (b := ?S2) ?hS1 ?hS2 |
            convert HasSum.add (f := $flSyn) (g := $frSyn) (a := ?S1) (b := ?S2) ?hS1 ?hS2))

        splitAdditions β addl (n - 1)
    | _ => return

-- Recursive tactic to break up a sum using `HasSum.add`
elab "sum_simp" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType

  match target.getAppFnArgs with
  | (``HasSum, #[α, β, _, _, f, a]) =>
    match f with
    | .lam _ _ body _ =>

      logInfo body
      let numAdditions := countAdditions body

      if numAdditions = 0 then
        return

      let S ← @generateSum α (numAdditions)
      let eq_a ← Meta.mkEq a S
      let eq_a_syn ← eq_a.toSyntax
      Lean.Elab.Tactic.evalTactic (← `(tactic| have : $eq_a_syn := ?Sa))
      splitAdditions β body numAdditions
    | _ => throwError "Goal type is not of the form `HasSum f S`"
  | _ => throwError "Goal type is not of the form `HasSum f S`"

example {α : Type} [AddCommMonoid α] [TopologicalSpace α] [ContinuousAdd α]
  {f1 f2 f3 f4 : ℕ → ℝ}
  (hf1 : HasSum f1 1) (hf2 : HasSum f2 3) (hf3 : HasSum f3 0) (hf4 : HasSum f4 (-2)) :
  HasSum (fun n => f1 n + f2 n + f3 n + f4 n) 2 := by
    sum_simp
    . exact hf1
    . exact hf2
    . exact hf3
    . exact hf4
    . linarith



