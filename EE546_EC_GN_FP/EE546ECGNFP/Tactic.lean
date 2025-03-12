--  * Copyright (C) <2025> <EMBER CHOW AND GOKUL NATHAN>
--  *
--  * This program is free software; you can redistribute it and/or modify
--  * it under the terms of the GNU General Public License as published by
--  * the Free Software Foundation; either version 3 of the License, or (at
--  * your option) any later version.
--  *
--  * This program is distributed in the hope that it will be useful,
--  * but WITHOUT ANY WARRANTY; without even the implied warranty of
--  * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
--  * General Public License for more details.
--  *
--  * You should have received a copy of the GNU General Public License
--  * along with this program; if not, see <http://www.gnu.org/licenses/>.

/-
<center><h1>Tactics supporting Lean4 implementation of Z-transforms</h1></center>
<center><h2>Final Project WI 25 EE-546 B</h2></center>

<center>
Department of Electrical and Computer Engineering<br />
Unviersity of Washington<br />
Ember Chow and Gokul Nathan<br />
Winter 2025<br />
</center>
<br />

-/

import Lean
import Lean.Elab.Tactic
import Mathlib.Tactic

open Lean Elab Tactic

set_option maxHeartbeats 10000000

partial def countAdditions (expr : Expr) : Nat :=
    match expr.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, instHAdd, addl, addr]) | (``Add.add, #[_, instAdd, addl, addr]) =>
      1 + countAdditions addl
    | _ => 0


lemma hasSum_trivial_comp {α β : Type*} [AddCommMonoid α] [TopologicalSpace α]
   (f : β → α) (a : α) : HasSum f a = HasSum (fun x : β ↦ f x) a :=
  rfl

-- Collect all metavariables in an expression
partial def collectMVars (e : Expr) : MetaM (Array MVarId) := do
  let mut mvars : Array MVarId := #[]  -- Declare `mvars` as mutable
  let rec visit (e : Expr) (mvars : Array MVarId) : MetaM (Array MVarId) := do
    match e with
    | .mvar mvarId =>  -- If the expression is a metavariable, add it to the list
      return mvars.push mvarId  -- Return the updated array
    | .app f arg =>  -- Recursively visit function applications
      let mvars ← visit f mvars
      visit arg mvars
    | .lam _ t b _ =>  -- Recursively visit lambda expressions
      let mvars ← visit t mvars
      visit b mvars
    | .forallE _ t b _ =>  -- Recursively visit forall expressions
      let mvars ← visit t mvars
      visit b mvars
    | .letE _ t v b _ =>  -- Recursively visit let expressions
      let mvars ← visit t mvars
      let mvars ← visit v mvars
      visit b mvars
    | _ => return mvars  -- Base case: return the array unchanged
  visit e mvars  -- Start the recursion with the initial `mvars`

-- Example usage
elab "test_mvars" : tactic => do
  let goal ← getMainGoal
  let target ← getMainTarget

  let mvars ← collectMVars target
  --logInfo m!"Metavariables in goal: {mvars}"



def getFVarIdFromName! (name : Name) : MetaM FVarId := do
  -- Get the local context
  let lctx ← getLCtx
  -- Find the local declaration with the given name
  let decl? := lctx.findFromUserName? name
  -- Return the FVarId of the declaration, or throw an error if it doesn't exist
  match decl? with
  | some decl => return decl.fvarId
  | none => throwError m!"No local variable with name '{name}' found in the local context"

-- Turn a list of expressions into a chain of HMul.hMul applications
def reduceHMul (exprs : List Expr) : MetaM Expr := do
  if exprs.isEmpty then
    throwError "Cannot create a chain from an empty list"
  else
    let mut result := exprs.head!
    for expr in exprs.tail! do
      result ← Meta.mkAppM ``HMul.hMul #[result, expr]
    return result

-- Helper function to collect independent terms
partial def collectIndependent(e : Expr) : MetaM (List Expr × List Expr) := do
  match e.getAppFnArgs with
  | (``HMul.hMul, #[α, β, γ, instHMul, mull, mulr]) | (``Mul.mul, #[_, instMul, mull, mulr]) =>
    -- Check if the left and right operands depend on `fvarid`
    -- Recursively collect independent terms from the left and right operands
    let (lhsDependent, lhsIndependent) ← collectIndependent mulr
    let (rhsDependent, rhsIndependent) ← collectIndependent mull

    -- Combine results
    let dependentTerms := lhsDependent ++ rhsDependent
    let independentTerms := lhsIndependent ++ rhsIndependent

    return (dependentTerms, independentTerms)
  | _ =>
    let dep := e.hasLooseBVars
    return (if dep then [e] else [], if dep then [] else [e])

-- Main function
def factor_independent_left (β : Expr) (f : Expr)  : TacticM Unit := do
  let .lam var α body binderInfo := f | throwError "Expected a lambda expression"

  -- Collect dependent and independent terms
  let (dependentTerms, independentTerms) ← collectIndependent body
  -- Log the results
  --logInfo m!"{body} => Dependent terms: {dependentTerms}, Independent terms: {independentTerms}"

  if !independentTerms.isEmpty then
    let deps ← reduceHMul dependentTerms
    let indeps ← reduceHMul independentTerms
    let factored_body ← Meta.mkAppM ``HMul.hMul #[indeps, deps]

    let indepsSyn ← indeps.toSyntax

    let factored_f := Lean.Expr.lam `n α factored_body binderInfo
    let factored_fSyn ← factored_f.toSyntax
    let f_syn ← f.toSyntax

    let f_dependent := Lean.Expr.lam `n α deps binderInfo
    let f_dependentSyn ← f_dependent.toSyntax

    Lean.Elab.Tactic.evalTactic (←`(tactic| try have : $f_syn = $factored_fSyn := by ext; ring_nf))
    Lean.Elab.Tactic.evalTactic (←`(tactic| try simp only[this]))
    Lean.Elab.Tactic.evalTactic (← `(tactic| try clear * -))


    let a₁ ← Meta.mkFreshExprMVar β
    let a₁Syn ← a₁.toSyntax
    Lean.Elab.Tactic.evalTactic (←`(tactic|
      convert HasSum.mul_left (f := $f_dependentSyn) (a₁ := $a₁Syn) $indepsSyn ?_ using 1))
    Lean.Elab.Tactic.evalTactic (← `(tactic| try clear * -))

partial def generateSum {α : Expr} (n : Nat) : MetaM Expr := do
  -- Base case: if n = 1, return ?S1
  if n == 1 then
    Lean.Meta.mkFreshExprMVar α (kind := MetavarKind.synthetic)
  else
    -- Recursive case: generate ?S1 + ?S2 + ... + ?Sn
    let Sn ← Meta.mkFreshExprMVar α
    let prevSum ← @generateSum α (n - 1)
    Meta.mkAppM ``HAdd.hAdd #[prevSum, Sn]


partial def splitAdditions (α' β' expr : Expr) (n : Nat) : TacticM Unit := do
    match expr.getAppFnArgs with
    | (``HAdd.hAdd, #[α, β, γ, instHAdd, addl, addr]) | (``Add.add, #[_, instAdd, addl, addr]) =>

        let fl := Lean.Expr.lam `n β' addl BinderInfo.default
        let fr := Lean.Expr.lam `n β' addr BinderInfo.default

        let flSyn ← Lean.Expr.toSyntax fl
        let frSyn ← Lean.Expr.toSyntax fr

        if n > 1 then
          let hSnIdent := mkIdent s!"sum_simp_{n}".toName
          let Sn ← Lean.Meta.mkFreshExprMVar α' (userName := s!"sum_simp_term_{n + 1}".toName)
          let SnSyn ← Sn.toSyntax


          Lean.Elab.Tactic.evalTactic (←
          `(tactic| try refine HasSum.add (f := $flSyn) (g := $frSyn) (a := ?_) (b := $SnSyn) ?_ ?$hSnIdent))

          factor_independent_left α' fr

        else
          let S1 ← Lean.Meta.mkFreshExprMVar α' (userName := s!"sum_simp_term_1".toName)
          let S2 ← Lean.Meta.mkFreshExprMVar α' (userName := s!"sum_simp_term_2".toName)

          let S1Syn ← S1.toSyntax
          let S2Syn ← S2.toSyntax

          Lean.Elab.Tactic.evalTactic (←
          `(tactic| try refine HasSum.add (f := $flSyn) (g := $frSyn) (a := $S1Syn) (b := $S2Syn) ?sum_simp1 ?sum_simp_2))

          factor_independent_left α' fl
          Lean.Elab.Tactic.evalTactic (←`(tactic| try rotate_left))
          factor_independent_left α' fr
          Lean.Elab.Tactic.evalTactic (←`(tactic| try rotate_right))

        splitAdditions α' β' addl (n - 1)
    | _ => return


-- Recursive tactic to break up a sum using `HasSum.add`
elab "sum_simp" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType

  match target.getAppFnArgs with
  | (``HasSum, #[α, β, _, _, f, a]) =>
    match f with
    | .lam _ _ body _ =>
      let numAdditions := countAdditions body
      --logInfo m!"{←Lean.Meta.inferType a}"

      if numAdditions = 0 then
        factor_independent_left α f
        return

      let eq_a ← Meta.mkEq a (← @generateSum α (numAdditions))
      let eq_a_syn ← eq_a.toSyntax
      Lean.Elab.Tactic.evalTactic (← `(tactic| have : $eq_a_syn := ?_))

      match body.getAppFnArgs with
        | (``HAdd.hAdd, #[α', β', γ, instHAdd, addl, addr]) | (``Add.add, #[_, instAdd, addl, addr]) =>
          let fl := Lean.Expr.lam `n β addl BinderInfo.default
          let fr := Lean.Expr.lam `n β addr BinderInfo.default
          let flSyn ← Lean.Expr.toSyntax fl
          let frSyn ← Lean.Expr.toSyntax fr

          if numAdditions = 1 then
            let S1 ← Lean.Meta.mkFreshExprMVar α (userName := s!"sum_simp_term_1".toName)
            let S2 ← Lean.Meta.mkFreshExprMVar α (userName := s!"sum_simp_term_2".toName)

            let S1Syn ← S1.toSyntax
            let S2Syn ← S2.toSyntax

            Lean.Elab.Tactic.evalTactic (←
            `(tactic| try convert HasSum.add (f := $flSyn) (g := $frSyn) (a := $S1Syn) (b := $S2Syn) ?sum_simp1 ?sum_simp_2))
            factor_independent_left α fl
            Lean.Elab.Tactic.evalTactic (←`(tactic| try rotate_left))

            factor_independent_left α fr
            Lean.Elab.Tactic.evalTactic (←`(tactic| try rotate_right))
          else
            let hSnIdent := mkIdent s!"sum_simp_{numAdditions + 1}".toName
            let Sn ← Lean.Meta.mkFreshExprMVar α (userName := s!"sum_simp_term_{numAdditions + 1}".toName)
            let SnSyn ← Sn.toSyntax

            Lean.Elab.Tactic.evalTactic (←`(tactic| try convert HasSum.add (f := $flSyn) (g := $frSyn) (b := $SnSyn) ?_ ?$hSnIdent))
            factor_independent_left α fr

            splitAdditions α β addl (numAdditions - 1)
        | _ => return
      --Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals try simp only[←hasSum_trivial_comp] ))
      Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals try assumption))
      Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals try clear * -))

      Lean.Elab.Tactic.evalTactic (← `(tactic| rotate_right))
      Lean.Elab.Tactic.evalTactic (← `(tactic| try linarith))
      Lean.Elab.Tactic.evalTactic (← `(tactic| rotate_left))
    | _ => throwError "2: Goal type is not of the form `HasSum f S`"
  | _ => throwError "Goal type is not of the form `HasSum f S`"


example {α : Type} [AddCommMonoid α] [TopologicalSpace α] [ContinuousAdd α]
  {f1 f2 f3 f4 : ℕ → ℝ}
  (hf1 : HasSum f1 1) (hf2 : HasSum f2 3) (hf3 : HasSum f3 0) (hf4 : HasSum f4 (-2)) :
  HasSum (fun n => 2 * f1 n + 3 * f2 n + f3 n + f4 n) 9 := by
    sum_simp


example {α : Type} [AddCommMonoid α] [TopologicalSpace α] [ContinuousAdd α]
  {f1 f2 f3 f4 : ℕ → α} {a1 a2 a3 a4 A : α}
  (hf1 : HasSum f1 a1) (hf2 : HasSum f2 a2) (hf3 : HasSum f3 a3) (hf4 : HasSum f4 a4)
  (hA : A = a1 + a2 + a3 + a4)
  :
  HasSum (fun n => f1 n + f2 n + f3 n + f4 n) A := by
  have : A = ?S1 + ?S2 + ?S3 + ?S4 := ?Sa
  convert HasSum.add (f := fun n => f1 n + f2 n + f3 n) (g := f4) (b := ?S4) ?_ ?hS4
  refine HasSum.add (f := fun n => f1 n + f2 n) (g := f3) (a := ?_) (b := ?S3) ?_ ?hS3
  refine HasSum.add (f := f1) (g := f2) (a := ?S1) (b := ?S2) ?hS1 ?hS2
  all_goals clear * -
  all_goals sorry

example : HasSum (fun (n : ℕ) => 2 * (1/2 : ℝ)^n * 3 * 4 * 5 + 2 * (1/3 : ℝ)^n * 5)
  (255 : ℝ) := by
  ring_nf
  sum_simp

  . refine hasSum_geometric_of_abs_lt_one (r := (1/3 : ℝ)) ?_
    rw[abs_of_nonneg]
    <;> linarith

  . refine hasSum_geometric_of_abs_lt_one (r := (1/2 : ℝ)) ?_
    rw[abs_of_nonneg]
    <;> linarith

  . linarith
