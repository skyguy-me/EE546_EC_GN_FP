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


partial def splitAdditions (β' expr : Expr) (n : Nat) : TacticM Unit := do
    match expr.getAppFnArgs with
    | (``HAdd.hAdd, #[α, β, γ, instHAdd, addl, addr]) | (``Add.add, #[_, instAdd, addl, addr]) =>

        let fl := Lean.Expr.lam `n β' addl BinderInfo.default
        let fr := Lean.Expr.lam `n β' addr BinderInfo.default

        let flSyn ← Lean.Expr.toSyntax fl
        let frSyn ← Lean.Expr.toSyntax fr

        if n > 2 then
          let hSnIdent := mkIdent s!"hS{n}".toName
          let SnIdent := mkIdent s!"S{n}".toName

          Lean.Elab.Tactic.evalTactic (←
          `(tactic| try first |
            refine HasSum.add (f := $flSyn) (g := $frSyn) (b := ?$SnIdent) ?_ ?$hSnIdent |
            convert HasSum.add (f := $flSyn) (g := $frSyn) (b := ?$SnIdent) ?_ ?$hSnIdent))
        else
          Lean.Elab.Tactic.evalTactic (←
          `(tactic| try first |
            refine HasSum.add (f := $flSyn) (g := $frSyn) (a := ?S1) (b := ?S2) ?hS1 ?hS2 |
            convert HasSum.add (f := $flSyn) (g := $frSyn) (a := ?S1) (b := ?S2) ?hS1 ?hS2))

        splitAdditions β' addl (n - 1)
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

      if numAdditions = 0 then
        return

      let S ← @generateSum α (numAdditions)
      logInfo S
      let eq_a ← Meta.mkEq a S
      let eq_a_syn ← eq_a.toSyntax
      Lean.Elab.Tactic.evalTactic (← `(tactic| have : $eq_a_syn := ?Sa))
      splitAdditions β body numAdditions
      Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals try simp only[←hasSum_trivial_comp] ))
      Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals try assumption))
      --Lean.Elab.Tactic.evalTactic (← `(tactic| assumption))
    | _ => throwError "2: Goal type is not of the form `HasSum f S`"
  | _ => throwError "Goal type is not of the form `HasSum f S`"

example {α : Type} [AddCommMonoid α] [TopologicalSpace α] [ContinuousAdd α]
  {f1 f2 f3 f4 : ℕ → α} {a1 a2 a3 a4 A : α}
  (ha : a1 + a2 + a3 + a4 = A)
  (hf1 : HasSum f1 a1) (hf2 : HasSum f2 a2) (hf3 : HasSum f3 a3) (hf4 : HasSum f4 a4) :
  HasSum (fun n => f1 n + f2 n + f3 n + f4 n) A := by

  have : HasSum (fun n => f1 n + f2 n) (a1 + a2) := by exact HasSum.add hf1 hf2
  have : HasSum (fun n => f1 n + f2 n + f3 n) (a1 + a2 + a3) := by exact HasSum.add this hf3

  have : HasSum (fun n => f1 n + f2 n + f3 n + f4 n) (a1 + a2 + a3 + a4) := by exact HasSum.add this hf4

  convert this



example {α : Type} [AddCommMonoid α] [TopologicalSpace α] [ContinuousAdd α]
  {f1 f2 f3 f4 : ℕ → ℝ}
  (hf1 : HasSum f1 1) (hf2 : HasSum f2 3) (hf3 : HasSum f3 0) (hf4 : HasSum f4 (-2)) :
  HasSum (fun n => f1 n + f2 n + f3 n + f4 n) 2 := by
    sum_simp
    . linarith

example {α : Type} [AddCommMonoid α] [TopologicalSpace α] [ContinuousAdd α]
  {f1 f2 f3 f4 : ℕ → α} {a1 a2 a3 a4 A : α}
  (hf1 : HasSum f1 a1) (hf2 : HasSum f2 a2) (hf3 : HasSum f3 a3) (hf4 : HasSum f4 a4) :
  HasSum (fun n => f1 n + f2 n + f3 n + f4 n) A := by

  have : A = ?S1 + ?S2 + ?S3 + ?S4 := ?hS

  convert HasSum.add (f := fun n => f1 n + f2 n + f3 n) (g := f4) (b := ?S4) ?_ ?$hS4

  refine HasSum.add (f := fun n => f1 n + f2 n) (g := f3) (b := ?s3) ?_ ?hs3

  refine HasSum.add (f := f1) (g := f2) (a := ?s1) (b := ?s2) ?hs1 ?hs2

  . exact hf1



example : HasSum (fun (n : ℕ) => 2 * (1/2 : ℝ)^n + 2 * (1/3 : ℝ)^n) (7 : ℝ) := by
  sum_simp
  . convert (hasSum_mul_left_iff (a₁ := ?_) (a₂ := 2) (f := fun n ↦  (1/2 : ℝ)^n) ?_).mpr ?_
    . exact Ne.symm (NeZero.ne' 2)
    . refine hasSum_geometric_of_abs_lt_one (r := (1/2 : ℝ)) ?_
      rw[abs_of_nonneg]
      . exact one_half_lt_one
      . simp

  . convert (hasSum_mul_left_iff (a₁ := ?_) (a₂ := 2) (f := fun n ↦  (1/3 : ℝ)^n) ?_).mpr ?_
    . exact Ne.symm (NeZero.ne' 2)
    . refine hasSum_geometric_of_abs_lt_one (r := (1/3 : ℝ)) ?_
      rw[abs_of_nonneg]
      <;> linarith

  . linarith
