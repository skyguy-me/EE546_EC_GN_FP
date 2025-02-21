import Lean
import Lean.Elab.Tactic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Defs

def hello := "world"

open Lean Elab Tactic

def isFunWithAdd (e : Expr) : MetaM Bool :=
  match e with
  | .lam n _ body _ =>
    match body with
    | .app (.app (.const ``Add.add _) a) b => return true
    | _ => throwError "Add not found"
  | _ => throwError "Add not found"


example : True := by
  #check isFunWithAdd (fun n : ℕ => n + n)  -- Logs: "The function is of the form `fun n => a + b`."

#check HAdd.hAdd

-- Recursive tactic to break up a sum using `HasSum.add`
elab "breakupHasSum" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  --dbg_trace f!"goal: {goal.name}"

  --Lean.Elab.Tactic.evalTactic (← `(tactic| try apply HasSum.add))

  let .app (
    .app (.app (.app (.app (.app (.const `HasSum _) α) β) _) _) f
  ) S := target | throwError "Goal type is not of the form `HasSum f S`"

  match f with
  | .lam n type_n body _  =>
    --logInfo body
    match body with
    | .app (.app (.app (.app (.app (.app (.const ``HAdd.hAdd _) type_a) type_b) type_c) _ ) f) g =>
      Lean.Elab.Tactic.evalTactic (← `(tactic | refine HasSum.add (f := f) (g := g) ?_ ?_))
    | .app (.app (.const ``Add.add _) a) b => log a
    | _ => throwError "no2"
  | _ => throwError "no"




example {α : Type} [AddCommMonoid α] [TopologicalSpace α] [ContinuousAdd α]
  {f1 f2 f3 : ℕ → α} {a1 a2 a3 A : α}
  (hf1 : HasSum f1 a1) (hf2 : HasSum f2 a2) (hf3 : HasSum f3 a3)
  (ha : A = a1 + a2 + a3) :
  HasSum (fun n => f1 n + f2 n + f3 n) A := by
  breakupHasSum

  --refine HasSum.add (f := fun n => f1 n) (g := fun n => f2 n) ?_ ?_

  -- Now the goal is broken into three subgoals: `HasSum f1 a1`, `HasSum f2 a2`, and `HasSum f3 a3`
  --exact hf1
  --exact hf2
  --exact hf3

variable (p q : Prop)

example : p ∧ q ↔ q ∧ p := by
  breakupHasSum

