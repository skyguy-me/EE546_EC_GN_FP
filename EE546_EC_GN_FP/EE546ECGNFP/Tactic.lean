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


The sum simplification tactic decmposes a sum through linearity. In general, many sums can be expressed as linear
combinations of simpler sums. Decomposing these by hand can be tedious and not scalable for large sums.
-/

import Lean
import Lean.Elab.Tactic
import Mathlib.Tactic

open Lean Elab Tactic

/-
## Utilities

In order to define the sum simplification tactic, we first write several utilities which will be used by the file.
-/


/-

#### reduceHMul

Performs a mulutiplication reducation on a list of expressions, turning `[expr1, expr2, expr3, ...]` into
`expr1 * expr2 * expr3 * ...`

This is used in factoring expressions out of sums. In the tactic, we collect all constant factors as an array.
This function reassembles us to reorder the product with all constant
factors to the left.
-/

def reduceHMul (exprs : List Expr) : MetaM Expr := do
  if exprs.isEmpty then
    throwError "Cannot create a chain from an empty list"
  else
    let mut result := exprs.head!
    for expr in exprs.tail! do
      result ← Meta.mkAppM ``HMul.hMul #[result, expr]
    return result

/-
#### Collect Independent

This function takes an expression e which is of the form  and collects all all dependent and
independent terms. `a * b(n) * c(n) * d ...` gets turned into two lists `[a, d, ...]` and `[b(n), c(n), ...]`

This is used to decompose scaled sums. It works whether or not the scaling happens to the left or right,
and works for arbitrary numbers of factors.
-/
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

/-
#### countAndCollect

Given an expression that is a sum of products: $`a₁ * b₁(n) * c₁(n) * ... + a₂(n) * b₂(n) * ... + ... `$
this function simulatneously counts how many additions are in the expression and for each term, seperates out
independent and dependent terms.

For example:

$`a_1 * b_1(n) * c_1(n) * ... + a_2(n) * b_2(n) * ... + ... a_N(n) * b_N * ...`$ is converted into
$`\left(N, [[b_N],\ ...,\ [a₁]],\ [[a_N, b_N],\ ...,\ [a_2, b_2],\ [b_1, c_1]]\right)`$
-/
partial def countAndCollect(expr : Expr) : MetaM (Nat × List (List Expr) × List (List Expr)) := do
    match expr.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, instHAdd, addl, addr]) | (``Add.add, #[_, instAdd, addl, addr]) =>
      let (n, deps, indeps) ← countAndCollect addl
      let (depl, indepl) ← collectIndependent addr
      return (n + 1, [depl] ++ deps , [indepl] ++ indeps)
    | _ =>
      let (dep, indep) ← collectIndependent expr
      return ((0 : ℕ), [dep], [indep])

/-
#### factorIndependentLeft

Given a lambda expression that is a part of a `HasSum`, this will
factor all constant factors (independent terms) to the left.

This function does nothing if there are no independent terms to factor.
-/
def factorIndependentLeft (f : Expr) (dependentTerms : List Expr) (independentTerms : List Expr) (target : Expr)  : TacticM Unit := do
  let .lam var α _ binderInfo := f | throwError "Expected a lambda expression"

  if !independentTerms.isEmpty then

/-
The first step is to generate the factored expression. This is
accomplished by mutiplying all the independent terms to the left
of the dependent terms. This is used to create a lambda expression
that represents the result of the factorization.

$`\textrm{dependentTerms} = [a, b, c]
\quad \to \quad
\textrm{depsMul} = a\, *\, b\, *\, c`$

$`\textrm{independentTerms} = [f₁(n), f_2(n)]
\quad \to \quad
\textrm{indepsMul} = f_1(n)\, *\, f_2(n)`$

$`\textrm{factored\_body} = a\, *\, b\, *\, c\, *\, f_1(n)\, *\, f_2(n)`$
-/
    let depsMul ← reduceHMul dependentTerms
    let indepsMul ← reduceHMul independentTerms
    let factored_body ← Meta.mkAppM ``HMul.hMul #[indepsMul, depsMul]

    let factored_f := Lean.Expr.lam var α factored_body binderInfo
    let factored_fSyn ← factored_f.toSyntax
    let f_syn ← f.toSyntax

/-
The factored expression and the original expression can be shown
to be equal by using the `ext` and `ring_nf` tactics. This equality
is subsequently substituted into the current subgoal.

The equality subgoal introduced by the `have` tactic is then
cleared since it is no longer necessary.


$`\textrm{fun}\ n \mapsto a\, *\, f₁(n)\, *\, b\, *\, f₂(n)\, *\, c =
\textrm{fun}\ n \mapsto a\, *\, b\, *\, c\, *\, f₁(n)\, *\, f₂(n)`$

$`\textrm{HasSum} (\textrm{fun}\ n \mapsto a\, *\, f₁(n)\, *\, b\, *\, f₂(n)\, *\, c)\ ?\_
\to
\textrm{HasSum} (\textrm{fun}\ n \mapsto a\, *\, b\, *\, c\, *\, f₁(n)\, *\, f₂(n))\ ?\_
`$
-/
    Lean.Elab.Tactic.evalTactic (←`(tactic|
      try have : $f_syn = $factored_fSyn := by ext; ring_nf))
    Lean.Elab.Tactic.evalTactic (←`(tactic| try simp only[this]))
    Lean.Elab.Tactic.evalTactic (← `(tactic| try clear * -))

/-
Finally `HasSum.mul_left` is applied to reduce solving the sum to solving its
dependent part.

$`\textrm{HasSum} (\textrm{fun}\ n \mapsto a\, *\, b\, *\, c\, *\,
f_1(n)\, *\, f_2(n))\ ?\_
\to
\textrm{HasSum} \underbrace{(\textrm{fun}\ n \mapsto f_1(n)\, *\, f_2(n))}_{\textrm{f\_dependent}}\ (\underbrace{(a\, *\, b\, *\, c)}_{\textrm{indepsMul}}\, *\, ?\_)`$
-/

    let f_dependent := Lean.Expr.lam var α depsMul binderInfo
    let f_dependentSyn ← f_dependent.toSyntax

    let indepsMulSyn ← indepsMul.toSyntax
    let targetSyn ← target.toSyntax

    Lean.Elab.Tactic.evalTactic (←`(tactic|
      refine HasSum.mul_left (f := $f_dependentSyn) (a₁ := $targetSyn) $indepsMulSyn ?_))
    Lean.Elab.Tactic.evalTactic (← `(tactic| try clear * -))

/-
#### generateSum

Generates a sum with n placeholder variables with constant factors. Returns ths sum expression, a list of the
placeholders with constant factors out front, and a list of the placeholders.
-/
partial def generateSum {α : Expr} (n : Nat) (indeps : List (List Expr)) : MetaM (Expr × List Expr × List Expr) := do
  -- Base case: if n = 1, return ?S1
  if n == 1 then

    let Sn ← Lean.Meta.mkFreshExprMVar α (userName := s!"S{n}".toName) (kind := MetavarKind.syntheticOpaque)
    if !indeps.head!.isEmpty then
      let Sn_mul ← Meta.mkAppM ``HMul.hMul #[←reduceHMul indeps.head!, Sn]
      return (Sn_mul, [Sn_mul], [Sn])
    else
      return (Sn, [Sn], [Sn])
  else
    let (prevSum, snMulList, snList) ← @generateSum α (n - 1) indeps.tail!
    -- Recursive case: generate ?S1 + ?S2 + ... + ?Sn
    let Sn ← Meta.mkFreshExprMVar (userName := s!"S{n}".toName) α (kind := MetavarKind.syntheticOpaque)

    if !indeps.head!.isEmpty then
      let Sn_mul ← Meta.mkAppM ``HMul.hMul #[←reduceHMul indeps.head!, Sn]
      return (←Meta.mkAppM ``HAdd.hAdd #[prevSum, Sn_mul], [Sn_mul] ++ snMulList, [Sn] ++ snList)
    else
      return (←Meta.mkAppM ``HAdd.hAdd #[prevSum, Sn], [Sn] ++ snMulList, [Sn] ++ snList)


/-
#### decomposeSum

Decomposes a sum expression using linearity. The first step is to
check if the expression we are decomposing is a HasSum expression..
-/
partial def decomposeSum  (β' : Expr) (depsList indepsList : List (List Expr)) (mulTermsList expMvarsList : List Expr) (expr : Expr) (n : Nat) : TacticM Unit := do
    match expr.getAppFnArgs with
    | (``HAdd.hAdd, #[α, β, γ, instHAdd, addl, addr]) | (``Add.add, #[_, instAdd, addl, addr]) =>

/-
We recursively split the sum into left and right components using left
associativity. An example is provided below.

$`\textrm{HasSum} \underbrace{((f_1(n) + f_2(n))}_{\textrm{addl}} +
\underbrace{a\, *\, f_3(n)\, *\, b)}_{addr}`$

We subsequently turn these into lambdas expressions.

$`fl := \textrm{fun}\ n \mapsto a\, *\, f_3(n)\, *\, b `$
$`fr := \textrm{fun}\ n \mapsto f_1(n) + f_2(n) `$
-/

        let fl := Lean.Expr.lam `n β' addl BinderInfo.default
        let fr := Lean.Expr.lam `n β' addr BinderInfo.default

        let flSyn ← Lean.Expr.toSyntax fl
        let frSyn ← Lean.Expr.toSyntax fr

/-
Base case:

This is similar to the recursive case, which is discussed in further depth.
-/
        if n == 1 then

          let S1Syn ← mulTermsList[1]!.toSyntax
          let S2Syn ← mulTermsList[0]!.toSyntax

          Lean.Elab.Tactic.evalTactic (←
          `(tactic| try convert HasSum.add (f := $flSyn) (g := $frSyn) (a := $S1Syn) (b := $S2Syn) ?sum_simp_1 ?sum_simp_2))

          factorIndependentLeft fl depsList[1]! indepsList[1]! expMvarsList[1]!
          Lean.Elab.Tactic.evalTactic (←`(tactic| try rotate_left))
          factorIndependentLeft fr depsList[0]! indepsList[0]! expMvarsList[0]!
          Lean.Elab.Tactic.evalTactic (←`(tactic| try rotate_right))
          return
/-
Recursive case:

We use the `convert` tactic to decompose the current goal
into two subgoals, recursively applying `HasSum.add`.
We name the right subgoal `sum_simp_{n + 1}`. The left subgoal
will continue to be decomposed.

Here `SnSyn` represents the unknown value of the right-most term of the sum
after the split. It includes the value of any known constant factors so that the
Lean type system performs better inference. Continuing from the previous example we
now have:

$`\textrm{HasSum}\ (\textrm{fun}\ \mapsto f_1(n) + f_2(n))\ ?\_ \quad\quad`$ left subgoal

$`\textrm{HasSum}\ (\textrm{fun}\ \mapsto a\, *\, f_3(n)\, *\, b)
\underbrace{(a\, *\, b\, *\, ?S_k)}_{\textrm{mulTermsList[0]}} \quad\quad`$ right subgoal (sum_simp_1)

All arrays are structured so terms are ordered right to left.
-/

        let hSnIdent := mkIdent s!"sum_simp_{n + 1}".toName
        let SnSyn ← mulTermsList.head!.toSyntax

        Lean.Elab.Tactic.evalTactic (←`(tactic| try convert HasSum.add (f := $flSyn) (g := $frSyn) (b := $SnSyn) ?_ ?$hSnIdent))

/-
The next step is to factor out any constants to the left. `rotate_left`
is used to reorder the goals so we can factor the right-most sum. After
the term is factored, `rotate_right` resets the goals to their original order.

See `factorIndependentLeft` for more details.

Finally, we recusively call the `decomposeSum` function, giving it
the left-side of the `HasSum` expression. `depsList`, `indepsList`,
`mulTermsList`, and `expMvarsList` are ordered right-most to left-most
so the head of the tail is the next term.
-/

        Lean.Elab.Tactic.evalTactic (←`(tactic| try rotate_left))
        factorIndependentLeft fr depsList.head! indepsList.head! expMvarsList.head!
        Lean.Elab.Tactic.evalTactic (←`(tactic| try rotate_right))

        decomposeSum β' depsList.tail indepsList.tail mulTermsList.tail expMvarsList.tail addl (n - 1)
    | _ => return


/-
### sum_simp

Recusrively simplifies a sum expression using linearity.
-/
elab "sum_simp" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType

  match target.getAppFnArgs with
  | (``HasSum, #[α, β, _, _, f, a]) =>
    match f with
    | .lam _ _ body _ =>
      let (numAdditions, depsList, indepsList) ← countAndCollect body

      if numAdditions = 0 then
        factorIndependentLeft f depsList[0]! indepsList[0]! (←Meta.mkFreshExprMVar β (kind := MetavarKind.syntheticOpaque))
        return

      let (sum, mulTermsList, expMvarsList) ← @generateSum α (numAdditions + 1) indepsList
      let eq_a ← Meta.mkEq a (sum)
      let eq_a_syn ← eq_a.toSyntax
      Lean.Elab.Tactic.evalTactic (← `(tactic| have : $eq_a_syn := ?_))

      match body.getAppFnArgs with
        | (``HAdd.hAdd, #[α', β', γ, instHAdd, addl, addr]) | (``Add.add, #[_, instAdd, addl, addr]) =>
          let fl := Lean.Expr.lam `n β addl BinderInfo.default
          let fr := Lean.Expr.lam `n β addr BinderInfo.default
          let flSyn ← Lean.Expr.toSyntax fl
          let frSyn ← Lean.Expr.toSyntax fr

          if numAdditions = 1 then
            let S1Syn ← mulTermsList[1]!.toSyntax
            let S2Syn ← mulTermsList[0]!.toSyntax

            Lean.Elab.Tactic.evalTactic (←
            `(tactic| try convert HasSum.add (f := $flSyn) (g := $frSyn) (a := $S1Syn) (b := $S2Syn) ?sum_simp_1 ?sum_simp_2))

            factorIndependentLeft fl depsList[1]! indepsList[1]! expMvarsList[1]!
            Lean.Elab.Tactic.evalTactic (←`(tactic| try rotate_left))
            factorIndependentLeft fr depsList[0]! indepsList[0]! expMvarsList[0]!
            Lean.Elab.Tactic.evalTactic (←`(tactic| try rotate_right))

          else
            let hSnIdent := mkIdent s!"sum_simp_{numAdditions + 1}".toName
            let SnSyn ← mulTermsList[0]!.toSyntax

            Lean.Elab.Tactic.evalTactic (←`(tactic| try convert HasSum.add (f := $flSyn) (g := $frSyn) (b := $SnSyn) ?_ ?$hSnIdent))

            Lean.Elab.Tactic.evalTactic (←`(tactic| try rotate_left))
            factorIndependentLeft fr depsList[0]! indepsList[0]! expMvarsList[0]!
            Lean.Elab.Tactic.evalTactic (←`(tactic| try rotate_right))

            decomposeSum β depsList.tail indepsList.tail mulTermsList.tail expMvarsList.tail addl (numAdditions - 1)
        | _ => return
      --Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals try simp only[←hasSum_trivial_comp] ))
      Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals try assumption))
      Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals try clear * -))

      Lean.Elab.Tactic.evalTactic (← `(tactic| rotate_right))
      Lean.Elab.Tactic.evalTactic (← `(tactic| try linarith))
      Lean.Elab.Tactic.evalTactic (← `(tactic| rotate_left))
    | _ => throwError "2: Goal type is not of the form `HasSum f S`"
  | _ => throwError "Goal type is not of the form `HasSum f S`"

/-
### Developing an Intuition for the Tactic

In general, we wish to break up a sum using linearity. Below, we have a sum that is the sum of four known
sums. This decomposition takes four steps since we can only decompose it one at a time.

Even this relatively simply example already has a complex proof. If each of these also were multiplied by constant
factors, this would require 12 steps: 4 to split the addtions, 4 to simplify the products, and 4 to factor the products.
-/
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


/-
### Automation with `sum_simp`

`sum_simp` automates each of the steps shown in the previous problem. We sketch out the algorithm roughly as follows

1. Count the number of additions.
2. For each term in the addition, create lists of constants (independent factors) and dependent factors.
3. Inform Lean of the form of the goal using placeholders.
4. Recuisvely decompose.
5. Try to solve any subgoals using hypothesis in the goal state.
6. Run linarith to show each of the sub-sums (scaled by their constant factors.)
-/
example {α : Type} [AddCommMonoid α] [TopologicalSpace α] [ContinuousAdd α]
  {f1 f2 f3 f4 : ℕ → ℝ}
  (hf1 : HasSum f1 1) (hf2 : HasSum f2 3) (hf3 : HasSum f3 0) (hf4 : HasSum f4 (-2)) :
  HasSum (fun n => 2 * f1 n + 3 * f2 n + f3 n + 2 * f4 n) 7 := by
    sum_simp


example (A B C : ℝ) : HasSum (fun (n : ℕ) => 2 * C * A * (1/2 : ℝ)^n * 3 * 4 * 5 + 2 * (1/3 : ℝ)^n * 5 * B + 3 * (1/4 : ℝ)^n * A * B^2)
  (240 * A * C + 15 * B + 4 * A * B^2 : ℝ) := by
  sum_simp

  . refine hasSum_geometric_of_abs_lt_one (r := (1/2 : ℝ)) ?_
    rw[abs_of_nonneg]
    <;> linarith

  . refine hasSum_geometric_of_abs_lt_one (r := (1/3 : ℝ)) ?_
    rw[abs_of_nonneg]
    <;> linarith

  . refine hasSum_geometric_of_abs_lt_one (r := (1/4 : ℝ)) ?_
    rw[abs_of_nonneg]
    <;> linarith

  . linarith
