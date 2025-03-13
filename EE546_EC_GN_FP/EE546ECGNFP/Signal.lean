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
<center><h1>Signal definitions for Lean4 Z-transform  implementation</h1></center>
<center><h2>Final Project WI 25 EE-546 B</h2></center>

<center>
Department of Electrical and Computer Engineering<br />
Unviersity of Washington<br />
Ember Chow and Gokul Nathan<br />
Winter 2025<br />
</center>
<br />

-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Norm
import Mathlib.Topology.Filter
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Group.Basic

import EE546ECGNFP.Defs

open Complex Filter Topology Controls

namespace Controls.Discrete

-- Because we're al engineers here.
def j : ℂ := I

/-
A discrete signal is defined to be a function $`x : \mathbb{Z} \to \mathbb{C}`$
-/
def DiscreteSignal : Type := ℤ → ℂ

noncomputable def discrete_convolution (f g : DiscreteSignal) : DiscreteSignal :=
  fun k => ∑' m : ℤ, f m * g (k - m)

/-
A discrete signal is said to be causal iff it is zero for all negative indicies.

$`\forall k < 0, \quad x[k] = 0`$
-/
def IsCausal (x : DiscreteSignal) := ∀ k : ℤ, k < 0 → x k = 0

/-
A discrete signal is said to be causal iff it is zero for all positive indicies.

$`\forall k > 0, \quad x[k] = 0`$
-/
def IsAnticausal (x : DiscreteSignal) := ∀ k ∈ PosInt, x k = 0

/-
A discrete signal is said to be bounded iff there is an upperbound on its norm
for all indicies.

x is bounded $\iff `\exists M \in \mathbb{R} : \forall k \in \mathbb{Z}, \quad \lVert x[k]\rVert` < M$
-/
def IsBoundedSignal (x : DiscreteSignal) := ∃ M : ℝ, ∀ k : ℤ, ‖x k‖ < M

/-
A discrete signal is said to be stable iff its limit at infinity exists and is finite.

$`x`$ is stable $`\iff \displaystyle \lim_{k \to \infty} x[k]`$ exists
-/
def IsStable (x : DiscreteSignal) := ∃ xf : ℂ, Tendsto x atTop (𝓝 xf)

/-
A signal that is both stable and causal is bounded.

$`x`$ is stable and $`x`$ is bounded $`\implies \displaystyle \exists M \in \mathbb{R} :
\forall k \in \mathbb{Z}, \quad \lVert x[k]\rVert` < M`$

We sketch the proof out as follows.

The stability of $`x`$ bounds the tails of the signal for $`n > N`$.
Since there are only finitely many nonzero terms $`n \le N`$, the head of the signal is also bounded.
The overall bound is then the maximum of both of bound on the tail and the head.
-/
theorem isStableAndCausal_implies_isBounded (x : DiscreteSignal) :
    IsStable x → IsCausal x → IsBoundedSignal x := by
  intro hs hc
  obtain ⟨xf, hxf⟩ := hs
  simp only[Metric.tendsto_atTop] at hxf
  have : ∃ N, ∀ n ≥ N, dist (x n) xf < 1 := by
    convert hxf 1
    simp only[zero_lt_one, true_implies]

  obtain ⟨N, hN⟩ := this
  change ∀ n ≥ N, ‖x n - xf‖ < 1 at hN

  have : ∃ M1 : ℝ, ∀ n < N, ‖x n‖ < M1 := by
    by_cases hN_lt_zero : N < 0
    . use 1
      intro n hn
      have hn_lt_zero : n < 0 := by exact Int.lt_trans hn hN_lt_zero
      simp only[hc n, hn_lt_zero]
      simp[norm_zero, zero_lt_one]
    . have hN_gte_zero : N ≥ 0 := by exact Int.not_lt.mp hN_lt_zero
      let Ns := Finset.range (Int.toNat (N + 1))
      have hNs_nonempty : Finset.Nonempty Ns := by
        refine Finset.nonempty_range_iff.mpr ?_
        have : N + 1 > 0 := by exact Int.lt_add_one_iff.mpr hN_gte_zero
        have : ((N + 1).toNat : ℤ) = N + 1 := by
          convert Int.toNat_of_nonneg ?_
          exact Int.le_add_one hN_gte_zero

        intro hn_succ_zero
        have : ((N + 1).toNat : ℤ) = 0 := by exact congrArg Nat.cast hn_succ_zero
        linarith

      let X := Ns.image (fun n : ℕ ↦ ‖x n‖)
      let M0 := X.max' ((Ns.image_nonempty).mpr hNs_nonempty)
      have : 0 ≤ M0 := by
        have hx0_nonneg : ∀ x0 ∈ X, x0 ≥ 0 := by
          intro x0 hx0
          simp only[X] at hx0
          have := by apply (Ns.mem_image (f := (fun n : ℕ ↦ ‖x n‖))).mp hx0
          obtain ⟨n, ⟨hn_mem, hn⟩⟩ := this
          have : ‖x n‖ ≥ 0 := by exact norm_nonneg (x ↑n)
          exact le_of_le_of_eq this hn

        let x0 := X.toList.head!
        have hx0 : x0 ∈ X := by
          refine (X.mem_toList).mp ?_
          refine List.head!_mem_self ?_
          refine Finset.Nonempty.toList_ne_nil ?_
          exact Finset.image_nonempty.mpr hNs_nonempty

        have : 0 ≤ x0 := by
          apply hx0_nonneg
          exact hx0

        have := X.le_max' x0 hx0
        exact Preorder.le_trans 0 x0 M0 (hx0_nonneg x0 hx0) this

      have : M0 < M0 + 1 := by linarith

      use M0 + 1
      intro n hn
      by_cases hn_lt_zero : n < 0
      . simp only[hc n, hn_lt_zero]
        simp only [norm_zero]
        linarith
      . have n_nonneg : n ≥ 0 := by exact Int.not_lt.mp hn_lt_zero

        have : ‖x n.toNat‖ ≤ M0 := by
          simp only[M0]
          apply X.le_max'
          refine Ns.mem_image_of_mem (fun n ↦ ‖x ↑n‖) ?_
          refine Finset.mem_range.mpr ?_
          refine (Int.toNat_lt_toNat ?_).mpr ?_
          . exact Int.lt_add_one_iff.mpr hN_gte_zero
          . refine Int.lt_add_one_iff.mpr ?_
            exact Int.le_of_lt hn

        simp only[Int.toNat_of_nonneg n_nonneg] at this
        linarith

  obtain ⟨M, hM⟩ := this
  have hN_bound : ∀ n ≥ N, ‖x n‖ < 1 + ‖xf‖ := by
    intro n hn

    calc
      ‖x n‖ = ‖x n - xf + xf‖ := by ring_nf
      _ ≤ ‖x n - xf‖ + ‖xf‖ := by exact norm_add_le (x n - xf) xf
      _ < 1 + ‖xf‖ := by rel[hN n hn]

  use max (M) (1 + ‖xf‖)
  intro k

  by_cases hk : k < N
  . refine lt_max_of_lt_left (a := ‖x k‖) (b := M) (c := 1 + ‖xf‖) ?_
    exact hM k hk
  . simp[Int.not_lt] at hk
    refine lt_max_of_lt_right (a := ‖x k‖) (b := M) (c := 1 + ‖xf‖) ?_
    exact hN_bound k hk


/-
A discrete signal is said to have a final value $`xf`$ iff that is its limit at infinity.

$`xf`$ is the final value of $`x` \iff \displaystyle \lim_{k \to \infty} x[k] = xf$
-/
def HasFinalValue (x : DiscreteSignal) (xf : ℂ) := Tendsto x atTop (𝓝 xf)

/-
A discrete signal with a final value is stable.
-/
theorem hasFinalValue_implies_isStable (x : DiscreteSignal) (xf : ℂ) :
    HasFinalValue x xf → IsStable x := by
      intro h
      use xf
      exact h

/-
The following two theorems state that $`f`$ is causal signal, the product of it with any signal is
also causal.

$`f`$ is causal $`\implies \forall g : \mathbb{Z} \to \mathbb{C}, \quad f \cdot g`$ is causal
-/
theorem isCausal_of_mul_causal {f g : DiscreteSignal} (hf : IsCausal f) : IsCausal (fun k ↦ g k * f k) := by
  intro k hk
  convert mul_zero (g k)
  exact hf k hk

theorem isCausal_of_causal_mul {f g : DiscreteSignal} (hf : IsCausal f) : IsCausal (fun k ↦ f k * g k) := by
  convert isCausal_of_mul_causal (g := g) hf using 2
  rw[mul_comm]


/-
The infinite sum over the negative indicies of a causal signal is zero.

$`\displaystyle f`$ is causal $`\implies \sum_{k = -\infty}^-1 f[k] = 0`$
-/
theorem summable_zero_of_causal {f : DiscreteSignal} (hf : IsCausal f) :
    Summable (fun k : NegInt ↦ f k) := by
      convert summable_zero with ⟨k, hk⟩
      exact hf k hk

theorem hasSum_zero_of_causal {f : DiscreteSignal} (hf : IsCausal f) :
    HasSum (fun k : NegInt ↦ f k) 0 := by
      convert hasSum_zero with ⟨k, hk⟩
      exact hf k hk


/-
Multiplication by a causal signal can be written as an indicator function.

$`\displaystyle f`$ is causal $`\implies \sum_{k = -\infty}^-1 f[k] = 0`$
-/

theorem indicator_of_IsCausal_mul {f : DiscreteSignal} {g : DiscreteSignal} (hf : IsCausal f) :
  (fun k : ℤ ↦ f k * g k) = (fun k : ℤ ↦ NonNegInt.indicator (fun k ↦ f k * g k) k) := by
    ext k

    by_cases hk : k < 0

    . have : k ∉ NonNegInt := by exact Int.not_le.mpr hk
      simp only[Set.indicator_of_not_mem this, hf k hk, zero_mul]

    . simp only[Int.not_lt] at hk
      change k ∈ NonNegInt at hk
      simp only[Set.indicator_of_mem hk]

theorem indicator_of_mul_IsCausal {f : DiscreteSignal} {g : DiscreteSignal} (hf : IsCausal f) :
  (fun k : ℤ ↦ g k * f k) = fun k : ℤ ↦ NonNegInt.indicator (fun k ↦ g k * f k) k := by
    convert indicator_of_IsCausal_mul hf (g := g) using 2
    <;> simp[mul_comm]

/-
**1. Unit Impulse Function (`δ(k)`)**
The **unit impulse function**, also known as the **Kronecker delta function**, is defined as:
-/

@[simp]
def unit_impulse (k : ℤ) : ℂ :=
  if k = 0 then 1 else 0
/-This function acts as an identity under convolution and is fundamental for analyzing system responses. The impulse function can be equivalently expressed using a set indicator function:-/

theorem unit_impulse_equiv_indicator :
    ∀ k : ℤ, unit_impulse k = Set.indicator {0} 1 k := by
  intro k
  by_cases k_zero : k = 0
  <;> simp[k_zero]

notation "δ" => unit_impulse

/-
**2. Unit Step Function (`u(k)`)**
The **unit step function**, which reperent causality in discrete time signals is defined as:
-/


@[simp]
def unit_step (k : ℤ) : ℂ :=
  if k ≥ 0 then 1 else 0

alias u := unit_step
alias H := unit_step

/-
The following utility lemmas conditions on when the unit step function is 1 or 0.
-/
@[simp]
lemma unit_step_of_nat : ∀ (n : ℕ), unit_step n = 1 := by
  intro n
  simp

@[simp]
lemma unit_step_of_nonneg : ∀ (k : NonNegInt), unit_step k = 1 := by
  intro ⟨k, hk⟩
  simp
  exact hk


@[simp]
lemma unit_step_of_pos : ∀ (k : PosInt), unit_step k = 1 := by
  intro ⟨k, hk⟩
  simp
  exact Int.le_of_lt hk

@[simp]
lemma unit_step_of_neg : ∀ (k : NegInt), unit_step k = 0 := by
  intro ⟨k, hk⟩
  simp
  exact hk

/-
The unit step function is equivalen tot an indiicator function of 1.
-/
lemma unit_step_equiv_indicator : ∀ k : ℤ, unit_step k = NonNegInt.indicator 1 k := by
  intro k
  unfold NonNegInt
  by_cases k_pos : k ≥ 0
  <;> simp[k_pos]

/-
The unit step function is causal.
-/
lemma unit_step_causal : IsCausal unit_step := by simp[IsCausal]

@[simp]
theorem hasSum_nat_of_unit_step_mul (f : DiscreteSignal) (S : ℂ) :
    HasSum (fun (n : ℕ) ↦ u n * f n) S ↔
    HasSum (fun (n : ℕ) ↦ f n) S := by
      simp only[u, unit_step_of_nat, one_mul]

/-
This allows us to rewrite sums over ℤ in terms of sums over non-negative integers only,
a key step when handling Z-transform proofs for causal signals.
-/

theorem causal_of_mul_unit_step (x : DiscreteSignal) :
    IsCausal (fun k : ℤ ↦ x k * u k) := by
      exact isCausal_of_mul_causal unit_step_causal

/-
This confirms that causal signals only depend on present and past values,
which simplifies Z-transform computations.
-/


theorem causal_of_unit_step_mul (x : DiscreteSignal) :
    IsCausal (fun k : ℤ ↦ u k * x k) := by
      simp only[mul_comm]
      exact causal_of_mul_unit_step x

/-This means we can safely reorder terms in proofs without worrying about violating causality-/


  /--
The rect function,from (a,b]), is defined as:
-/

/-
**2. Rect Function (`R(k)`)**
The **rectfunction**, which represent a signal that is non-zero for  definite, positive interval:
-/

@[simp]
def rect (a b : ℤ) (k : ℤ) :=
  unit_step (k - a) - unit_step (k - b)
