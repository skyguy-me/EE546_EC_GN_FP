
<center><h1>Signal definitions for Lean4 Z-transform  implementation</h1></center>
<center><h2>Final Project WI 25 EE-546 B</h2></center>

<center>
Department of Electrical and Computer Engineering<br />
Unviersity of Washington<br />
Ember Chow and Gokul Nathan<br />
Winter 2025<br />
</center>
<br />


```hs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Norm
import Mathlib.Topology.Filter
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Order.BoundedOrder.Basic

import EE546ECGNFP.Defs

open Complex Filter Topology Controls

namespace Controls.Discrete

-- Because we're al engineers here.
def j : ℂ := I
```

A discrete signal is defined to be a function $`x : \mathbb{Z} \to \mathbb{C}`$

```hs
def DiscreteSignal : Type := ℤ → ℂ

noncomputable def discrete_convolution (f g : DiscreteSignal) : DiscreteSignal :=
  fun k => ∑' m : ℤ, f m * g (k - m)
```

A discrete signal is said to be causal iff it is zero for all negative indicies.

$`\forall k < 0, \quad x[k] = 0`$

```hs
def IsCausal (x : DiscreteSignal) := ∀ k : ℤ, k < 0 → x k = 0
```

A discrete signal is said to be causal iff it is zero for all positive indicies.

$`\forall k > 0, \quad x[k] = 0`$

```hs
def IsAnticausal (x : DiscreteSignal) := ∀ k ∈ PosInt, x k = 0
```

A discrete signal is said to be bounded iff there is an upperbound on its norm
for all indicies.

x is bounded $\iff `\exists M \in \mathbb{R} : \forall k \in \mathbb{Z}, \quad \lVert x[k]\rVert` < M$

```hs
def IsBoundedSignal (x : DiscreteSignal) := ∃ M : ℝ, ∀ k : ℤ, ‖x k‖ < M
```

A discrete signal is said to be stable iff its limit at infinity exists and is finite.

$`x`$ is stable $`\iff \displaystyle \lim_{k \to \infty} x[k]`$ exists

```hs
def IsStable (x : DiscreteSignal) := ∃ xf : ℂ, Tendsto x atTop (𝓝 xf)
```

A signal that is both stable and causal is bounded.

$`x`$ is stable and $`x`$ is bounded $`\implies \displaystyle \exists M \in \mathbb{R} :
\forall k \in \mathbb{Z}, \quad \lVert x[k]\rVert` < M`$

We sketch the proof out as follows.

The stability of $`x`$ bounds the tails of the signal for $`n > N`$.
Since there are only finitely many nonzero terms $`n \le N`$, the head of the signal is also bounded.
The overall bound is then the maximum of both of bound on the tail and the head.

```hs
theorem isStableAndCausal_implies_isBounded (x : DiscreteSignal) :
    IsStable x → IsCausal x → IsBoundedSignal x := by
  intro hs hc
  obtain ⟨xf, hxf⟩ := hs
```

We'll use subistute in the $`\epsilon = 1`$ into the stability condition first.

$`\exists N : \forall n \ge N \lVert x[n] - x_f \rVert < \underbrace{\epsilon}_{= 1}`$

```hs
simp only[Metric.tendsto_atTop] at hxf
  have : ∃ N, ∀ n ≥ N, dist (x n) xf < 1 := by exact hxf 1 zero_lt_one

  obtain ⟨N, hN⟩ := this
  change ∀ n ≥ N, ‖x n - xf‖ < 1 at hN
```

#### Establish the bound for n ≥ N

This is a simple application of the triangle inequality and the bounding condition that
$`\lVert x[n] - x_f \rVert < 1 `$

```hs
have hN_bound : ∀ n ≥ N, ‖x n‖ < 1 + ‖xf‖ := by
    intro n hn
    calc
      ‖x n‖ = ‖x n - xf + xf‖ := by ring_nf
      _ ≤ ‖x n - xf‖ + ‖xf‖ := by exact norm_add_le (x n - xf) xf
      _ < 1 + ‖xf‖ := by rel [hN n hn]
```

#### Establish the bound for n < N

We can split this into two cases.

##### Case 1: $`N < 0`$

In this case we have $`n < N < 0`$.
$\implies `x[n] = 0`$ by causality.

Any positive number upperbounds this part of the signal, so we choose $`M_1 = 1`$.

```hs
have : ∃ M1 : ℝ, ∀ n < N, ‖x n‖ < M1 := by
    by_cases hN_lt_zero : N < 0
    · use 1
      intro n _
      have : n < 0 := by linarith
      simp [hc n this]
```

##### Case 2: $`N \ge 0`$

There's only a finite number of nonzero terms $`0 \le n < N`$ due to the causal nature of
$`x[n]`$.

We can show this using a nonempty finite set $`S := \{0, \dots, [N - 1\}`$.
Then we define $`M := \displaystyle \sup_{s \in S} \lVert x[s] \rVert `$.

We assert $`M + 1`$ this is a strict upperbound for $`\lVert x[n] \rVert`$

```hs
· simp only [Int.not_lt] at hN_lt_zero
      let S := (Finset.range (Int.toNat (N + 1)))

      have S_nonempty : S.Nonempty := by
        refine Finset.nonempty_range_iff.mpr ?_
        simp only [ne_eq, Int.toNat_eq_zero, not_le]
        exact Int.lt_add_one_iff.mpr hN_lt_zero
```

We have $`\lVert x[n] \rVert ≥ 0`$ by the non-negativity of norms.
Since $`M`$ must upperbound all of these as the supremum, we have:

$`M \ge 0`$

```hs
let M := S.sup' S_nonempty (fun n ↦ ‖x ↑n‖)
      have hM : 0 ≤ M := by
        simp[M]
        exact S_nonempty

      use M + 1
```

For $`n < 0`$, $`x[n] = 0`$ by causality.

Then by transitivity:

$`x[n] = 0 \le M < M + 1`$

```hs
intro n hn
      by_cases hn_lt_zero : n < 0
      . simp [hc n hn_lt_zero]
        linarith
```

For $`\displaystyle 0 \le n < N \quad x[n] \le \sup_{0 \le n < N} \lVert x[n] \rVert`$

Substituting in $`S = \{n | 0 \le n < N\}`$, we have:

$`\displaystyle x[n] \le \underbrace{\sup_{s \in S} \lVert x[s] \rVert}_{= M} \quad 0 \le n < N`$

$`\displaystyle \le M < M + 1 \quad 0 \le n < N`$

```hs
. simp only[Int.not_lt] at hn_lt_zero
        suffices hx : ‖x n‖ ≤ M by
          linarith

        simp only [Finset.le_sup'_iff, Finset.mem_range, M, S]
        use n.toNat
        constructor
        <;> simp[hn_lt_zero]
        linarith

  obtain ⟨M, hM⟩ := this
```

Finally, we can combine the bounds for each half two get a global bound.

Since $`x[n] < M + 1 \quad \forall n < N`$ and  $`x[n] < 1 + \lVert xf \rVert \quad \forall n \ge N`$

Then we have $`x[n] < \max\{M + 1, 1 + \lVert xf \rVert\} \quad \forall n`$

```hs
use max M (1 + ‖xf‖)
  intro k
  by_cases hk : k < N
  · exact lt_max_of_lt_left (hM k hk)
  · simp [Int.not_lt] at hk
    exact lt_max_of_lt_right (hN_bound k hk)
```

A discrete signal is said to have a final value $`xf`$ iff that is its limit at infinity.

$`xf`$ is the final value of $`x` \iff \displaystyle \lim_{k \to \infty} x[k] = xf$

```hs
def HasFinalValue (x : DiscreteSignal) (xf : ℂ) := Tendsto x atTop (𝓝 xf)
```

A discrete signal with a final value is stable.

```hs
theorem hasFinalValue_implies_isStable (x : DiscreteSignal) (xf : ℂ) :
    HasFinalValue x xf → IsStable x := by
      intro h
      use xf
      exact h
```

The following two theorems state that $`f`$ is causal signal, the product of it with any signal is
also causal.

$`f`$ is causal $`\implies \forall g : \mathbb{Z} \to \mathbb{C}, \quad f \cdot g`$ is causal

```hs
theorem isCausal_of_mul_causal {f g : DiscreteSignal} (hf : IsCausal f) : IsCausal (fun k ↦ g k * f k) := by
  intro k hk
  convert mul_zero (g k)
  exact hf k hk

theorem isCausal_of_causal_mul {f g : DiscreteSignal} (hf : IsCausal f) : IsCausal (fun k ↦ f k * g k) := by
  convert isCausal_of_mul_causal (g := g) hf using 2
  rw[mul_comm]
```

The infinite sum over the negative indicies of a causal signal is zero.

$`\displaystyle f`$ is causal $`\implies \displaystyle \sum_{k = -\infty}^{-1} f[k] = 0`$

```hs
theorem summable_zero_of_causal {f : DiscreteSignal} (hf : IsCausal f) :
    Summable (fun k : NegInt ↦ f k) := by
      convert summable_zero with ⟨k, hk⟩
      exact hf k hk

theorem hasSum_zero_of_causal {f : DiscreteSignal} (hf : IsCausal f) :
    HasSum (fun k : NegInt ↦ f k) 0 := by
      convert hasSum_zero with ⟨k, hk⟩
      exact hf k hk
```

Multiplication by a causal signal can be written as an indicator function.

$`\displaystyle f`$ is causal $`\implies \displaystyle \sum_{k = -\infty}^{-1} f[k] = 0`$

```hs
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
```

**1. Unit Impulse Function (`δ(k)`)**
The **unit impulse function**, also known as the **Kronecker delta function**, is defined as:

```hs
@[simp]
def unit_impulse (k : ℤ) : ℂ :=
  if k = 0 then 1 else 0
```
This function acts as an identity under convolution and is fundamental for analyzing system responses. The impulse function can be equivalently expressed using a set indicator function:
```hs
theorem unit_impulse_equiv_indicator :
    ∀ k : ℤ, unit_impulse k = Set.indicator {0} 1 k := by
  intro k
  by_cases k_zero : k = 0
  <;> simp[k_zero]

notation "δ" => unit_impulse
```

**2. Unit Step Function (`u(k)`)**
The **unit step function**, which reperent causality in discrete time signals is defined as:

```hs
@[simp]
def unit_step (k : ℤ) : ℂ :=
  if k ≥ 0 then 1 else 0

alias u := unit_step
alias H := unit_step
```

The following utility lemmas conditions on when the unit step function is 1 or 0.

```hs
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
```

The unit step function is equivalen tot an indiicator function of 1.

```hs
lemma unit_step_equiv_indicator : ∀ k : ℤ, unit_step k = NonNegInt.indicator 1 k := by
  intro k
  unfold NonNegInt
  by_cases k_pos : k ≥ 0
  <;> simp[k_pos]
```

The unit step function is causal.

```hs
lemma unit_step_causal : IsCausal unit_step := by simp[IsCausal]

@[simp]
theorem hasSum_nat_of_unit_step_mul (f : DiscreteSignal) (S : ℂ) :
    HasSum (fun (n : ℕ) ↦ u n * f n) S ↔
    HasSum (fun (n : ℕ) ↦ f n) S := by
      simp only[u, unit_step_of_nat, one_mul]
```

This allows us to rewrite sums over ℤ in terms of sums over non-negative integers only,
a key step when handling Z-transform proofs for causal signals.

```hs
theorem causal_of_mul_unit_step (x : DiscreteSignal) :
    IsCausal (fun k : ℤ ↦ x k * u k) := by
      exact isCausal_of_mul_causal unit_step_causal
```

This confirms that causal signals only depend on present and past values,
which simplifies Z-transform computations.

```hs
theorem causal_of_unit_step_mul (x : DiscreteSignal) :
    IsCausal (fun k : ℤ ↦ u k * x k) := by
      simp only[mul_comm]
      exact causal_of_mul_unit_step x
```
This means we can safely reorder terms in proofs without worrying about violating causality
-
The rect function,from (a,b]), is defined as:


**2. Rect Function (`R(k)`)**
The **rectfunction**, which represent a signal that is non-zero for  definite, positive interval:

```hs
@[simp]
def rect (a b : ℤ) (k : ℤ) :=
  unit_step (k - a) - unit_step (k - b)
```
