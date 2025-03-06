
<center><h1>EE 546 : Automated Reasoning</h1></center>
<center><h2>Final Project Z-transforms</h2></center>

<center>
Department of Electrical and Computer Engineering<br />
Unviersity of Washington<br />
Ember CHow and Gokul Nathan<br />
Winter 2025<br />
</center>
<br />



The Z-transform is a key tool in the analysis of discrete-time control systems, yet formally verified solutions in lean 4 and matlib remain limited. To address this gap, we systematically attmempt to encode a standard Z-transform table into Lean and developed a robust library that allows control engineers to simplify Z-transform expressions using `simp_only[]`. Contrary to initial expectations, this effort proved more intricate than anticipated, owing to subtleties in representing and manipulating mathematical objects within a proof assistant. In this report, we detail how canonical Z-transform identities were encoded, discuss the underlying proof mechanisms, and highlight the advantages of automated simplifications. We have successfully enclosed a set of key Z-transform identities, proved several properties, and laid the groundwork for additional proof techniques. While these results mark a significant step toward a comprehensive toolkit, the endeavor remains ongoing. Future work will expand the set of covered identities, refine the proof infrastructure, and ultimately enable a robust, formally verified Z-transform framework for control engineering applications.

```hs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Indicator
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Basic
import Mathlib.Topology.Filter
import Mathlib.Tactic.Linarith
```
 <h2>Our custom Libraries</h2>

`Defs.lean[]` serves as the fundamental definitions file. It provides the basic mathematical structures and operations essential for encoding discrete-time signals, their properties, and the Z-transform in Lean. By collecting these primitives into a single, well-organized file, the project ensures that all higher-level modules rely on a consistent and rigorously defined foundation.

**Key Components**

1. **Discrete-Time Sequences**
   -Formalizes signals as functions `ℤ → α` (or subsets of `ℤ`), enabling precise manipulation of time-indexed data.
   - Used for: Forms the bedrock for proving common operations such as shifting, summation, and scaling on discrete-time signals.

2. **Basic Operators and Functions**
   - Defines pointwise addition and scalar multiplication for signals, laying the groundwork for linear algebraic treatments in the Z-domain.
   -Used for:Encodes time shifts (left or right), essential for handling transforms of delayed signals.

3. **Notation and Typeclasses**
   - Introduces the relevant typeclasses (e.g., for real or complex coefficients) to unify signal definitions and operations.
   - Used for:Simplifies theorem statements and proofs through user-friendly notation, reducing boilerplate and improving readability.


`Signal.lean` formalizes signal properties central to control engineering, such as causality and linearity. These properties are crucial for thorough and rigorous Z-transform proofs.

**Key Components**

1. **Signal Properties**
   - **Causality**: Defines when a signal is zero for times before a given reference, vital for modeling physically realizable systems.
   - **Linearity**: Establishes conditions for superposition and homogeneity in signals, enabling straightforward reasoning about linear systems.

2. **Signal Constructions**
   - Provides examples like impulse, step, and ramp signals, along with foundational proofs of their properties.
   - Demonstrates how signals can be combined (e.g., summed or shifted) while preserving or modifying fundamental attributes.

3. **Theorems and Lemmas**
   - Supplies initial proofs and templates for reasoning about signal transformations.


```hs
import EE546ECGNFP.Defs -- Useful definitions for implementing engineering Z-transforms
import EE546ECGNFP.Signal -- USeful examining the signal properties

open Filter Topology Controls Controls.Discrete

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000




@[simp]
noncomputable def zt_kernel (x : DiscreteSignal) (z : ℂ) : ℤ → ℂ :=
  fun k ↦ x (k) * z^(-k : ℤ)

@[simp]
noncomputable def ZTransform (x : DiscreteSignal) (z : ℂ) :=
  ∑' k : ℤ, x (k) * z^(-k : ℤ)


def HasZTransform (f : DiscreteSignal) (F : ℂ → ℂ) (z : ℂ) := HasSum (fun (k : ℤ) ↦ f k * z ^ (-k : ℤ)) (F z)

def ZTransformable (f : DiscreteSignal) (z : ℂ) := Summable fun k ↦ f k * z ^ (-k)

@[simp]
noncomputable def ZTransformUnilateral (x : DiscreteSignal) (z : ℂ) :=
  ∑' k : ℕ, x (k) * z^(-k : ℤ)

def HasZTransformUnilateral (x : DiscreteSignal) (z : ℂ) := HasSum (fun (n : ℕ) ↦ x n * z ^ (-n : ℤ))

@[simp]
noncomputable def ZTransformUnilateral' (x : DiscreteSignal) (z : ℂ) :=
  ∑' k : NonNegInt, x (k) * z ^ (-↑k : ℤ)

@[simp]
noncomputable def DiscreteTimeFourierTransform (x : DiscreteSignal) (ω : ℝ) :=
  ∑' k : ℤ, x (k) * Complex.exp (-j * ω * k)

@[simp]
alias ZT := ZTransform

@[simp]
alias DTFT := DiscreteTimeFourierTransform

notation "𝓩" => ZTransform
notation "𝓩_u" => ZTransformUnilateral
notation "𝓕_d" => DiscreteTimeFourierTransform

variable (x : DiscreteSignal)
```
**Fundamental Discrete-Time Signals and Their Z-Transforms**
In this section, we define and analyze two fundamental discrete-time signals: the **unit impulse** (`δ(k)`) and the **unit step** (`u(k)`). These signals play a crucial role in system analysis, forming the basis for deriving the Z-transform of more complex signals. We also provide key theorems related to their properties, including causality and summability, and prove their corresponding Z-transforms. THis is the first fundamental contribution we make towards the problem of encoding digital control systems in lean 4.


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
We now attempt to prove one of the fundamental Z-transform relationships:

The Z-transform of a shifted unit impulse function \( \delta(k - k_0) \) is given by:
$
\mathcal{Z} \{ \delta(k - k_0) \} = z^{-k_0}
$

```hs
theorem zt_unit_impulse {z : ℂ} (k₀ : ℤ) : HasZTransform (fun k ↦ δ (k - k₀)) (fun z : ℂ ↦ (z ^ (-k₀))) z := by
  rw[HasZTransform]
  simp

  have : ∀ k : ℤ, k - k₀ = 0 ↔ k = k₀ := by intro _; exact Int.sub_eq_zero
  simp only[this]

  have : ∀ k : ℤ, ∀ z : ℂ, (if k = k₀ then (z ^ k)⁻¹ else 0) = (if k = k₀ then z ^ (-k₀) else 0) := by
    intro k _
    by_cases hk : k = k₀
    <;> simp[hk]

  simp [this]
  exact hasSum_ite_eq k₀ (z ^ k₀)⁻¹
```

**2. Unit Step Function (`δ(k)`)**
The **unit impulse function**, also known as the **Kronecker delta function**, is defined as:

```hs
@[simp]
def unit_step (k : ℤ) : ℂ :=
  if k ≥ 0 then 1 else 0

@[simp]
theorem unit_step_of_nat : ∀ (n : ℕ), unit_step n = 1 := by
  intro n
  simp

@[simp]
theorem unit_step_of_nonneg : ∀ (k : NonNegInt), unit_step k = 1 := by
  intro ⟨k, hk⟩
  simp
  exact hk

@[simp]
theorem unit_step_of_pos : ∀ (k : PosInt), unit_step k = 1 := by
  intro ⟨k, hk⟩
  simp
  exact Int.le_of_lt hk

@[simp]
theorem unit_step_of_neg : ∀ (k : NegInt), unit_step k = 0 := by
  intro ⟨k, hk⟩
  simp
  exact hk

theorem unit_step_equiv_indicator : ∀ k : ℤ, unit_step k = NonNegInt.indicator 1 k := by
  intro k
  unfold NonNegInt
  by_cases k_pos : k ≥ 0
  <;> simp[k_pos]

alias u := unit_step
alias H := unit_step

theorem unit_step_causal : IsCausal unit_step := by simp[IsCausal]

@[simp]
theorem hasSum_nat_of_unit_step_mul (f : DiscreteSignal) (S : ℂ) :
    HasSum (fun (n : ℕ) ↦ u n * f n) S ↔
    HasSum (fun (n : ℕ) ↦ f n) S := by
      simp only[u, unit_step_of_nat, one_mul]


theorem causal_of_mul_unit_step (x : DiscreteSignal) :
    IsCausal (fun k : ℤ ↦ x k * u k) := by
      intro k hk
      change k < 0 at hk
      have : ¬(k ≥ 0) := by exact Int.not_le.mpr hk
      simp only[u, unit_step, this, reduceIte, mul_zero]


theorem causal_of_unit_step_mul (x : DiscreteSignal) :
    IsCausal (fun k : ℤ ↦ u k * x k) := by
      simp only[mul_comm]
      exact causal_of_mul_unit_step x
```
-
The rect function is one on [a, b)

```hs
@[simp]
def rect (a b : ℤ) (k : ℤ) :=
  unit_step (k - a) - unit_step (k - b)

theorem ZTransformToDTFT : ∀ x : DiscreteSignal, (fun ω : ℝ => 𝓩 x (Complex.exp (j * ω))) = 𝓕_d x := by
  intro x
  ext ω
  simp
  apply tsum_congr
  intro k
  calc
    x k * (Complex.exp (j * ↑ω) ^ k)⁻¹
      = x k * (Complex.exp (j * ↑ω * ↑k))⁻¹ := by rw [← Complex.exp_int_mul (j * ↑ω) k]; ring_nf
    _ = x k * Complex.exp (-(j * ↑ω * ↑k)) := by rw [←Complex.exp_neg (j * ↑ω * ↑k)]




theorem ZTUnilateral_hasSum_equiv {z : ℂ} {a : ℂ} (x : DiscreteSignal) :
  HasSum (fun n : ℕ ↦ x n * z ^ (-n : ℤ)) a ↔
  HasSum (fun k : NonNegInt ↦ x k * z ^ (-k : ℤ)) a := by
    exact Equiv.hasSum_iff nonNegInt_nat_equiv.symm (a := a) (
      f := fun (k : NonNegInt) ↦ x k * z ^ (-k : ℤ))

theorem ZTUnilateral_summable_equiv{z : ℂ} (x : DiscreteSignal) :
  Summable (fun n : ℕ ↦ x n * z ^ (-n : ℤ)) ↔
  Summable (fun k : NonNegInt ↦ x k * z ^ (-k : ℤ)) := by
    exact Equiv.summable_iff nonNegInt_nat_equiv.symm (
      f := fun (k : NonNegInt) ↦ x k * z ^ (-k : ℤ))


theorem ZTUnilateral_tsum_equiv {z : ℂ} (x : DiscreteSignal) :
  (ZTransformUnilateral x) z = (ZTransformUnilateral' x) z := by
    exact Equiv.tsum_eq nonNegInt_nat_equiv.symm (
      fun (k : NonNegInt) ↦ x k * z ^ (-k : ℤ)
    )

theorem indicator_one_mul {α β : Type*} [Semiring β] {A : Set α} (a : α) (f : α → β) :
    A.indicator 1 a * f a = A.indicator (fun a' ↦ f a') a := by
      by_cases ha : a ∈ A
      <;> simp[ha]

theorem zt_summable_causal {z : ℂ} {f : DiscreteSignal} :
    (hf : IsCausal f) →
    Summable (fun (k : ℤ) ↦ f k * z ^ (-k : ℤ)) ↔
    Summable (fun (n : ℕ) ↦ f n * z ^ (-n : ℤ)) := by
      intro hf
      apply Iff.intro
      . intro hmp
        have h_ind : (fun k : ℤ ↦ f k * z^(-k : ℤ)) = (fun k : ℤ ↦ NonNegInt.indicator (fun k ↦ f k * z^(-k : ℤ)) k) := by
          ext k
          by_cases hk : k < 0

          . have : k ∉ NonNegInt := by exact Int.not_le.mpr hk
            simp only[Set.indicator_of_not_mem this, hf k hk, zero_mul]

          . simp[Int.not_lt] at hk
            change k ∈ NonNegInt at hk
            simp only[Set.indicator_of_mem hk]

        rw[h_ind] at hmp
        simp only[ZTUnilateral_summable_equiv]
        exact (summable_subtype_iff_indicator).mpr hmp

      . intro hmpr
        simp only[←summable_univ (f := fun k : ℤ ↦ f k * z ^ (-k : ℤ))]
        convert Summable.add_compl (s := NegInt) (f := fun k : ℤ ↦ f k * z ^ (-k : ℤ)) ?_ ?_

        . exact summable_univ (f := fun k : ℤ ↦ f k * z ^ (-k : ℤ))

        . change Summable (fun k : NegInt ↦ f k * z ^ (-k : ℤ))
          convert summable_zero with k
          convert zero_mul (z ^ (-k : ℤ))
          obtain ⟨k, hk⟩ := k
          change k < 0 at hk
          change f k = 0
          exact hf k hk

        . change Summable (fun k : ↑NegIntᶜ ↦ f k * z ^ (-k : ℤ))
          rw[NegIntComp]
          simp only[←ZTUnilateral_summable_equiv]
          exact hmpr



theorem zt_sum_causal {z : ℂ} {f : DiscreteSignal} {S : ℂ} :
    (hf : IsCausal f) →
    HasSum (fun (k : ℤ) ↦ f k * z ^ (-k : ℤ)) S ↔
    HasSum (fun (n : ℕ) ↦ f n * z ^ (-n : ℤ)) S := by
      intro hf
      apply Iff.intro
      . intro hmp
        have h_ind : (fun k : ℤ ↦ f k * z^(-k : ℤ)) = (fun k : ℤ ↦ NonNegInt.indicator (fun k ↦ f k * z^(-k : ℤ)) k) := by
          ext k
          by_cases hk : k < 0

          . have : k ∉ NonNegInt := by exact Int.not_le.mpr hk
            simp only[Set.indicator_of_not_mem this, hf k hk, zero_mul]

          . simp[Int.not_lt] at hk
            change k ∈ NonNegInt at hk
            simp only[Set.indicator_of_mem hk]

        rw[h_ind] at hmp
        simp only[ZTUnilateral_hasSum_equiv]
        exact (hasSum_subtype_iff_indicator).mpr hmp

      . intro hmpr
        simp only[←hasSum_univ (f := fun k : ℤ ↦ f k * z ^ (-k : ℤ))]
        rw[←neg_nonneg_union]
        convert HasSum.add_disjoint (a := 0) (b := S) (f := fun k : ℤ ↦ f k * z ^ (-k : ℤ)) int_neg_nonneg_disjoint ?_ ?_

        . rw[zero_add]

        . change HasSum (fun k : NegInt ↦ f k * z ^ (-k : ℤ)) 0
          convert hasSum_zero with k
          convert zero_mul (z ^ (-k : ℤ))
          obtain ⟨k, hk⟩ := k
          change k < 0 at hk
          change f k = 0
          exact hf k hk

        . change HasSum (fun k : NonNegInt ↦ f k * z ^ (-k : ℤ)) S
          simp only[←ZTUnilateral_hasSum_equiv]
          exact hmpr

theorem zt_sum_unit_step {z : ℂ} {f : DiscreteSignal} {S : ℂ} :
    HasSum (fun (k : ℤ) ↦ u k * f k * z ^ (-k : ℤ)) S ↔
    HasSum (fun (n : ℕ) ↦ f n * z ^ (-n : ℤ)) S := by

      convert zt_sum_causal (causal_of_unit_step_mul f) with n
      simp[u]

theorem zt_unit_step {z : ℂ} (h_roc : ‖z‖ > 1) : HasZTransform u (fun z ↦ (1 / (1 - z⁻¹))) z := by
  rw[HasZTransform]

  have : ∀ k, u k * z ^ (-k) = u k * 1 * z ^ (-k) := by simp
  simp only [this]

  refine' zt_sum_unit_step.mpr _
  simp
  simp only[←inv_pow]

  refine' hasSum_geometric_of_norm_lt_one _
  rw[norm_inv, inv_lt_comm₀] <;> linarith
```

# Properties of the Z-Transform

| No. | Name                          | Formula                                                                                                                                  |
|----:|:------------------------------|:-----------------------------------------------------------------------------------------------------------------------------------------|
| 1   | **Linearity**                 | $ \mathcal{Z}\{a\,f_1(k) + b\,f_2(k)\} \;=\; a\,F_1(z)\;+\;b\,F_2(z)$                                                      |
| 2   | **Time Delay**                | $ \mathcal{Z}\{f(k - n)\} \;=\; z^{-n}\,F(z)$                                                                             |
| 3   | **Time Advance**              | $ \mathcal{Z}\{f(k + 1)\} \;=\; z\,F(z)\;-\;z\,f(0)$<br>$ \mathcal{Z}\{f(k + n)\} \;=\; z^n\,F(z)\;-\;z^{n-1}f(0)\;-\;\dots\;-\;z\,f(n-1)$ |
| 4   | **Discrete-Time Convolution** | $ \mathcal{Z}\{f_1(k)\ast f_2(k)\} \;=\; F_1(z)\,F_2(z)$                                                                   |
| 5   | **Multiplication by Exponential** | $ \mathcal{Z}\{a^k\,f(k)\} \;=\; F(a\,z)$                                                                               |
| 6   | **Complex Differentiation**   | $ \mathcal{Z}\{k^m\,f(k)\} \;=\; \Bigl(-\,z\,\frac{d}{dz}\Bigr)^{m}F(z)$                                                   |
| 7   | **Final Value Theorem**       | $ f(\infty)\;=\;\lim_{k\to\infty}f(k)\;=\;\lim_{z\to 1}\bigl(1 - z^{-1}\bigr)\,F(z)$                                       |
| 8   | **Initial Value Theorem**     | $ f(0)\;=\;\lim_{k\to 0}f(k)\;=\;\lim_{z\to \infty}F(z)$                                                                   |


```hs
theorem ZTransform_linear (z : ℂ) (f₁ f₂ : DiscreteSignal) (F₁ F₂ : ℂ → ℂ) (z : ℂ) (a b : ℂ) (hz₁ : HasZTransform f₁ F₁ z)  (hz₂ : HasZTransform f₂ F₂ z) :
  HasZTransform (fun k => a * f₁ k + b * f₂ k) (fun z => a * F₁ z + b * F₂ z) z := by
  unfold HasZTransform
  sorry

--   simp only[ZTransform]
--   calc
--   ∑' (k : ℤ), (a * f₁ k + b * f₂ k) * z ^ (-k) = ∑' (k : ℤ), (a * f₁ k * z ^ (-k) + b * f₂ k * z ^ (-k)) := by group

--   _ = ∑' (k : ℤ), a * f₁ k * z ^ (-k) + ∑' (k : ℤ), b * f₂ k * z ^ (-k) := by
--     rw[tsum_add]

--   _ = ∑' (k : ℤ), a * (f₁ k * z ^ (-k)) + ∑' (k : ℤ), b * (f₂ k * z ^ (-k)) := by group
--   _ = a * ∑' (k : ℤ), f₁ k * z ^ (-k) + b * ∑' (k : ℤ), f₂ k * z ^ (-k) := by rw[tsum_mul_left, tsum_mul_left]

-- @[simp]
-- theorem ZTransform_time_delay (f : DiscreteSignal) (n : ℤ) (z : ℂ) :  𝓩 (fun k => f (k - n)) z = z ^ (-n) * 𝓩 f z := by
--   simp only[ZTransform]

--   let g := fun k : ℤ => f (k - n) * z ^ (-k)
--   let h := fun m : ℤ => f m * z ^ (-(m + n))

--   have h_i : (fun k => f (k - n) * z ^ (-k)) = (fun m => f m * z ^ (-(m + n))) := by
--     ext m
--     -- ring_nf
--   sorry

-- @[simp]
-- theorem ZTransform_time_advance_one (f : DiscreteSignal) (z : ℂ) : 𝓩 (fun k => f (k + 1)) z = z * 𝓩 f z - z * f 0 := by
--   sorry

-- @[simp]
-- theorem ZTransform_time_advance_n (f : DiscreteSignal) (n : ℕ) (z : ℂ) : 𝓩 (fun k => f (k + n)) z = z^n * 𝓩 f z - ∑ i in Finset.range n, z^(n - i) * f i := by
--   sorry

-- -- @[simp]
-- theorem ZTransform_convolution (f g : DiscreteSignal) (z : ℂ) : 𝓩 (discrete_convolution f g) z = 𝓩 f z * 𝓩 g z := by
--   rw [ZTransform] -- ∑' (k : ℤ), discrete_convolution f g k * z ^ (-k) = 𝓩 f z * 𝓩 g z
--   simp only [discrete_convolution] -- ∑' (k : ℤ), (∑' (m : ℤ), f m * g (k - m)) * z ^ (-k) = 𝓩 f z * 𝓩 g z
--   let h := fun k => ∑' m : ℤ, f m * g (k - m)
--   let t := fun k => h k * z ^ (-k)
--   sorry

theorem ZTransform_exp_mul (f : DiscreteSignal) (F : ℂ → ℂ) (ROC : Set ℂ) :
 (∀ (z : ROC), HasZTransform f F z) →
 (∀ z a : ℂ, z * a ∈ ROC → (HasZTransform (λ k ↦ a^ (-k) * f k) z (F (z * a)))) := by
  unfold HasZTransform -- HasSum (fun k ↦ f k * ↑z ^ (-k)) (F ↑z)) →  ∀ (z a : ℂ), z * a ∈ ROC → HasSum (fun k ↦ (fun k ↦ a ^ (-k) * f k) k * z ^ (-k)) (F (z * a))
  intro h --  ∀ (z : ↑ROC), HasSum (fun k ↦ f k * ↑z ^ (-k)) (F ↑z)
  intro z a hza --  z * a ∈ ROC ⊢ HasSum (fun k ↦ (fun k ↦ a ^ (-k) * f k) k * z ^ (-k)) (F (z * a))
  have :  (λ k ↦ a ^ (-k) * f k * z ^ (-k)) =  (λ k ↦ (a*z)^(-k) * f k) := by
    ext k
    calc
      a ^ (-k) * f k * z ^ (-k)
        =  f k * a ^ (-k) * z ^ (-k) := by ring
      _ = f k * (a * z)^ (-k) :=  by rw[mul_zpow, mul_assoc]
      _ = (a * z) ^ (-k) * f k := by rw[mul_comm]

  simp only[this]
  simp only[mul_comm] -- asSum (fun k ↦ (a * z) ^ (-k) * f k) (F (z * a))
  exact h ⟨z * a, hza⟩

theorem ztransormable_of_stable_and_causal (x : DiscreteSignal) (z : ℂ) (h_roc : ‖z‖ > 1) : IsStable x → IsCausal x → ZTransformable x z := by
  intro hs hc
  have hb : IsBoundedSignal x := by apply isStableAndCausal_implies_isBounded x hs hc
  rw [ZTransformable]
  obtain ⟨m, hm⟩ := hb
  apply (zt_summable_causal hc).mpr
  refine Summable.of_norm_bounded ?_ ?_ ?_  --⊢ Summable fun a ↦ ‖x a * z ^ (-a)‖
  . exact fun k ↦ ‖m‖ * ‖z^(-k : ℤ)‖

  . refine Summable.mul_left (f := fun n : ℕ ↦ ‖z^(-n : ℤ)‖) ‖m‖ ?_
    simp only[zpow_neg, ←inv_zpow]
    simp only[zpow_natCast]
    refine summable_norm_geometric_of_norm_lt_one ?_
    rw[norm_inv, inv_lt_comm₀] <;> linarith

  . intro n
    calc
    ‖x ↑n * z ^ (-n : ℤ)‖
      = ‖x ↑n‖ * ‖ z ^ (-n : ℤ)‖ := by rw[norm_mul]
     _ ≤ m * ‖z ^ (-n : ℤ)‖ := by rel [hm n]
      _ ≤ ‖m‖ * ‖z ^ (-n : ℤ)‖ := by
        have : m ≤ ‖m‖ := by exact Real.le_norm_self m
        rel[this]




theorem zt_FinalValueTheorem
  (x : DiscreteSignal) (xf : ℂ) :
  IsCausal x → HasFinalValue x xf →
  Tendsto (fun z ↦ (z - 1) * (𝓩 x z)) (𝓝 1) (𝓝 xf) := by
    intro hx_causal
    intro hxf
    simp only[ZTransform]
    sorry


-- theorem zt_InitialValueTheorem
--   (x : DiscreteSignal) (xf : ℂ) :
--   IsCausal x → HasFinalValue x xf →
--   Tendsto (fun z ↦ (z - 1) * (𝓩 x z)) (𝓝 1) (𝓝 xf) := by
--     intro hx_causal
--     intro hxf
--     simp only[ZTransform]
--     sorry
```
