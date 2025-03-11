
<center><h1>EE 546 : Automated Reasoning</h1></center>
<center><h2>Final Project Z-transforms</h2></center>

<center>
Department of Electrical and Computer Engineering<br />
Unviersity of Washington<br />
Ember CHow and Gokul Nathan<br />
Winter 2025<br />
</center>
<br />


The explosion of artificial Intelignece (AI) and Machine Learning (ML), has promoted rexamination many long standing prinicples in the field of control theory and applications <sup>1</sup>. From NVIDIA's latest COSMOS foundation models for physical AI development <sup>2</sup> to Harvard' Generalist Medical AI (GMAI) <sup>3</sup>, AI and ML are often used as a method of solving multi-objective, contrained optimization problems in numerous industries including aerospace, agricutlutral, medical, and robotics <sup>4-7</sup>. Given the high impact nature of these industries, there is a critical need for interpretable, generalizable, explainable, and, perhaps most importantly, certifiable models for safety critcal applications. One of the key challenges in ensuring safety and reliability in control systems is the rigorous verification of mathematical properties <sup>8</sup>. A traditional approach is to encode such systems using the language of control theory, understanding how such systems transform inputs into outputs, and then proving mathematical properties of these transformations. However, manual encoding and independent verification is not a scalable approach, given the rapid proliferation of AI/ML systems <sup>9</sup>. This highlights a key gap in current landscape: verificable and scalable methods of evaulavating and certification of the AI/ML models. Modern theorem provers, like Lean4, bridge this gap by providing a rigorous yet scalable approach for formal verification using mechanized proof techniques based on classsical approaches. The Z-transform is a foundational tool in the analysis of discrete-time control systems, but it is not well supported in Lean 4 and Mathlib's digital signal processing capabilities remain limited.

To address this gap, we propose encoding a standard Z-transform table, as described in <sup>10</sup>, into the language and additionally exposing APIs to interact with these definitions. Contrary to initial expectations, this effort proved more challenging than anticipated due to a lack of existing foundational results, either because they were wholly missing or because they were not specialized from more general results. In this retrospective report, we detail how canonical Z-transform identities were encoded, discuss the underlying proof mechanisms, and highlight the advantages of automated simplifications. The authors have successfully enclosed a few of key Z-transform identities, proved several properties, and laid the groundwork for additional proof techniques. While these results mark a significant step toward a comprehensive toolkit, more efforts will be needed to meet the initial proposal. Future work should expand the set of covered identities, refine the proof infrastructure, and ultimately enable a robust and unified Z-transform verification framework for control engineering applications.

<h3>Works Cited</h3>

1. Bensoussan, A., Li, Y., Nguyen, D.P.C., Tran, M.B., Yam, S.C.P. and Zhou, X., 2022. Machine learning and control theory. In Handbook of numerical analysis (Vol. 23, pp. 531-558). Elsevier

2. Agarwal, N., Ali, A., Bala, M., Balaji, Y., Barker, E., Cai, T., Chattopadhyay, P., Chen, Y., Cui, Y., Ding, Y. and Dworakowski, D., 2025. Cosmos world foundation model platform for physical ai. arXiv preprint arXiv:2501.03575.

3. Moor, M., Banerjee, O., Abad, Z.S.H., Krumholz, H.M., Leskovec, J., Topol, E.J. and Rajpurkar, P., 2023. Foundation models for generalist medical artificial intelligence. Nature, 616(7956), pp.259-265.

4. Brunton, S.L., Nathan Kutz, J., Manohar, K., Aravkin, A.Y., Morgansen, K., Klemisch, J., Goebel, N., Buttrick, J., Poskin, J., Blom-Schieber, A.W. and Hogan, T., 2021. Data-driven aerospace engineering: reframing the industry with machine learning. Aiaa Journal, 59(8), pp.2820-2847.

5. Eli-Chukwu, N.C., 2019. Applications of artificial intelligence in agriculture: A review. Engineering, Technology & Applied Science Research, 9(4).

6. Chella, A., Iocchi, L., Macaluso, I. and Nardi, D., 2006. Artificial Intelligence and Robotics. Intelligenza Artificiale, 3(1-2), pp.87-93.

7. Sun, Q., Akman, A. and Schuller, B.W., 2025. Explainable artificial intelligence for medical applications: A review. ACM Transactions on Computing for Healthcare, 6(2), pp.1-31.

8. Prabhakar, P., 2011. Approximation based safety and stability verification of hybrid systems. University of Illinois at Urbana-Champaign.

9. Kaminwar, S.R., Goschenhofer, J., Thomas, J., Thon, I. and Bischl, B., 2023. Structured verification of machine learning models in industrial settings. Big Data, 11(3), pp.181-198.

10. Fadali, M.S. and Visioli, A., 2009. Digital control engineering: analysis and design. Academic press.

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
import Mathlib.Data.Complex.Basic
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




-- @[simp]
-- noncomputable def zt_kernel (x : DiscreteSignal) (z : ℂ) : ℤ → ℂ :=
--   fun k ↦ x (k) * z^(-k : ℤ)

@[simp]
noncomputable def ZTransform (x : DiscreteSignal) (z : ℂ) :=
  ∑' k : ℤ, x (k) * z^(-k : ℤ)


@[simp]
def HasZTransform (f : DiscreteSignal) (F : ℂ → ℂ) (z : ℂ) := HasSum (fun (k : ℤ) ↦ f k * z ^ (-k : ℤ)) (F z)

@[simp]
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
In this section, we define and analyze three fundamental discrete-time signals: the **unit impulse** (`δ(k)`), the **unit step** (`u(k)`) and the **rect function**. These signals play a crucial role in system analysis, forming the basis for deriving the Z-transform of more complex signals. We also provide key theorems related to their properties, including causality and summability, and prove their corresponding Z-transforms. THis is the first fundamental contribution we make towards the problem of encoding digital control systems in lean 4.


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
  simp[Int.sub_eq_zero]
  convert hasSum_ite_eq k₀ (z ^ k₀)⁻¹
```

**2. Unit Step Function (`δ(k)`)**
The **unit step function**, which reperent causality in discrete time signals is defined as:

```hs
@[simp]
def unit_step (k : ℤ) : ℂ :=
  if k ≥ 0 then 1 else 0
```

we now expand the defiriniton of all unit step function to include non-negative, positive (these have to be shown to be equivalent) and negtive indices. We do this to force coercion for lean 4

```hs
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
```
In this sub-section, we provide a detailed explanation of several key theorems related to the unit step function `unit_step` (aliased as `u`). These theorems establish fundamental properties such as causality and summability, and they show how multiplication by the unit step function affects discrete-time signals. Specifically, we establish that multiplying a signal by \( u(k) \) enforces causality and preserves summability.

We formalize these properties in Lean so that the **causal nature of our signals has specific implications in the Z-transform**. By encoding these results, we ensure that Lean can automatically reason about causality in **Z-transform proofs**, particularly when proving properties like the **region of convergence (ROC)** and **linearity of summation**.

These causal properties allow us to **exploit simplifications** in proofs, ensuring that when working with the Z-transform of causal signals, we can restrict summation to the non-negative domain, rather than dealing with the entire integer set $ \mathbb{Z} $.
```hs
theorem unit_step_causal : IsCausal unit_step := by simp[IsCausal]

@[simp]
theorem hasSum_nat_of_unit_step_mul (f : DiscreteSignal) (S : ℂ) :
    HasSum (fun (n : ℕ) ↦ u n * f n) S ↔
    HasSum (fun (n : ℕ) ↦ f n) S := by
      simp only[u, unit_step_of_nat, one_mul]
```
This allows us to rewrite sums over ℤ in terms of sums over non-negative integers only, a key step when handling Z-transform proofs for causal signals.
```hs
theorem causal_of_mul_unit_step (x : DiscreteSignal) :
    IsCausal (fun k : ℤ ↦ x k * u k) := by
      exact isCausal_of_mul_causal unit_step_causal
```
This confirms that causal signals only depend on present and past values, which simplifies Z-transform computations.
```hs
theorem causal_of_unit_step_mul (x : DiscreteSignal) :
    IsCausal (fun k : ℤ ↦ u k * x k) := by
      simp only[mul_comm]
      exact causal_of_mul_unit_step x
```
This means we can safely reorder terms in proofs without worrying about violating causality
```hs
theorem ZTUnilateral_hasSum_equiv {z : ℂ} {a : ℂ} (x : DiscreteSignal) :
  HasSum (fun n : ℕ ↦ x n * z ^ (-n : ℤ)) a ↔
  HasSum (fun k : NonNegInt ↦ x k * z ^ (-k : ℤ)) a := by
    exact Equiv.hasSum_iff nonNegInt_nat_equiv.symm (a := a) (
      f := fun (k : NonNegInt) ↦ x k * z ^ (-k : ℤ))
```
 This theorem ensures that we can switch between summing over ℕ and summing over NonNegInt, a more structured subset of  ℤ. This transition is useful for formalizing summation equivalences in Lean
```hs
theorem ZTUnilateral_summable_equiv{z : ℂ} (x : DiscreteSignal) :
  Summable (fun n : ℕ ↦ x n * z ^ (-n : ℤ)) ↔
  Summable (fun k : NonNegInt ↦ x k * z ^ (-k : ℤ)) := by
    exact Equiv.summable_iff nonNegInt_nat_equiv.symm (
      f := fun (k : NonNegInt) ↦ x k * z ^ (-k : ℤ))
```
This theorem ensures that summability properties hold when switching between standard natural number summations and structured integer sets
```hs
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
        simp only[ZTUnilateral_summable_equiv]
        rw[indicator_of_IsCausal_mul hf] at hmp
        exact (summable_subtype_iff_indicator).mpr hmp

      . intro hmpr
        simp only[←summable_univ (f := fun k : ℤ ↦ f k * z ^ (-k : ℤ))]
        convert Summable.add_compl (s := NegInt) (f := fun k : ℤ ↦ f k * z ^ (-k : ℤ)) ?_ ?_

        . exact summable_univ (f := fun k : ℤ ↦ f k * z ^ (-k : ℤ))

        . change Summable (fun k : NegInt ↦ f k * z ^ (-k : ℤ))
          refine summable_zero_of_causal (f := fun k ↦ f k * z ^ (-k : ℤ)) ?_
          exact isCausal_of_causal_mul hf

        . change Summable (fun k : ↑NegIntᶜ ↦ f k * z ^ (-k : ℤ))
          rw[NegIntComp]
          simp only[←ZTUnilateral_summable_equiv]
          exact hmpr
```
This theorem shows that if a signal is causal, we can restrict summation to non-negative indices. It justifies the transition from bilateral to unilateral Z-transforms.
```hs
theorem zt_sum_causal {z : ℂ} {f : DiscreteSignal} {S : ℂ} :
    (hf : IsCausal f) →
    HasSum (fun (k : ℤ) ↦ f k * z ^ (-k : ℤ)) S ↔
    HasSum (fun (n : ℕ) ↦ f n * z ^ (-n : ℤ)) S := by
      intro hf
      apply Iff.intro
      . intro hmp
        simp only[ZTUnilateral_hasSum_equiv]
        rw[indicator_of_IsCausal_mul hf] at hmp
        exact (hasSum_subtype_iff_indicator).mpr hmp

      . intro hmpr
        simp only[←hasSum_univ (f := fun k : ℤ ↦ f k * z ^ (-k : ℤ))]
        rw[←neg_nonneg_union]
        convert HasSum.add_disjoint (a := 0) (b := S) (f := fun k : ℤ ↦ f k * z ^ (-k : ℤ)) int_neg_nonneg_disjoint ?_ ?_

        . rw[zero_add]

        . change HasSum (fun k : NegInt ↦ f k * z ^ (-k : ℤ)) 0
          refine hasSum_zero_of_causal (f := fun k ↦ f k * z ^ (-k : ℤ)) ?_
          exact isCausal_of_causal_mul hf

        . change HasSum (fun k : NonNegInt ↦ f k * z ^ (-k : ℤ)) S
          simp only[←ZTUnilateral_hasSum_equiv]
          exact hmpr


theorem zt_sum_unit_step {z : ℂ} {f : DiscreteSignal} {S : ℂ} :
    HasSum (fun (k : ℤ) ↦ u k * f k * z ^ (-k : ℤ)) S ↔
    HasSum (fun (n : ℕ) ↦ f n * z ^ (-n : ℤ)) S := by

      convert zt_sum_causal (causal_of_unit_step_mul f) with n
      simp[u]
```
The preceding sub-theorems systematically reduce summation complexity and enforce causality in formal Z-transform proofs. They ensure that we only consider non-negative indices, enabling a rigorous transition from bilateral to unilateral Z-transforms. With all that done, we can finaly prove the unit step Z-transformation 
```hs
theorem zt_unit_step {z : ℂ} (h_roc : ‖z‖ > 1) : HasZTransform u (fun z ↦ (1 / (1 - z⁻¹))) z := by
  rw[HasZTransform]

  suffices ∀ k, u k * z ^ (-k) = u k * 1 * z ^ (-k) by
    simp only [this]

    refine' zt_sum_unit_step.mpr _
    simp
    simp only[←inv_pow]

    refine' hasSum_geometric_of_norm_lt_one _
    rw[norm_inv, inv_lt_comm₀] <;> linarith

  simp
```
-
The rect function,from (a,b]), is defined as:


**2. Rect Function (`R(k)`)**
The **rectfunction**, which represent a signal that is non-zero for  definite, positive interval:

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
theorem zt_mul_left (z : ℂ) (f₁ : DiscreteSignal) (F₁ : ℂ → ℂ) (a : ℂ)
(hz₁ : HasZTransform f₁ F₁ z) :
  HasZTransform (fun k => a * f₁ k) (fun z => a * F₁ z) z := by
  unfold HasZTransform
  change HasSum (fun k ↦ a * f₁ k * z ^ (-k)) (( a * F₁ z))
  simp only[mul_assoc]
  apply HasSum.mul_left a hz₁

theorem zt_mul_right (z : ℂ) (f₁ : DiscreteSignal) (F₁ : ℂ → ℂ) (a : ℂ)
(hz₁ : HasZTransform f₁ F₁ z) :
  HasZTransform (fun k => f₁ k * a) (fun z => F₁ z * a) z := by
  unfold HasZTransform
  change HasSum (fun k ↦  f₁  k  * a * z ^ (-k) ) ((F₁ z * a))
  have: (λ k ↦ f₁  k  * a * z ^ (-k)) = (λ k ↦ f₁  k   * z ^ (-k) * a ):= by
    ext k
    ring_nf
  -- ⊢ HasSum (fun k ↦ f₁ k * a * z ^ (-k)) (F₁ z * a)
  simp only[this]
  apply HasSum.mul_right a hz₁

theorem zt_add (z : ℂ) (f₁ f₂ : DiscreteSignal) (F₁ F₂ : ℂ → ℂ) (hz₁ : HasZTransform f₁ F₁ z)  (hz₂: HasZTransform f₂ F₂ z) :
   HasZTransform (fun k => f₁ k + f₂ k) (fun z => F₁ z + F₂ z) z := by
    unfold HasZTransform -- (fun k ↦ (fun k ↦ f₁ k + f₂ k) k * z ^ (-k)) ((fun z ↦ F₁ z + F₂ z) z)
    change HasSum (fun k ↦ (f₁ k + f₂ k) * z ^ (-k)) ( F₁ z + F₂ z)
    have :  (fun k ↦ (f₁ k + f₂ k) * z ^ (-k)) = (fun k ↦(f₁ k) * z ^ (-k) + (f₂ k) * z ^ (-k)) := by
      ext k
      ring_nf
    simp only[this]
    apply HasSum.add  hz₁ hz₂
```
 The following function facilitates the decomposition of complex systems into simpler components for independent verification. It would als be useful in superposition-based control design and verification.
 
```hs
theorem ZTransform_linear (f₁ f₂ : DiscreteSignal) (F₁ F₂ : ℂ → ℂ) (z : ℂ) (a b : ℂ) (hz₁ : HasZTransform f₁ F₁ z)  (hz₂ : HasZTransform f₂ F₂ z) :
  HasZTransform (fun k => a * f₁ k + b * f₂ k) (fun z => a * F₁ z + b * F₂ z) z := by
  convert zt_add z (fun k => a * f₁ k) (fun k => b * f₂ k) ?_ ?_ ?add_left ?add_right
  <;> apply zt_mul_left
  <;> assumption
```
 The following function helps analyze delay effects in control loops and stability assessments, essential for predictive and adaptive control strategies.
```hs
@[simp]
theorem ZTransform_time_delay {f : DiscreteSignal} {F : ℂ → ℂ} {z : ℂ} {z_neq_zero: z ≠ 0} (hz : HasZTransform f F z) (n : ℤ)   :
  HasZTransform (fun k => f (k - n)) (fun z => z^(-n) * F z) z := by
    unfold HasZTransform
    change HasSum (fun k ↦ f (k - n) * z ^ (-k)) (z ^ (-n) * F z)
    refine' (hasSum_int_shift n).mp _
    convert hz.mul_left (z^(-n)) using 2 with k
    calc
      f (k + n - n) * z ^ (-(k + n)) = f (k) * z ^ (-(k + n)) := by
        rw[add_sub_cancel_right]

      _ = f (k) * z^(-k) * z^(-n) := by rw[neg_add, zpow_add₀ z_neq_zero, mul_assoc]

      _ = z^(-n) * (f (k) * z^(-k)) := by rw[mul_comm]
```
 The following function provides a framework for forward-time shifting analysis in control law design. This proof is foundational result for analyzing sampled-data control systems.
```hs
theorem ZTransform_time_adv (f : DiscreteSignal) {F : ℂ → ℂ} {z : ℂ} {z_neq_zero: z ≠ 0} (hz : HasZTransform f F z) (n : ℤ) :
  HasZTransform (fun k => f (k + n)) (fun z => z^n * F z) z := by
    convert ZTransform_time_delay (z_neq_zero := z_neq_zero) hz (-n) using 2
    <;> ring_nf
```
 The following function allows transformation of scaled versions of signals, aiding in overall system modeling. System responses to exponential inputs are important tool for stability analysis.
```hs
theorem ZTransform_exp_mul (f : DiscreteSignal) (F : ℂ → ℂ) (ROC : Set ℂ) :
 (∀ (z : ROC), HasZTransform f F z) →
 (∀ z a : ℂ, z * a ∈ ROC → (HasZTransform (λ k ↦ a^ (-k) * f k) (fun z ↦ F (z * a)) z)) := by
  unfold HasZTransform -- HasSum (fun k ↦ f k * ↑z ^ (-k)) (F ↑z)) →  ∀ (z a : ℂ), z * a ∈ ROC → HasSum (fun k ↦ (fun k ↦ a ^ (-k) * f k) k * z ^ (-k)) (F (z * a))
  intro h z a hza --  z * a ∈ ROC ⊢ HasSum (fun k ↦ (fun k ↦ a ^ (-k) * f k) k * z ^ (-k)) (F (z * a))

  convert h ⟨z * a, hza⟩ using 2 with k
  change a ^ (-k) * f k * z ^ (-k) = f k * (z * a) ^ (-k)
  calc
    a ^ (-k) * f k * z ^ (-k) =  f k * z ^ (-k) * a ^ (-k) := by ring
    _ = f k * (z * a)^ (-k) :=  by rw[mul_zpow, mul_assoc]
```
This is a foundational result in control systems: if a signal is both stable and casual,then its gauranteed to have a stable Z-transform. This ensures that the  systems being analyzed in the Z-domain are physically realizable.
Furthermore, it provides a rigorous criterion for determining when a system is Z-transformable and supports the development of robust control laws by verifying whether system properties hold within the region of convergence. 
```hs
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
