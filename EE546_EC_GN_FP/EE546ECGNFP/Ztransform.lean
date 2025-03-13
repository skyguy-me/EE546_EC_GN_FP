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
<center><h1>EE 546 : Automated Reasoning</h1></center>
<center><h2>Final Project Z-transforms</h2></center>

<center>
Department of Electrical and Computer Engineering<br />
Unviersity of Washington<br />
Ember Chow and Gokul Nathan<br />
Winter 2025<br />
</center>
<br />
-/

/-
<center><h2>Project Abstract and Overview</h2></center>

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
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed

import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Complex.Basic

import Mathlib.Algebra.Group.Indicator

import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Basic
import Mathlib.Topology.Filter

import Mathlib.Tactic.Linarith


/-
<center><h2>Introductions to Z-transforms</h2></center>

This project focuses on implementing and exploring the Z-transform, a crucial mathematical tool for analyzing discrete-time signals and systems in the field of signal processing. The Z-transform transforms discrete signals from the time domain into the complex frequency domain, enabling more efficient analysis and manipulation of signals. The Z-transform is defined as:

<center>
$` \mathcal{Z}\{x[n]\} = X(z) = \sum_{k=-\infty}^{\infty} x[k] z^{-k} `$
</center>

Where:
- $` x[k] `$ is the discrete-time signal,
- $` z `$ a complex variable,
- $` X(z) `$ is the Z-transform of $` x[k] `$.

This transformation is widely used in systems analysis, particularly in the design of digital filters and stability analysis of discrete-time systems. In this project, we've defined several types and functions in Lean to formalize the concept of the Z-transform for discrete-time signals.

The **Z-transform** of a discrete signal $`x `$ is defined as `noncomputable def ZTransform (x : DiscreteSignal) (z : ℂ) := ∑' k : ℤ, x(k) * z^(-k : ℤ)`, which sums over all integer values of $`k `$, multiplying each value of the signal $`x(k) `$ by the complex number $`z `$ raised to the power of $`-k `$.

We also define a condition for the existence of the Z-transform for a given signal $`f `$ with `def HasZTransform (f : DiscreteSignal) (F : ℂ → ℂ) (z : ℂ) := HasSum (fun (k : ℤ) ↦ f k * z ^ (-k : ℤ)) (F z)`, asserting that the signal $` f `$ has a Z-transform $` F(z) `$ if the sum converges for all $` k \in \mathbb{Z} `$.

A signal is considered **Z-transformable** if it satisfies the condition that the summation is **summable**: `def ZTransformable (f : DiscreteSignal) (z : ℂ) := Summable fun k ↦ f k * z ^ (-k)`, checking whether the sum of the signal values multiplied by $` z^{-k} `$ is finite for some complex number $`z `$.

The **unilateral Z-transform** is a variant of the Z-transform where the summation only runs over non-negative integers (i.e., $`k \geq 0 `$) and is defined as `noncomputable def ZTransformUnilateral (x : DiscreteSignal) (z : ℂ) := ∑' k : ℕ, x(k) * z^(-k : ℤ)`, useful for one-sided discrete-time signals, typically encountered in causal systems. An alternate form of the unilateral Z-transform is defined with a non-negative integer type as `noncomputable def ZTransformUnilateral' (x : DiscreteSignal) (z : ℂ) := ∑' k : NonNegInt, x(k) * z ^ (-↑k : ℤ)`.

The **Discrete-Time Fourier Transform (DTFT)** is closely related to the Z-transform, used to analyze signals in the frequency domain, and is given by `noncomputable def DiscreteTimeFourierTransform (x : DiscreteSignal) (ω : ℝ) := ∑' k : ℤ, x(k) * Complex.exp (-j * ω * k)`, which sums over all integers $`k `$, with each value of the signal $`x(k) `$ multiplied by a complex exponential $`e^{-j \omega k} `$.

For convenience, we define some aliases for the Z-transform and DTFT with `alias ZT := ZTransform` and `alias DTFT := DiscreteTimeFourierTransform`, allowing us to use shorthand notation. Finally, we define custom notation for the Z-transform and DTFT with `notation "𝓩" => ZTransform`, `notation "𝓩_u" => ZTransformUnilateral`, and `notation "𝓕_d" => DiscreteTimeFourierTransform`, making the expressions more concise.

This project aims to provide a formal and computational framework for the Z-transform and related transforms like the DTFT. By implementing these definitions in Lean, we can rigorously analyze discrete-time signals, explore their properties, and apply these transforms in various signal processing tasks such as system analysis, filter design, and stability analysis.
-/

/-
<h2> Approach: solving challenges while maintaing robust future development directions </h2>

Our approach to implementing the Z-transform in Lean 4 follows a top-down methodology, beginning with an in-depth examination of the foundational content available in Mathlib. During this process, we identified a gap in how certain critical aspects of signal processing—specifically the Z-transform—were represented and handled. To address this, we built a structured framework from the ground up, defining core principles and mathematical structures to support the Z-transform and its applications.

The first step in our implementation was defining the Z-transform itself, along with its essential properties. This required an understanding of its mathematical and computational aspects, such as convergence, summability, and the interplay between time and frequency domains. We then defined a representation for discrete sampled signals, as they form the fundamental unit of analysis in signal processing. This process led to a more foundational exploration of key mathematical structures, including sets, monoids, complex numbers, and natural numbers. While Mathlib provided a strong foundation, many of these structures were not readily available in the form needed for signal processing tasks, prompting us to develop them independently while ensuring compatibility with existing Mathlib definitions.

## Mathematical Foundations and Implementation
The implementation of the Z-transform is centered around defining it as an infinite sum over integer indices, mapping a discrete-time function into the complex plane. A key aspect of this formalization is the integration of summability results from fundamental definitions, ensuring that infinite series converge appropriately within the Lean framework. The following core properties, implemented in `ZTransformProperties.lean`, `Signal.lean`, and `Defs.lean`, were rigorously proven:

- **Linearity:** The Z-transform maintains linearity, meaning that the transform of a linear combination of two sequences is equivalent to the corresponding linear combination of their individual transforms. This was achieved by expanding the summation and using the linearity of infinite series to separate terms, confirming that the transformation operation is distributive over addition and scalar multiplication. Lean’s formalization of infinite summation allows for precise separation and recombination of terms within the proof.

- **Scaling Property:** This theorem proves that multiplying a discrete-time function by an exponential sequence translates to a shift in the complex Z-domain. The proof rewrites the Z-transform summation by factoring out the scaling term and demonstrating that it corresponds to a simple substitution of variables in the transformed function. This property is crucial in frequency-domain analysis, where shifts in time correspond to frequency scaling. The proof utilizes bijective transformations of summation indices, ensuring that changes in the function’s domain are well-defined and rigorously justified.

- **Time Shifting:** The time-shifting theorem proves that delaying a discrete-time function in the time domain results in multiplication by a power of \(z\) in the Z-domain. This is shown by algebraically manipulating the indices of the summation and using the properties of exponentiation. The proof methodically demonstrates how the shift in index position modifies the sum while maintaining the function’s structure. We leverage established summation-shifting theorems to ensure that our proof remains consistent across different types of discrete-time signals.

Each proof follows a structured approach: first, the Z-transform is expanded in its summation form, then algebraic manipulation is applied to express the transformed function in an equivalent form, and finally, Lean’s theorem-proving capabilities are used to rigorously validate each step. The constructive nature of Lean ensures that each transformation is fully verified within a formal logical framework. Additionally, the implementation benefits from existing summability theorems and bijective mappings, ensuring correctness and reducing redundancy in proof structures.
-/

/- <h3>Our custom Libraries</h>

Having outlined our top-down approach and the foundational work behind implementing the Z-transform in Lean 4, we now turn to the three core definition files that follow this method. These files serve as the backbone of the project, each contributing to the larger goal of creating a comprehensive, rigorously defined framework for signal processing and Z-transform applications in Lean 4.

### `Defs.lean`

`Defs.lean` serves as a crucial definitions file, providing the basic mathematical structures and operations that are essential for encoding discrete-time signals, their properties, and the Z-transform in Lean. This file acts as the foundational layer upon which all higher-level modules are built. By collecting these essential primitives into a single, well-organized file, `Defs.lean` ensures that the project relies on a consistent and rigorously defined base. These structures, such as sets, monoids, complex numbers, and natural numbers, are key building blocks that allow for the formalization of more complex signal processing concepts.

### `Signals.lean`

`Signals.lean` serves as the fundamental file for encoding the properties of the signals being studied and their behavior in the context of the Z-transform. This file extends the foundational structures defined in `Defs.lean` to provide specific representations and operations related to discrete-time signals. It is in this file that the core mathematical structures for signals are formalized, ensuring that all signal properties and operations are consistent with the project’s overall framework. `Signals.lean` ensures that the signals we work with can be manipulated, transformed, and analyzed in a mathematically sound manner, enabling us to apply the Z-transform and other related operations effectively.

### `ZtransformProperties.lean`

`ZtransformProperties.lean` is the key file for defining the core properties of the Z-transform itself. Building upon the signal definitions in `Signals.lean`, this file encodes the essential properties and operations required to define and manipulate the Z-transform. It includes definitions of convergence, summability, and the mapping between time-domain signals and their Z-domain representations. This file is fundamental in establishing the theoretical framework for the Z-transform, ensuring that all subsequent work involving the Z-transform is rooted in a rigorous and well-defined foundation. By clearly separating the properties of the Z-transform from other signal processing operations, `ZtransformProperties.lean` keeps the project modular and well-organized.

Given these helper lemmas and theorems, each proof bellow follows a structured approach: first, the Z-transform is expanded in its summation form, then algebraic manipulation is applied to express the transformed function in an equivalent form, and finally, Lean’s theorem-proving capabilities are used to rigorously validate each sub-goal. The constructive nature of Lean ensures that each transformation is fully verified within a formal logical framework. Additionally, the implementation benefits from existing summability theorems, bijective mappings, and set-based transformations defined in `Defs.lean`, ensuring correctness and reducing redundancy in proof structures.
 -/

import EE546ECGNFP.Defs -- Useful mathematical definitions
import EE546ECGNFP.Signal -- USeful examining the signal properties
import EE546ECGNFP.ZTransformProperties -- Useful properties for implementing engineering Z-transforms

open Filter Topology Controls Controls.Discrete

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000

variable (x : DiscreteSignal)

/- <h3>Development of our custom Lean4 tactics</h>
  @EMMY PUT YOUR TACTICS WRITEUP HERE.
-/



/- **Fundamental Z-Transforms Properties**

In this sub-section, we provide a detailed explanation of several key theorems related to the unit step function `unit_step` (aliased as `u`). These theorems establish fundamental properties such as causality and summability, and they show how multiplication by the unit step function affects discrete-time signals. Specifically, we establish that multiplying a signal by $`u(k) `$ enforces causality and preserves summability. We formalize these properties in Lean so that the **causal nature of our signals has specific implications in the Z-transform**. By encoding these results, we ensure that Lean can automatically reason about causality in **Z-transform proofs**, particularly when proving properties like the **region of convergence (ROC)** and **linearity of summation**.

These causal properties allow us to **exploit simplifications** in proofs, ensuring that when working with the Z-transform of causal signals, we can restrict summation to the non-negative domain, rather than dealing with the entire integer set $ \mathbb{Z} $.-/

/-
# Properties of the Z-Transform
| No. | Name                          | Formula                                                                                                                                  | Implementation |
|----:|:------------------------------|:-----------------------------------------------------------------------------------------------------------------------------------------|----------------|
| 1   | **Linearity**                 | $` \mathcal{Z}\{a\,f_1(k) + b\,f_2(k)\} \;=\; a\,F_1(z)\;+\;b\,F_2(z)`$                                                      |:white_check_mark:|
| 2   | **Time Delay**                | $` \mathcal{Z}\{f(k - n)\} \;=\; z^{-n}\,F(z)`$                                                                             | :white_check_mark:|
| 3   | **Time Advance**              | $` \mathcal{Z}\{f(k + 1)\} \;=\; z\,F(z)\;-\;z\,f(0)$<br>$ \mathcal{Z}\{f(k + n)\} \;=\; z^n\,F(z)\;-\;z^{n-1}f(0)\;-\;\dots\;-\;z\,f(n-1)`$ | :white_check_mark:|
| 4   | **Discrete-Time Convolution** | $` \mathcal{Z}\{f_1(k)\ast f_2(k)\} \;=\; F_1(z)\,F_2(z)`$                                                                   | :black_square_button:|
| 5   | **Multiplication by Exponential** | $` \mathcal{Z}\{a^k\,f(k)\} \;=\; F(a\,z)`$                                                                               | :white_check_mark:|
| 6   | **Complex Differentiation**   | $` \mathcal{Z}\{k^m\,f(k)\} \;=\; \Bigl(-\,z\,\frac{d}{dz}\Bigr)^{m}F(z)`$                                                   |:black_square_button:|
| 7   | **Final Value Theorem**       | $` f(\infty)\;=\;\lim_{k\to\infty}f(k)\;=\;\lim_{z\to 1}\bigl(1 - z^{-1}\bigr)\,F(z)`$                                       |:black_square_button:|
| 8   | **Initial Value Theorem**     | $` f(0)\;=\;\lim_{k\to 0}f(k)\;=\;\lim_{z\to \infty}F(z)`$                                                                   |:black_square_button:|
-/

/-
### **Solving the Linearity Property**
The proof of linearity ensures that the Z-transform of a linear combination of two sequences is equivalent to the corresponding linear combination of their individual transforms. This is achieved by expanding the Z-transform definition into an infinite summation and applying the linearity of summation operators. Since the summation of two functions distributes over addition, we formally separate the summation into two distinct sums, allowing each to be rewritten in terms of their respective Z-transforms. Lean’s theorem-proving framework rigorously verifies this transformation by enforcing correct term expansion and sum decomposition, ensuring that the final expression adheres to the expected mathematical formulation.

-/
@[simp]
theorem ZTransform_linear (f₁ f₂ : DiscreteSignal) (F₁ F₂ : ℂ → ℂ) (z : ℂ) (a b : ℂ) (hz₁ : HasZTransform f₁ F₁ z)  (hz₂ : HasZTransform f₂ F₂ z) :
  HasZTransform (fun k => a * f₁ k + b * f₂ k) (fun z => a * F₁ z + b * F₂ z) z := by
  convert zt_add z (fun k => a * f₁ k) (fun k => b * f₂ k) ?_ ?_ ?add_left ?add_right
  <;> apply zt_mul_left
  <;> assumption


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


@[simp]
theorem ZTransform_time_adv (f : DiscreteSignal) {F : ℂ → ℂ} {z : ℂ} {z_neq_zero: z ≠ 0} (hz : HasZTransform f F z) (n : ℤ) :
  HasZTransform (fun k => f (k + n)) (fun z => z^n * F z) z := by
    convert ZTransform_time_delay (z_neq_zero := z_neq_zero) hz (-n) using 2
    <;> ring_nf



@[simp]
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

/-This is a foundational result in control systems: if a signal is both stable and casual,then its gauranteed to have a stable Z-transform. This ensures that the  systems being analyzed in the Z-domain are physically realizable.
Furthermore, it provides a rigorous criterion for determining when a system is Z-transformable and supports the development of robust control laws by verifying whether system properties hold within the region of convergence. -/


@[simp]
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

-- future work
theorem zt_FinalValueTheorem
  (x : DiscreteSignal) (xf : ℂ) :
  IsCausal x → HasFinalValue x xf →
  Tendsto (fun z ↦ (z - 1) * (𝓩 x z)) (𝓝 1) (𝓝 xf) := by
    intro hx_causal
    intro hxf
    simp only[ZTransform]
    sorry


-- future work
-- theorem zt_InitialValueTheorem
--   (x : DiscreteSignal) (xf : ℂ) :
--   IsCausal x → HasFinalValue x xf →
--   Tendsto (fun z ↦ (z - 1) * (𝓩 x z)) (𝓝 1) (𝓝 xf) := by
--     intro hx_causal
--     intro hxf
--     simp only[ZTransform]
--     sorry


/-
## Limitations and Future Work
While this project successfully formalizes key properties of the Z-transform, several limitations remain, providing opportunities for future extensions. First, developing a formal proof of the inverse Z-transform remains an open challenge. While the direct Z-transform is well-structured and provable within Lean’s framework, the inverse transform involves contour integration techniques and residue calculus, which are not yet fully formalized in Lean’s mathematical libraries.

Another limitation arises in the stability analysis of discrete-time systems. Although the Z-transform allows for pole-zero analysis in the complex domain, a fully rigorous treatment of stability requires extending Lean’s complex function analysis toolkit to support advanced properties and convergence criteria for rational functions. The lack of a robust framework for reasoning about system stability means that direct applications to control systems remain limited in this implementation.

Additionally, extending this work to multidimensional transforms would enable applications in image processing and spatiotemporal signal analysis. However, the extension to two-dimensional and higher-dimensional Z-transforms introduces additional mathematical complexities, particularly in defining appropriate convergence conditions for multidimensional power series. The current implementation assumes summability in a one-dimensional setting, and generalizing this to higher dimensions would require further theoretical advancements.

A key design choice in this project was the adoption of the **bilateral Z-transform**, which considers summation over all integer values rather than restricting to causal sequences (as in the unilateral Z-transform). The bilateral Z-transform is particularly advantageous for frequency-domain analysis of bidirectional signals, where non-causal behavior plays a role. However, this choice introduces additional complexity in handling convergence issues. Since the bilateral transform does not inherently assume a region of convergence that starts at the origin, the burden of proving absolute summability is greater, especially for sequences with nonzero values extending indefinitely in both positive and negative time indices. Furthermore, practical digital systems often deal with causal signals, meaning that extending this formalization to include the unilateral Z-transform would make it more relevant to many engineering applications. Future work should explore the integration of both bilateral and unilateral transforms to provide a comprehensive formal framework for signal analysis.

Despite these limitations, each of these areas presents a significant opportunity for future research. The development of formal inverse Z-transform proofs, robust stability analysis, and multidimensional Z-transform extensions would greatly enhance the robustness and applicability of this framework, making it more suitable for real-world engineering applications.

-/
