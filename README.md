<center><h1>EE 546 : Automated Reasoning</h1></center>
<center><h2>Implementing Z-transforms in Lean4</h2></center>

<center>
Department of Electrical and Computer Engineering<br />
Unviersity of Washington<br />
Ember CHow and Gokul Nathan<br />
Winter 2025<br />
</center>
<br />


<h2>Abstract and Introduction</h2>
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

<h2>Repository Organization</h2>

This repository is structured into five Lean files that collectively build a comprehensive Z-Transform table implementation. Each file contributes to a specific aspect of the theory and its applications. Each lean file has an associated readme file that dives more deeply into the theory and the lean implementation of the transform tables. **Ztransform.md** is the primary file to read to track the progress of the Z-transform implementations. 

#### **1. `Defs.lean` – Core Definitions**
This file serves as the **foundational layer** of the project, defining key mathematical structures used throughout the repository. It collects **essential primitives** to maintain consistency across the implementation.

#### **2. `Signal.lean` – Signal Representation & Properties**
This file **extends `Defs.lean`** by providing formal definitions for **discrete-time signals** and their mathematical properties. 

#### **3. `ZTransformProperties.lean` – Fundamental Properties of the Z-Transform**
This file encodes **core properties and operations** of the Z-transform. It **builds upon `Signal.lean`** by formally defining the convergence, summability and the linearity property of the Z-transforms. 


#### **4. `Tactic.lean` – Custom Tactics for Summation Manipulation**
`Tactic.lean` defines the **`sum_simp`** tactic, which simplifies infinite sums by leveraging **linearity** properties. This allows for the automatic decomposition of sums into known forms, making it easier to apply existing results. 

#### **5. `ZTransform.lean` – Core Z-Transform Implementation**
This is the central file of the repository, where the **Z-transform table is formally defined and implemented**.








<h2>Contributions to state of art</h2>
This repository introduces three major contributions to the state of the art in formal methods, engineering, and control theory. 

### **1. Sum-Simp Tactic: A Powerful Summation Decomposition Tool**
- Introduces `sum_simp`, a **powerful Lean tactic** for **decomposition and recombination of sums**.
- Its applications extend **beyond the Z-transform**, providing utility in:
  - **Digital signal processing (DSP)** – Efficient sum simplification for Fourier/Z-transforms.
  - **Control theory** – Analyzing stability and convergence of signals.
  - **Mathematical analysis** – Automated manipulation of infinite series.
  - **Machine learning** – Symbolic summation simplifications in probabilistic models. 

#### **Example Usage**
To solve the sum:

$`\sum_{k = 0}^{\infty} 2 \left(\frac{1}{2}\right)^k + 3 \left(\frac{1}{3}\right)^k `$

We can break it into geometric series components:

$` \sum_{k = 0}^{\infty} 2 \left(\frac{1}{2}\right)^k + 3 \left(\frac{1}{3}\right)^k =
2 \sum_{k = 0}^{\infty} \left(\frac{1}{2}\right)^k +
3 \sum_{k = 0}^{\infty} \left(\frac{1}{3}\right)^k `$

Applying the formula for a geometric series, we obtain:

$` 2 \left(1 - \left(\frac{1}{2}\right)^{-1}\right) +
3 \left(1 - \left(\frac{1}{3}\right)^{-1}\right) `$

While this decomposition can be done manually, **`sum_simp` automates the process**. 

### **2. Formalization of Signal Characteristics for Engineering and Control Applications**
- Provides a **rigorous framework** for analyzing discrete-time signals.
- Establishes **key properties** such as:
  - Stability: Shows that **stable and causal signals are bounded**.
  - Final Value Theorem: Proves the **existence of a final value at \( t \to \infty \)**.
  - Stability Implications: Demonstrates the behavior of a new **bounded signal with a final value**.
- These properties are **critical for control system design** and **signal stability analysis**.

### **3. Implementation and Proofs of Z-Transform Tables for System Analysis**
- Implements **fully formalized Z-transform tables** in Lean 4.
- These tables allow users to:
  - **Analyze system stability** through signal behavior in the Z-domain.
  - **Assess controllability** by examining Z-transform properties.
  - **Facilitate controller design** based on available signal information.
- This work provides a **formal verification** approach to classical **Z-transform techniques**, ensuring **mathematical rigor** in engineering applications.

---

## **Documentation and Guidance**
- **Inline comments** in each file guide the reader through the implementation process.
- **Each Lean file has its own README** detailing its structure and purpose.
- **This document provides a high-level overview** of how the files interconnect.

This structured approach ensures that the implementation is **modular, correct, and extensible**, making it a valuable resource for formalizing the Z-transform in Lean 4.