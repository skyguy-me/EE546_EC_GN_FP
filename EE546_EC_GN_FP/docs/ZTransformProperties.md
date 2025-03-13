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
