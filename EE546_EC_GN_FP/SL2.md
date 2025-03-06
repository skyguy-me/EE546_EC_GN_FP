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


theorem zt_unit_impulse {z : ℂ} (k₀ : ℤ) : HasZTransform (fun k ↦ δ (k - k₀)) z (z ^ (-k₀)) := by
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

theorem ZTUnilateral_hasSum_equiv {z : ℂ} {a : ℂ} (x : DiscreteSignal) :
  HasSum (fun n : ℕ ↦ x n * z ^ (-n : ℤ)) a ↔
  HasSum (fun k : NonNegInt ↦ x k * z ^ (-k : ℤ)) a := by
    exact Equiv.hasSum_iff nonNegInt_nat_equiv.symm (a := a) (
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

theorem zt_unit_step {z : ℂ} (h_roc : ‖z‖ > 1) : HasZTransform u z (1 / (1 - z⁻¹)) := by
  rw[HasZTransform]

  have : ∀ k, u k * z ^ (-k) = u k * 1 * z ^ (-k) := by simp
  simp only [this]

  refine' zt_sum_unit_step.mpr _
  simp
  simp only[←inv_pow]

  refine' hasSum_geometric_of_norm_lt_one _
  rw[norm_inv, inv_lt_comm₀] <;> linarith

theorem zt_FinalValueTheorem
  (x : DiscreteSignal) (xf : ℂ) :
  IsCausal x → HasFinalValue x xf →
  Tendsto (fun z ↦ (z - 1) * (𝓩 x z)) (𝓝 1) (𝓝 xf) := by
    intro hx_causal
    intro hxf
    simp only[ZTransform]
    sorry

-- @[simp]
-- theorem ZTransform_linear {z : ℂ} (f₁ f₂ : DiscreteSignal) (hf₁ : @ZTransformable z f₁) (hf₂ : @ZTransformable z f₂) (a b : ℂ) : 𝓩 (fun k => a * f₁ k + b * f₂ k) z = a * 𝓩 f₁ z + b * 𝓩 f₂ z := by
--   simp only[ZTransform]
--   calc
--   ∑' (k : ℤ), (a * f₁ k + b * f₂ k) * z ^ (-k) = ∑' (k : ℤ), (a * f₁ k * z ^ (-k) + b * f₂ k * z ^ (-k)) :=
--     by group

--   _ = ∑' (k : ℤ), a * f₁ k * z ^ (-k) + ∑' (k : ℤ), b * f₂ k * z ^ (-k) := by
--     rw[tsum_add]

--   _ = ∑' (k : ℤ), a * (f₁ k * z ^ (-k)) + ∑' (k : ℤ), b * (f₂ k * z ^ (-k)) := by group
--   _ = a * ∑' (k : ℤ), f₁ k * z ^ (-k) + b * ∑' (k : ℤ), f₂ k * z ^ (-k) := by rw[tsum_mul_left, tsum_mul_left]

-- @[simp]
-- theorem ZTransform_time_delay (f : DiscreteSignal) (n : ℤ) (z : ℂ) :  𝓩 (fun k => f (k - n)) z = z ^ (-n) * 𝓩 f z := by
  -- simp only[ZTransform]

  -- let g := fun k : ℤ => f (k - n) * z ^ (-k)
  -- let h := fun m : ℤ => f m * z ^ (-(m + n))

  -- have h_i : (fun k => f (k - n) * z ^ (-k)) = (fun m => f m * z ^ (-(m + n))) := by
  --   ext m
  --   -- ring_nf



--   sorry

-- @[simp]
-- theorem ZTransform_time_advance_one (f : DiscreteSignal) (z : ℂ) : 𝓩 (fun k => f (k + 1)) z = z * 𝓩 f z - z * f 0 := by
--   sorry

-- @[simp]
-- theorem ZTransform_time_advance_n (f : DiscreteSignal) (n : ℕ) (z : ℂ) : 𝓩 (fun k => f (k + n)) z = z^n * 𝓩 f z - ∑ i in Finset.range n, z^(n - i) * f i := by
--   sorry

-- class ZTransformable (f : DiscreteSignal) (z : ℂ) : Prop where
--   summable : Summable (λ k : ℤ, f k * z^(-k))

-- instance (f : DiscreteSignal) (z : ℂ) [ZTransformable f z] : HasZTransform f z (ZTransform f z) :=
--   by
--     rw [HasZTransform, ZTransform]
--     exact (ZTransformable.summable f z).hasSum

-- theorem zt_unit_step {z : ℂ} (h_roc : ‖z‖ > 1) : @HasZTransform z u (1 / (1 - z⁻¹)) := by sorry



theorem ZTransform_exp_mul (f : DiscreteSignal) (F : ℂ → ℂ) (ROC : Set ℂ) :
 (∀ (z : ROC), (HasZTransform f z (F z))) →
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

theorem ℤt_of_stable_and_causal (x : DiscreteSignal) (z : ℂ) (h_roc : ‖z‖ > 1) : IsStable x → IsCausal x → ZTransformable x z := by
  intro hs hc
  have hb : IsBoundedSignal x := by apply isStableAndCausal_implies_isBounded x hs hc
  rw [ZTransformable]
  obtain ⟨m, hm⟩ := hb
  refine Summable.of_norm_bounded ?_ ?_ ?_  --⊢ Summable fun a ↦ ‖x a * z ^ (-a)‖
  --case 1
  . exact fun k ↦ ‖m‖ * ‖z^(-k)‖
  . refine Summable.mul_left (f := fun k ↦ ‖z^(-k)‖) ‖m‖ ?_





  .




sorry


-- @[simp]
-- theorem ZTransform_convolution (f g : DiscreteSignal) (z : ℂ) : 𝓩 (discrete_convolution f g) z = 𝓩 f z * 𝓩 g z := by
--   rw [ZTransform] -- ∑' (k : ℤ), discrete_convolution f g k * z ^ (-k) = 𝓩 f z * 𝓩 g z
--   simp only [discrete_convolution] -- ∑' (k : ℤ), (∑' (m : ℤ), f m * g (k - m)) * z ^ (-k) = 𝓩 f z * 𝓩 g z


--   let h := fun k => ∑' m : ℤ, f m * g (k - m)
--   let t := fun k => h k * z ^ (-k)
--   sorry


-- theorem ZTransform_IVT: := by
--   sorry

-- theorem ZTransform_FVT := by
--   sorry
```
