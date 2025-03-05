import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Group.Indicator
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Basic
import Mathlib.Topology.Filter
import Mathlib.Tactic.Linarith

import EE546ECGNFP.Defs
import EE546ECGNFP.Signal

open Filter Topology Controls Controls.Discrete

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000


@[simp]
noncomputable def zt_kernel (x : DiscreteSignal) (z : ℂ) : ℤ → ℂ :=
  fun k ↦ x (k) * z^(-k : ℤ)

@[simp]
noncomputable def ZTransform (x : DiscreteSignal) (z : ℂ) :=
  ∑' k : ℤ, x (k) * z^(-k : ℤ)


def HasZTransform (x : DiscreteSignal) (z : ℂ) := HasSum (fun (k : ℤ) ↦ x k * z ^ (-k : ℤ))

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


@[simp]
def unit_impulse (k : ℤ) : ℂ :=
  if k = 0 then 1 else 0

theorem unit_impulse_equiv_indicator :
    ∀ k : ℤ, unit_impulse k = Set.indicator {0} 1 k := by
  intro k
  by_cases k_zero : k = 0
  <;> simp[k_zero]


notation "δ" => unit_impulse

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

/--
The rect function is one on [a, b)
-/
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



  -- unfold HasZTransform


  -- calc a^(-k) * f k * z^(-k)
  --    = f k * (a^(-k) * z^(-k))  : by rw [mul_comm (a^(-k)) (f k)]
  --  _ = f k * (a * z)^(-k)     : by rw [mul_assoc, ← mul_zpow, mul_comm a z]


  -- rfl

  -- simp only [ZTransform]

  -- have h : ∀ k, a^(-k) * f k * z^(-k) = f k * (a * z)^(-k) := by
  --   intro k -- a ^ (-k) * f k * z ^ (-k) = f k * (a * z) ^ (-k)
  --   calc a^(-k) * f k * z^(-k)
  --     _ = f k * a^(-k) * z^(-k) := by ring
  --     _ = f k * (a * z)^(-k) := by sorry


  -- rw [tsum_congr h]



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
