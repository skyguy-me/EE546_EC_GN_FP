import Mathlib.Tactic
import Mathlib.Data.Complex.Abs

open Complex

set_option maxHeartbeats 1000000
set_option maxRecDepth 1000

def j : ℂ := Complex.I
def Signal : Type := ℤ → ℂ

def PosInt : Set ℤ := { k | k > 0 }
def NonNegInt : Set ℤ := { k | k ≥ 0 }
def NegInt : Set ℤ := { k | k < 0 }
def NonPosInt : Set ℤ := { k | k ≤ 0 }

def NonNegIntNatIso : NonNegInt ≃ ℕ where
  toFun := fun n ↦ Int.toNat n
  invFun := fun n ↦ Int.ofNat n
  left_inv := fun n ↦ by simp [int.to_nat_coe_nat]
  right_inv := fun k ↦ subtype.ext (int.to_nat_of_nonneg k.property)


lemma int_pos_neg_disjoint : Disjoint PosInt NegInt := by
    refine' Set.disjoint_iff_forall_ne.mpr _
    intro a _ b _

    have : a > 0 := by assumption
    have : b < 0 := by assumption
    linarith

lemma neg_pos_int_disjoint : Disjoint NegInt PosInt := by
  exact Disjoint.symm int_pos_neg_disjoint

lemma int_pos_nonpos_disjoint : Disjoint PosInt NonPosInt := by
    refine' Set.disjoint_iff_forall_ne.mpr _
    intro a _ b _

    have : a > 0 := by assumption
    have : b ≤ 0 := by assumption
    linarith

lemma int_nonpos_pos_disjoint : Disjoint NonPosInt PosInt := by
  exact Disjoint.symm int_pos_nonpos_disjoint

lemma int_neg_nonneg_disjoint : Disjoint NegInt NonNegInt := by
    refine' Set.disjoint_iff_forall_ne.mpr _
    intro a _ b _

    have : a < 0 := by assumption
    have : b ≥ 0 := by assumption
    linarith

lemma int_nonneg_neg_disjoint : Disjoint NonNegInt NegInt := by
  exact Disjoint.symm int_neg_nonneg_disjoint


@[simp]
noncomputable def ZTransform (x : Signal) (z : ℂ) :=
  ∑' k : ℤ, x (k) * z^(-k)

@[simp]
noncomputable def DiscreteTimeFourierTransform (x : Signal) (ω : ℝ) :=
  ∑' k : ℤ, x (k) * Complex.exp (-j * ω * k)

@[simp]
alias ZT := ZTransform

@[simp]
alias DTFT := DiscreteTimeFourierTransform

notation "𝓩" => ZTransform
notation "𝓕_d" => DiscreteTimeFourierTransform

variable (x : Signal)

@[simp]
def unit_impulse (k : ℤ) : ℂ :=
  if k = 0 then 1 else 0

@[simp]
def unit_step (k : ℤ) : ℂ :=
  if k ≥ 0 then 1 else 0

alias u := unit_step
alias H := unit_step

@[simp]
def rect (a b : ℤ) (k : ℤ) :=
  unit_step (k - a) - unit_step (k - b)

notation "δ" => unit_impulse

theorem ZTransformToDTFT : ∀ x : Signal, (fun ω : ℝ => 𝓩 x (Complex.exp (j * ω))) = 𝓕_d x := by
  intro x
  ext ω
  simp
  apply tsum_congr
  intro k
  calc
    x k * (Complex.exp (j * ↑ω) ^ k)⁻¹
      = x k * (Complex.exp (j * ↑ω * ↑k))⁻¹ := by rw [← Complex.exp_int_mul (j * ↑ω) k]; ring_nf
    _ = x k * Complex.exp (-(j * ↑ω * ↑k)) := by rw [←Complex.exp_neg (j * ↑ω * ↑k)]

theorem zt_unit_impulse {z : ℂ} (h_roc : z ≠ 0) : 𝓩 δ z = 1 := by
  rw[ZTransform]
  refine' HasSum.tsum_eq _
  refine' Metric.tendsto_atTop.mpr _
  intro ε _
  use singleton 0
  intro n hn
  change ‖∑ b ∈ n, (fun k ↦ δ k * z ^ (-k)) b - 1‖ < ε

  have h_zero : 0 ∈ n := by exact Finset.zero_subset.mp hn

  have hs : ∑ b ∈ n, (fun x ↦ Complex.abs (if x = 0 then (z ^ x)⁻¹ else 0)) b = 1 := by
    rw[←Finset.add_sum_erase n (fun x ↦ Complex.abs (if x = 0 then (z ^ x)⁻¹ else 0)) h_zero]
    simp
    apply Finset.sum_eq_zero
    intro x hx
    have hx_nonzero : x ≠ 0 := by exact Finset.ne_of_mem_erase hx
    simp only[hx_nonzero]
    exact (AbsoluteValue.eq_zero Complex.abs).mpr rfl

  simp[hs, h_zero]
  assumption

theorem inv_cpow_int (x : ℂ) (n : ℤ) : x⁻¹ ^ n = (x ^ n)⁻¹ := by
  simp


theorem zt_unit_step {z : ℂ} (h_roc : ‖z‖ > 1) : 𝓩 u z = 1 / (1 - z⁻¹) := by
  rw[ZTransform]

  let f := fun (k : ℤ) ↦ u k * z ^ (-k)

  have : ∑' (k : NonNegInt), f k = 1 / (1 - z⁻¹) := by
    have u_one : ∀ (k : NonNegInt), u k = 1 := by
      simp[u]
      intros
      assumption

    simp [f, u_one, one_mul]
    simp only [←inv_cpow_int]

    have hz : ‖z⁻¹‖ < 1 := by
      rw[norm_inv, inv_lt_comm₀, inv_one]
      <;> linarith

    rw [tsum_eq_tsum_of_equiv nat_to_nonnegint]
    apply tsum_geometric_of_norm_lt_one hz


  have : ∑' (k : NegInt), f k = 0  := by
    have f_zero : ∀ (k : NegInt), f k = 0 := by
      simp[f, u, unit_step]
      intro a ha _
      have : a < 0 := by assumption
      linarith

    simp[f_zero]

@[simp]
theorem ZTransform_linear (f₁ f₂ : Signal) (α β : ℂ) (z : ℂ) :
  𝓩 (λ k, α * f₁ k + β * f₂ k) z = α * 𝓩 f₁ z + β * 𝓩 f₂ z :=
by simp [ZTransform, tsum_add, tsum_mul_left]

@[simp]
theorem ZTransform_time_delay (f : Signal) (n : ℤ) (z : ℂ) : 𝓩 (λ k, f (k - n)) z = z^(-n) * 𝓩 f z := sorry
