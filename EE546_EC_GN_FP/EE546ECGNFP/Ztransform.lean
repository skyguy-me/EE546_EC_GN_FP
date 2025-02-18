import Mathlib.Tactic
import Mathlib.Data.Complex.Abs

open Complex

set_option maxHeartbeats 1000000

def j : ℂ := Complex.I
def Signal : Type := ℤ → ℂ

--instance Lattice ℂ :=
local notation "|"x"|" => Complex.abs x

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

notation "𝓩" => ZT
notation "𝓕_d" => DTFT

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
  have a : Summable fun k ↦ δ k * z^(-k) := by
    refine' summable_norm_iff.mp _
    simp
    use 1
    refine' Metric.tendsto_atTop.mpr _
    intro ε hε
    use singleton 0
    intro n hn
    change ‖(∑ b ∈ n, (fun x ↦ Complex.abs (if x = 0 then (z ^ x)⁻¹ else 0)) b) - 1‖ < ε
    have h_zero : 0 ∈ n := by exact Finset.zero_subset.mp hn

    have hs : ∑ b ∈ n, (fun x ↦ Complex.abs (if x = 0 then (z ^ x)⁻¹ else 0)) b = 1 := by
      rw[←Finset.add_sum_erase n (fun x ↦ Complex.abs (if x = 0 then (z ^ x)⁻¹ else 0)) h_zero]
      simp
      apply Finset.sum_eq_zero
      intro x hx
      have : x ≠ 0 := by exact Finset.ne_of_mem_erase hx
      simp
      intro _
      contradiction


  unfold ZT ZTransform
  rw[tsum_eq_tsum_of_ne_zero]



theorem zt_unit_step {z : ℂ} (h_roc : |z| > 1) : 𝓩 u z = 1 / (1 - z⁻¹) := by
  simp
  have : Summable fun k ↦ u k * (z ^ k)⁻¹ := by
    refine' summable_norm_iff.mp _
    simp





@[simp]
theorem ZTransform_linear (f₁ f₂ : Signal) (α β : ℂ) (z : ℂ) :
  𝓩 (λ k, α * f₁ k + β * f₂ k) z = α * 𝓩 f₁ z + β * 𝓩 f₂ z :=
by simp [ZTransform, tsum_add, tsum_mul_left]

@[simp]
theorem ZTransform_time_delay (f : Signal) (n : ℤ) (z : ℂ) : 𝓩 (λ k, f (k - n)) z = z^(-n) * 𝓩 f z := sorry
