import Mathlib.Tactic
import Mathlib.Data.Complex.Abs

open Complex

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

#eval j⁻¹

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
  simp
  apply summable_abs_iff.mp


theorem zt_unit_step {z : ℂ} (h_roc : |z| > 1) : 𝓩 u z = 1 / (1 - z⁻¹) := by
  simp
