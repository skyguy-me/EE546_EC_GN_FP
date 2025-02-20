import Mathlib.Tactic
import Mathlib.Data.Complex.Abs

open Complex

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000

def j : ℂ := Complex.I
def Signal : Type := ℤ → ℂ

def PosInt : Set ℤ := { k | k > 0 }
def NonNegInt : Set ℤ := { k | k ≥ 0 }
def NegInt : Set ℤ := { k | k < 0 }
def NonPosInt : Set ℤ := { k | k ≤ 0 }

@[simp]
theorem nonpos_pos_union : NonPosInt ∪ PosInt = Set.univ := by
  ext x
  apply Iff.intro
  . intro hmp
    trivial

  . intro hmpr
    by_cases hx : x > 0
    case pos => exact Set.mem_union_right NonPosInt hx
    case neg =>
      have : x ≤ 0 := by exact Int.not_lt.mp hx
      exact Set.mem_union_left PosInt this

@[simp]
theorem pos_nonpos_union : PosInt ∪ NonPosInt = Set.univ := by
  rw[←Set.union_comm]
  exact nonpos_pos_union

@[simp]
theorem nonneg_neg_union : NonNegInt ∪ NegInt = Set.univ := by
  ext x
  apply Iff.intro
  . intro hmp
    trivial

  . intro hmpr
    by_cases hx : x < 0
    case pos => exact Set.mem_union_right NonNegInt hx
    case neg =>
      have : x ≥ 0 := by exact Int.not_lt.mp hx
      exact Set.mem_union_left NegInt this

@[simp]
theorem neg_nonneg_union : NegInt ∪ NonNegInt = Set.univ := by
  rw[←Set.union_comm]
  exact nonneg_neg_union

@[simp]
def nonnegint_nat_equiv : NonNegInt ≃ ℕ where
  toFun := fun i ↦ Int.toNat i
  invFun := by
    intro n
    refine' ⟨Int.ofNat n, _⟩
    exact Int.zero_le_ofNat n

  left_inv := by
    intro n
    simp[]
    refine Eq.symm (Subtype.coe_eq_of_eq_mk ?_)
    obtain ⟨ i,hn⟩ := n
    simp[]
    assumption

  right_inv := by
    intro n
    rfl

@[simp]
lemma int_pos_neg_disjoint : Disjoint PosInt NegInt := by
    refine' Set.disjoint_iff_forall_ne.mpr _
    intro a _ b _

    have : a > 0 := by assumption
    have : b < 0 := by assumption
    linarith

@[simp]
lemma neg_pos_int_disjoint : Disjoint NegInt PosInt := by
  exact Disjoint.symm int_pos_neg_disjoint

@[simp]
lemma int_pos_nonpos_disjoint : Disjoint PosInt NonPosInt := by
    refine' Set.disjoint_iff_forall_ne.mpr _
    intro a _ b _

    have : a > 0 := by assumption
    have : b ≤ 0 := by assumption
    linarith

@[simp]
lemma int_nonpos_pos_disjoint : Disjoint NonPosInt PosInt := by
  exact Disjoint.symm int_pos_nonpos_disjoint

@[simp]
lemma int_neg_nonneg_disjoint : Disjoint NegInt NonNegInt := by
    refine' Set.disjoint_iff_forall_ne.mpr _
    intro a _ b _

    have : a < 0 := by assumption
    have : b ≥ 0 := by assumption
    linarith

@[simp]
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


theorem tsum_equiv : ∀ {α β : Type} [Countable α] [Countable β] {f : α → ℂ} (e : α ≃ β), (∑' a : α, f a) = ∑' b : β, f (e.symm b) := by
  exact fun α β [Countable α] [Countable β] {f} e ↦ Eq.symm (Equiv.tsum_eq e.symm f)

theorem hasSum_equiv {α β γ : Type*}
  [AddCommMonoid α] [TopologicalSpace α]
  {f : β → α} {a : α} (e : γ ≃ β) :
   HasSum (f ∘ e) a ↔ HasSum f a := by
    refine' Function.Injective.hasSum_iff e.injective _
    intro _ hx
    simp at hx

theorem zt_unit_step {z : ℂ} (h_roc : ‖z‖ > 1) : 𝓩 u z = 1 / (1 - z⁻¹) := by
  rw[ZTransform]

  let f := fun (k : ℤ) ↦ u k * z ^ (-k)

  have s_neg : HasSum (fun k : NegInt ↦ f k) 0 := by
    have f_zero : ∀ (k : NegInt), f k = 0 := by
      simp[f, u, unit_step]
      intro a ha _
      have : a < 0 := by assumption
      linarith

    simp[f_zero]
    exact hasSum_zero

  have s_nonneg : HasSum (fun (k : NonNegInt) ↦ f k) (1 / (1 - z⁻¹)) := by
    refine' (hasSum_equiv
      (f := fun k : NonNegInt ↦ f k)
      (a := (1 / (1 - z⁻¹))) nonnegint_nat_equiv.symm).mp _

    have u_one : ∀ (k : NonNegInt), u k = 1 := by
      simp[u]
      intros
      assumption

    have hz : ‖z⁻¹‖ < 1 := by
      rw[norm_inv, inv_lt_comm₀, inv_one]
      <;> linarith

    simp[f, u_one]
    simp only[←inv_cpow_int]

    change HasSum (fun n : ℕ ↦ z⁻¹ ^ n) (1 - z⁻¹)⁻¹
    exact hasSum_geometric_of_norm_lt_one hz

  rw[←tsum_univ, ←neg_nonneg_union]

  have : (tsum fun (k : ↑(NegInt ∪ NonNegInt)) ↦ f ↑k) =
    ∑' (k : ↑NegInt), f ↑k + ∑' (k : ↑NonNegInt), f ↑k :=
    tsum_union_disjoint int_neg_nonneg_disjoint s_neg.summable s_nonneg.summable

  rw[this, s_neg.tsum_eq, s_nonneg.tsum_eq, zero_add]

-- These are the equations from the refrence text. We will be attmepting to prove these as a proof of concept excercise.




@[simp]
theorem ZTransform_linear (f₁ f₂ : Signal) (α β : ℂ) (z : ℂ) : 𝓩 (fun k => α * f₁ k + β * f₂ k) z = α * 𝓩 f₁ z + β * 𝓩 f₂ z := by sorry

@[simp]
theorem ZTransform_time_delay (f : Signal) (n : ℤ) (z : ℂ) :  𝓩 (fun k => f (k - n)) z = z ^ (-n) * 𝓩 f z := by
  rw [ZTransform]
  rw[tsum_congr]
  simp -- (z ^ n)⁻¹ * ∑' (k : ℤ), f k * (z ^ k)⁻¹


  sorry

@[simp]
theorem ZTransform_time_advance_one (f : Signal) (z : ℂ) : 𝓩 (fun k => f (k + 1)) z = z * 𝓩 f z - z * f 0 := sorry

@[simp]
theorem ZTransform_time_advance_n (f : Signal) (n : ℕ) (z : ℂ) : 𝓩 (fun k => f (k + n)) z = z^n * 𝓩 f z - ∑ i in Finset.range n, z^(n - i) * f i := sorry

@[simp]
theorem ZTransform_exp_mul (f : Signal) (a : ℂ) (z : ℂ) : 𝓩 (fun k => a^(-k) * f k) z = 𝓩 f (a * z) := sorry
