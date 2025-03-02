import Mathlib.Tactic
-- import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Complex.Abs
-- import Paperproof

open Complex

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000

-- Because we're al engineers here.
def j : ℂ := Complex.I

def Signal : Type := ℤ → ℂ

-- Some useful sets for partitioning sums over ℤ.
def PosInt : Set ℤ := { k | k > 0 }
def NonNegInt : Set ℤ := { k | k ≥ 0 }
def NegInt : Set ℤ := { k | k < 0 }
def NonPosInt : Set ℤ := { k | k ≤ 0 }

/--
The union of non-positive integers and positive integers is ℤ.
-/
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

/--
Symmetric verison of nonpos_pos_union
-/
@[simp]
theorem pos_nonpos_union : PosInt ∪ NonPosInt = Set.univ := by
  rw[←Set.union_comm]
  exact nonpos_pos_union

/--
The union of non-negative integers and negative integers is ℤ.
-/
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

/--
Symmetric verison of neg_nonneg_union
-/
@[simp]
theorem neg_nonneg_union : NegInt ∪ NonNegInt = Set.univ := by
  rw[←Set.union_comm]
  exact nonneg_neg_union

/--
Shows that there's a bijection between the non-negative integers and ℕ.
-/
@[simp]
def nonNegInt_nat_equiv : NonNegInt ≃ ℕ where
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

/--
Shows that the positive integers and the negative integers are disjoint.
That is, PosInt ∩ NegInt = ∅
-/
@[simp]
lemma int_pos_neg_disjoint : Disjoint PosInt NegInt := by
    refine' Set.disjoint_iff_forall_ne.mpr _
    intro a _ b _

    have : a > 0 := by assumption
    have : b < 0 := by assumption
    linarith

/--
Symmetric verison of int_pos_neg_disjoint
-/
@[simp]
lemma neg_pos_int_disjoint : Disjoint NegInt PosInt := by
  exact Disjoint.symm int_pos_neg_disjoint

/--
Shows that the positive integers and the non-positive integers are disjoint.
That is, PosInt ∩ NonPosInt = ∅
-/
@[simp]
lemma int_pos_nonpos_disjoint : Disjoint PosInt NonPosInt := by
    refine' Set.disjoint_iff_forall_ne.mpr _
    intro a _ b _

    have : a > 0 := by assumption
    have : b ≤ 0 := by assumption
    linarith

/--
Symmetric version of int_pos_nonpos_disjoint
-/
@[simp]
lemma int_nonpos_pos_disjoint : Disjoint NonPosInt PosInt := by
  exact Disjoint.symm int_pos_nonpos_disjoint

/--
Shows that the negative integers and the non-negative integers are disjoint.
That is, NegInt ∩ NonNegInt = ∅
-/
@[simp]
lemma int_neg_nonneg_disjoint : Disjoint NegInt NonNegInt := by
    refine' Set.disjoint_iff_forall_ne.mpr _
    intro a _ b _

    have : a < 0 := by assumption
    have : b ≥ 0 := by assumption
    linarith

/--
Symmetric version of int_neg_nonneg_disjoint
-/
@[simp]
lemma int_nonneg_neg_disjoint : Disjoint NonNegInt NegInt := by
  exact Disjoint.symm int_neg_nonneg_disjoint

@[simp]
noncomputable def zt_kernel (x : Signal) (z : ℂ) : ℤ → ℂ :=
  fun k ↦ x (k) * z^(-k : ℤ)

@[simp]
noncomputable def ZTransform (x : Signal) (z : ℂ) :=
  ∑' k : ℤ, x (k) * z^(-k : ℤ)

def HasZTransform {z : ℂ} (x : Signal) := HasSum (fun (k : ℤ) ↦ x k * z ^ (-k : ℤ))

@[simp]
noncomputable def ZTransformUnilateral (x : Signal) (z : ℂ) :=
  ∑' k : ℕ, x (k) * z^(-k : ℤ)

def HasZTransformUnilateral (x : Signal) (z : ℂ) := HasSum (fun (n : ℤ) ↦ x n * z ^ (-n : ℤ))

@[simp]
noncomputable def ZTransformUnilateral' (x : Signal) (z : ℂ) :=
  ∑' k : NonNegInt, x (k) * z ^ (-↑k : ℤ)

@[simp]
noncomputable def DiscreteTimeFourierTransform (x : Signal) (ω : ℝ) :=
  ∑' k : ℤ, x (k) * Complex.exp (-j * ω * k)

@[simp]
alias ZT := ZTransform

@[simp]
alias DTFT := DiscreteTimeFourierTransform

notation "𝓩" => ZTransform
notation "𝓩_u" => ZTransformUnilateral
notation "𝓕_d" => DiscreteTimeFourierTransform

variable (x : Signal)


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

/--
The rect function is one on [a, b)
-/
@[simp]
def rect (a b : ℤ) (k : ℤ) :=
  unit_step (k - a) - unit_step (k - b)

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


theorem zt_unit_impulse {z : ℂ} (k₀ : ℤ) : @HasZTransform z (fun k ↦ δ (k - k₀)) (z ^ (-k₀)) := by
  rw[HasZTransform]
  simp

  have : ∀ k : ℤ, k - k₀ = 0 ↔ k = k₀ := by intro _; exact Int.sub_eq_zero
  simp only[this]

  have : ∀ z : ℂ, ∀ k : ℤ, (if k = k₀ then (z ^ k)⁻¹ else 0) = (if k = k₀ then z ^ (-k₀) else 0) := by
    intro _ k
    by_cases hk : k = k₀
    <;> simp[hk]
  simp [this]

  exact hasSum_ite_eq k₀ (z ^ k₀)⁻¹

def univ_equiv (α : Type*) : α ≃ @Set.univ α where
  toFun := fun a ↦ ⟨a, by trivial⟩
  invFun := fun
    | ⟨a, _⟩ => a

  left_inv := by exact congrFun rfl
  right_inv := by exact congrFun rfl

theorem hasSum_univ {α β : Type*} {a : α} [AddCommMonoid α] [TopologicalSpace α]
  {f : β → α} : HasSum (fun x : @Set.univ β ↦ f x) a ↔ HasSum f a := by
    exact (Equiv.hasSum_iff (α := α) (f := f) (a := a) (univ_equiv β).symm)

theorem ZTUnilateral_hasSum_equiv {z : ℂ} {a : ℂ} (x : Signal) :
  HasSum (fun n : ℕ ↦ x n * z ^ (-n : ℤ)) a ↔
  HasSum (fun k : NonNegInt ↦ x k * z ^ (-k : ℤ)) a := by
    exact Equiv.hasSum_iff nonNegInt_nat_equiv.symm (a := a) (
      f := fun (k : NonNegInt) ↦ x k * z ^ (-k : ℤ))

theorem ZTUnilateral_tsum_equiv {z : ℂ} (x : Signal) :
  (ZTransformUnilateral x) z = (ZTransformUnilateral' x) z := by
    exact Equiv.tsum_eq nonNegInt_nat_equiv.symm (
      fun (k : NonNegInt) ↦ x k * z ^ (-k : ℤ)
    )

theorem indicator_one_mul {α β : Type*} [Semiring β] {A : Set α} (a : α) (f : α → β) :
    A.indicator 1 a * f a = A.indicator (fun a' ↦ f a') a := by
      by_cases ha : a ∈ A
      <;> simp[ha]


theorem zt_sum_unit_step {z : ℂ} {f : Signal} {S : ℂ} :
    HasSum (fun (k : ℤ) ↦ u k * f k * z ^ (-k : ℤ)) S ↔
    HasSum (fun (n : ℕ) ↦ f n * z ^ (-n : ℤ)) S := by

      apply Iff.intro
      . intro hmp

        have h_ind : ∀ k : ℤ, NonNegInt.indicator 1 k * (f k * z ^ (-k)) =
          NonNegInt.indicator (fun k' ↦ f k' * z ^ (-k')) k := by
            exact indicator_one_mul (A := NonNegInt) (f := fun k : ℤ ↦ f k * z ^ (-k : ℤ))

        simp only [mul_assoc] at hmp
        --simp only [indicator_one_mul (A := NonNegInt) (f := fun k : ℤ ↦ f k * z ^ (-k : ℤ))]
        simp only[u, unit_step_equiv_indicator, h_ind] at hmp
        simp only[ZTUnilateral_hasSum_equiv]

        exact (hasSum_subtype_iff_indicator).mpr hmp

      . intro hmpr
        simp only[←hasSum_univ (f := fun k : ℤ ↦ u k * f k * z ^ (-k : ℤ))]
        rw[←neg_nonneg_union]

        convert HasSum.add_disjoint int_neg_nonneg_disjoint (a := 0) (b := S)
          (f := fun k : ℤ ↦ u k * f k * z ^ (-k : ℤ)) ?S_neg ?S_nonneg

        . rw[zero_add]

        . change HasSum (fun k : NegInt ↦ u k * f k * z ^ (-k : ℤ)) 0
          convert hasSum_zero with k
          calc
            u ↑k * f ↑k * z ^ (-k : ℤ) = 0 * f ↑k * z ^ (-k : ℤ) := by rw[u, unit_step_of_neg]
            _ = 0 := by rw[zero_mul, zero_mul]

        . change HasSum (fun k : NonNegInt ↦ u k * f k * z ^ (-k : ℤ)) S
          simp only[u, unit_step_of_nonneg, one_mul, ←ZTUnilateral_hasSum_equiv]
          exact hmpr


theorem zt_unit_step {z : ℂ} (h_roc : ‖z‖ > 1) : @HasZTransform z u (1 / (1 - z⁻¹)) := by
  rw[HasZTransform]

  have : ∀ k, u k * z ^ (-k) = u k * 1 * z ^ (-k) := by simp
  simp only [this]

  refine' zt_sum_unit_step.mpr _
  simp
  simp only[←inv_pow]

  refine' hasSum_geometric_of_norm_lt_one _
  rw[norm_inv, inv_lt_comm₀] <;> linarith


noncomputable def discrete_convolution (f g : Signal) : Signal :=
  fun k => ∑' m : ℤ, f m * g (k - m)

def ZTransformable {z : ℂ} (f : Signal) := Summable fun k ↦ f k * z ^ (-k)

-- @[simp]
-- theorem ZTransform_linear {z : ℂ} (f₁ f₂ : Signal) (hf₁ : @ZTransformable z f₁) (hf₂ : @ZTransformable z f₂) (a b : ℂ) : 𝓩 (fun k => a * f₁ k + b * f₂ k) z = a * 𝓩 f₁ z + b * 𝓩 f₂ z := by
--   simp only[ZTransform]
--   calc
--   ∑' (k : ℤ), (a * f₁ k + b * f₂ k) * z ^ (-k) = ∑' (k : ℤ), (a * f₁ k * z ^ (-k) + b * f₂ k * z ^ (-k)) :=
--     by group

--   _ = ∑' (k : ℤ), a * f₁ k * z ^ (-k) + ∑' (k : ℤ), b * f₂ k * z ^ (-k) := by
--     rw[tsum_add]

--   _ = ∑' (k : ℤ), a * (f₁ k * z ^ (-k)) + ∑' (k : ℤ), b * (f₂ k * z ^ (-k)) := by group
--   _ = a * ∑' (k : ℤ), f₁ k * z ^ (-k) + b * ∑' (k : ℤ), f₂ k * z ^ (-k) := by rw[tsum_mul_left, tsum_mul_left]

-- @[simp]
-- theorem ZTransform_time_delay (f : Signal) (n : ℤ) (z : ℂ) :  𝓩 (fun k => f (k - n)) z = z ^ (-n) * 𝓩 f z := by
  -- simp only[ZTransform]

  -- let g := fun k : ℤ => f (k - n) * z ^ (-k)
  -- let h := fun m : ℤ => f m * z ^ (-(m + n))

  -- have h_i : (fun k => f (k - n) * z ^ (-k)) = (fun m => f m * z ^ (-(m + n))) := by
  --   ext m
  --   -- ring_nf



--   sorry

-- @[simp]
-- theorem ZTransform_time_advance_one (f : Signal) (z : ℂ) : 𝓩 (fun k => f (k + 1)) z = z * 𝓩 f z - z * f 0 := by
--   sorry

-- @[simp]
-- theorem ZTransform_time_advance_n (f : Signal) (n : ℕ) (z : ℂ) : 𝓩 (fun k => f (k + n)) z = z^n * 𝓩 f z - ∑ i in Finset.range n, z^(n - i) * f i := by
--   sorry

-- class ZTransformable (f : Signal) (z : ℂ) : Prop where
--   summable : Summable (λ k : ℤ, f k * z^(-k))

-- instance (f : Signal) (z : ℂ) [ZTransformable f z] : HasZTransform f z (ZTransform f z) :=
--   by
--     rw [HasZTransform, ZTransform]
--     exact (ZTransformable.summable f z).hasSum

-- theorem zt_unit_step {z : ℂ} (h_roc : ‖z‖ > 1) : @HasZTransform z u (1 / (1 - z⁻¹)) := by sorry

theorem ZTransform_exp_mul (f : Signal) (z : ℂ) (a : ℂ) (F : ℂ → ℂ):
 @HasZTransform  z f (F z) →
 @HasZTransform z (λ k ↦ a^ (-k) * f k) (F (z * a) ):= by

  unfold HasZTransform -- HasSum (fun k ↦ f k * z ^ (-k)) (F z) → HasSum (fun k ↦ (fun k ↦ a ^ (-k) * f k) k * z ^ (-k)) (F (z * a))
  intro h -- HasSum (fun k ↦ (fun k ↦ a ^ (-k) * f k) k * z ^ (-k)) (F (z * a))
  have :  (λ k ↦ a ^ (-k) * f k * z ^ (-k)) =  (λ k ↦ (a*z)^(-k) * f k) := by
    ext k

    calc
      a ^ (-k) * f k * z ^ (-k) = a ^ (-k) * z ^ (-k) *  f k := by ring
      _ = (a *z)^ (-k)  *  f k :=  by  rw[mul_zpow]

  simp[this] -- HasSum (fun k ↦ (a ^ k)⁻¹ * f k * (z ^ k)⁻¹) (F (z * a))





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
-- theorem ZTransform_convolution (f g : Signal) (z : ℂ) : 𝓩 (discrete_convolution f g) z = 𝓩 f z * 𝓩 g z := by
--   rw [ZTransform] -- ∑' (k : ℤ), discrete_convolution f g k * z ^ (-k) = 𝓩 f z * 𝓩 g z
--   simp only [discrete_convolution] -- ∑' (k : ℤ), (∑' (m : ℤ), f m * g (k - m)) * z ^ (-k) = 𝓩 f z * 𝓩 g z


--   let h := fun k => ∑' m : ℤ, f m * g (k - m)
--   let t := fun k => h k * z ^ (-k)
--   sorry


-- theorem ZTransform_IVT: := by
--   sorry

-- theorem ZTransform_FVT := by
--   sorry
