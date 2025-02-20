import Mathlib.Tactic
import Mathlib.Data.Complex.Abs

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

notation "δ" => unit_impulse

@[simp]
def unit_step (k : ℤ) : ℂ :=
  if k ≥ 0 then 1 else 0

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

theorem zt_unit_impulse {z : ℂ} (h_roc : z ≠ 0) : 𝓩 δ z = 1 := by
  -- Change the goal into an ε criterion.
  rw[ZTransform]
  refine' HasSum.tsum_eq _
  refine' Metric.tendsto_atTop.mpr _

  -- Introduce ε and hε
  intro ε _

  -- The notation in the goal is a bit funny. N and n are both sets of integers.
  -- n ≥ N means N ⊆ n.
  -- This makes sense, since we're summing over all the integers.

  -- Roughly, this is saying, for a sufficiently large set of set of integers covered,
  -- The sum is sufficiently close to ε

  -- Use N = {0}
  use singleton 0
  intro n hn

  -- Rewrite the goal so it's more sensible
  change ‖∑ b ∈ n, (fun k ↦ δ k * z ^ (-k)) b - 1‖ < ε

  -- Show that 0 ∈ n. Since N = {0} ⊆ n, this is trivial.
  have h_zero : 0 ∈ n := by exact Finset.zero_subset.mp hn

  -- Since the delta function is zero everywhere except 0, the sum should be 1.
  have hs : ∑ b ∈ n, (fun x ↦ Complex.abs (if x = 0 then (z ^ x)⁻¹ else 0)) b = 1 := by
    --Finset.add_sum_erase n can take a term out of the sum (assuming it's in it)
    --In this case, since 0 ∈ n, we can take the 0 term out.
    rw[←Finset.add_sum_erase n (fun x ↦ Complex.abs (if x = 0 then (z ^ x)⁻¹ else 0)) h_zero]

    -- Simplify a bit. Lean can see that the 0 term evalutes to 1 and then subtracts
    -- it across.
    simp

    -- Now we just have to show the rest of the sum is zero.

    -- Since all its terms are zero, the sum should be zero.
    apply Finset.sum_eq_zero

    -- We know k is not zero since we removed it from the set.
    intro k hk
    have hk_nonzero : k ≠ 0 := by exact Finset.ne_of_mem_erase hk

    -- Since k isn't 0, the delta function is zero.
    simp only[hk_nonzero]
    exact (AbsoluteValue.eq_zero Complex.abs).mpr rfl

  -- So our sum is exactly 1, which is our limit. We can see then that
  -- For all sets containing at least 0, our distance from the limit
  -- is 0, which is definitely "sufficiently close" (0 < ε)
  simp[hs, h_zero]
  assumption

-- For some reason, this isn't a theorem in Mathlib.
-- Mathlib has a version of this where n is complex, but that
-- introduces an additional constraint that arg x ≠ π. No such
-- restriction happens so long as the power is an integer.
theorem inv_cpow_int (x : ℂ) (n : ℤ) : x⁻¹ ^ n = (x ^ n)⁻¹ := by
  simp -- though mathlib does have enough theorems to solve by simp...

/--
Suppose f : β → α. And suppose β ≃ γ (there's a bijection, e, between them).

f has a sum over all elements of β iff f ∘ e has a sum over all elements of γ.

Useful for turning sums over one set into sums over another set. For example,
this lets you show that:

∑' (i : NonNegInt) f i = ∑' (n : ℕ) f n
-/
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

  -- We tackle this by partitioning the sum into the negative terms and non-negative terms.
  -- We then show each infinite sum has a value.

  -- Show that ∑' (k < 0), u k * z ^ (-k) = 0
  have s_neg : HasSum (fun k : NegInt ↦ f k) 0 := by
    -- Show u k * z ^ (-k) = 0 forall k.
    have f_zero : ∀ (k : NegInt), f k = 0 := by
      simp[f, u, unit_step]
      intro a ha _
      have : a < 0 := by assumption
      linarith

    -- Since the terms of the sum are all zero, the sum must also be zero
    simp[f_zero]
    exact hasSum_zero

  -- Show that ∑' (k ≥ 0) u k * z ^ (-k) = 1 / (1 - z⁻¹)
  have s_nonneg : HasSum (fun (k : NonNegInt) ↦ f k) (1 / (1 - z⁻¹)) := by
    -- This first looks confusing, but we're just trying to change the sum from:
    -- ∑' (k : NonNegInt) f k → ∑' (n : ℕ) f n.

    -- Lean is sadly not smart enough to understand these are equivalent.
    refine' (hasSum_equiv
      (f := fun k : NonNegInt ↦ f k)
      (a := (1 / (1 - z⁻¹))) nonNegInt_nat_equiv.symm).mp _

    -- It doesn't get you all the way there... but further simplification will do it.

    -- Since we're on the positive side, the step function is 1
    have u_one : ∀ (k : NonNegInt), u k = 1 := by
      simp[u]
      intros
      assumption

    -- ‖z‖ > 1 → ‖z⁻¹‖ < 1
    have hz : ‖z⁻¹‖ < 1 := by
      rw[norm_inv, inv_lt_comm₀, inv_one]
      <;> linarith

    -- Do some simplification here. We want the sum to be in the form:
    -- ∑ (n : ℕ) (z⁻¹) ^ n since that's a geometric series.
    simp[f, u_one]
    simp only[←inv_cpow_int]
    change HasSum (fun n : ℕ ↦ z⁻¹ ^ n) (1 - z⁻¹)⁻¹

    -- Apply the geometric series theorem.
    -- ∑ (n : ℕ) a ^ n = 1 / (1 - a) if ‖a‖ < 1 for a = z⁻¹
    exact hasSum_geometric_of_norm_lt_one hz

  --Rewrite the original sum so its in terms of our sets.
  rw[←tsum_univ, ←neg_nonneg_union]

  -- Show that we can break the sum up into its non-negative and negative parts.
  -- ∑' (a : α) f a + ∑' (b : β) f b = ∑' (c : α ∪ β) f c
  have : (tsum fun (k : ↑(NegInt ∪ NonNegInt)) ↦ f ↑k) =
    ∑' (k : ↑NegInt), f ↑k + ∑' (k : ↑NonNegInt), f ↑k :=
    -- This only works if α and β are disjoint and that
    -- ∑' (a : α) f a and ∑' (b : β) f b are well-defined.
    tsum_union_disjoint int_neg_nonneg_disjoint s_neg.summable s_nonneg.summable

  -- Break up the sum, then apply the results we got earlier for each sub-sum.
  rw[this, s_neg.tsum_eq, s_nonneg.tsum_eq, zero_add]


noncomputable def discrete_convolution (f g : Signal) : Signal :=
  fun k => ∑' m : ℤ, f m * g (k - m)

def HasZTransform {z : ℂ} (f : Signal) := Summable fun k ↦ f k * z ^ (-k)

@[simp]
theorem ZTransform_linear {z : ℂ} (f₁ f₂ : Signal) (hf₁ : @HasZTransform z f₁) (hf₂ : @HasZTransform z f₂) (a b : ℂ) : 𝓩 (fun k => a * f₁ k + b * f₂ k) z = a * 𝓩 f₁ z + b * 𝓩 f₂ z := by
  simp only[ZTransform]
  calc
  ∑' (k : ℤ), (a * f₁ k + b * f₂ k) * z ^ (-k) = ∑' (k : ℤ), (a * f₁ k * z ^ (-k) + b * f₂ k * z ^ (-k)) :=
    by group

  _ = ∑' (k : ℤ), a * f₁ k * z ^ (-k) + ∑' (k : ℤ), b * f₂ k * z ^ (-k) := by
    rw[tsum_add]

  _ = ∑' (k : ℤ), a * (f₁ k * z ^ (-k)) + ∑' (k : ℤ), b * (f₂ k * z ^ (-k)) := by group
  _ = a * ∑' (k : ℤ), f₁ k * z ^ (-k) + b * ∑' (k : ℤ), f₂ k * z ^ (-k) := by rw[tsum_mul_left, tsum_mul_left]

@[simp]
theorem ZTransform_time_delay (f : Signal) (n : ℤ) (z : ℂ) :  𝓩 (fun k => f (k - n)) z = z ^ (-n) * 𝓩 f z := by
  rw [ZTransform]
  have : (fun k => f (k - n) * z ^ (-k)) = (fun k => f k * z ^ (-(k + n))) := by
    simp
    funext k
    sorry
  sorry

@[simp]
theorem ZTransform_time_advance_one (f : Signal) (z : ℂ) : 𝓩 (fun k => f (k + 1)) z = z * 𝓩 f z - z * f 0 := by
  sorry

@[simp]
theorem ZTransform_time_advance_n (f : Signal) (n : ℕ) (z : ℂ) : 𝓩 (fun k => f (k + n)) z = z^n * 𝓩 f z - ∑ i in Finset.range n, z^(n - i) * f i := by
  sorry

@[simp]
theorem ZTransform_exp_mul (f : Signal) (a : ℂ) (z : ℂ) : 𝓩 (fun k => a^(-k) * f k) z = 𝓩 f (a * z) := by
  sorry

@[simp]
theorem ZTransform_convolution (f g : Signal) (z : ℂ) : 𝓩 (discrete_convolution f g) z = 𝓩 f z * 𝓩 g z := by
  rw [ZTransform] -- ∑' (k : ℤ), discrete_convolution f g k * z ^ (-k) = 𝓩 f z * 𝓩 g z
  simp only [discrete_convolution] -- ∑' (k : ℤ), (∑' (m : ℤ), f m * g (k - m)) * z ^ (-k) = 𝓩 f z * 𝓩 g z


  let h := fun k => ∑' m : ℤ, f m * g (k - m)
  let t := fun k => h k * z ^ (-k)
  sorry


-- theorem ZTransform_IVT: := by
--   sorry

-- theorem ZTransform_FVT := by
--   sorry
