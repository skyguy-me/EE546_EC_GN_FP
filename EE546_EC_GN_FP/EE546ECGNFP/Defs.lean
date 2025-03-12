--  * Copyright (C) <2025> <EMBER CHOW AND GOKUL NATHAN>
--  *
--  * This program is free software; you can redistribute it and/or modify
--  * it under the terms of the GNU General Public License as published by
--  * the Free Software Foundation; either version 3 of the License, or (at
--  * your option) any later version.
--  *
--  * This program is distributed in the hope that it will be useful,
--  * but WITHOUT ANY WARRANTY; without even the implied warranty of
--  * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
--  * General Public License for more details.
--  *
--  * You should have received a copy of the GNU General Public License
--  * along with this program; if not, see <http://www.gnu.org/licenses/>.



/-
<center><h1>Definitions supporting Lean4 implementation of Z-transforms</h1></center>
<center><h2>Final Project WI 25 EE-546 B</h2></center>

<center>
Department of Electrical and Computer Engineering<br />
Unviersity of Washington<br />
Ember Chow and Gokul Nathan<br />
Winter 2025<br />
</center>
<br />

-/

import Init.Data.Int.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Controls

set_option maxHeartbeats 1000000

-- Some useful sets for partitioning sums over ℤ.
@[simp] def PosInt : Set ℤ := { k | k > 0 }
@[simp] def NonNegInt : Set ℤ := { k | k ≥ 0 }
@[simp] def NegInt : Set ℤ := { k | k < 0 }
@[simp] def NonPosInt : Set ℤ := { k | k ≤ 0 }

@[simp]
theorem PosIntComp : PosIntᶜ = NonPosInt := by
  ext k
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
  exact Int.not_lt


@[simp]
theorem NonPosIntComp : NonPosIntᶜ = PosInt := by
  rw [←PosIntComp, compl_compl]

@[simp]
theorem NegIntComp : NegIntᶜ = NonNegInt := by
  ext k
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
  exact Int.not_lt


@[simp]
theorem NonNegIntComp : NonNegIntᶜ = NegInt := by
  rw [←NegIntComp, compl_compl]

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
    intro _ ha _ hb
    simp at ha hb
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
    intro _ ha _ hb
    simp at ha hb
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
    intro _ ha _ hb
    simp at ha hb
    linarith

/--
Symmetric version of int_neg_nonneg_disjoint
-/
@[simp]
lemma int_nonneg_neg_disjoint : Disjoint NonNegInt NegInt := by
  exact Disjoint.symm int_neg_nonneg_disjoint


def univ_equiv (α : Type*) : α ≃ @Set.univ α where
  toFun := fun a ↦ ⟨a, by trivial⟩
  invFun := fun
    | ⟨a, _⟩ => a

  left_inv := by exact congrFun rfl
  right_inv := by exact congrFun rfl

theorem hasSum_univ {α β : Type*} {a : α} [AddCommMonoid α] [TopologicalSpace α]
  {f : β → α} : HasSum (fun x : @Set.univ β ↦ f x) a ↔ HasSum f a := by
    exact (Equiv.hasSum_iff (α := α) (f := f) (a := a) (univ_equiv β).symm)

theorem summable_univ {α β : Type*} [AddCommMonoid α] [TopologicalSpace α]
  {f : β → α} : Summable (fun x : @Set.univ β ↦ f x) ↔ Summable f := by
    exact (Equiv.summable_iff (α := α) (f := f) (univ_equiv β).symm)

--theorem hasSum_bij' {α β γ : Type*} {a : α} [AddCommMonoid α] [TopologicalSpace α]
  --{f : β → α} {g : β → β} : (Function.Bijective g) →
  --(HasSum (fun (x : g '' @Set.univ β) ↦ f x) a ↔ HasSum f a) := by
    --intro hg
    --have : @Set.univ β ≃ g '' @Set.univ β := by
      --refine (Equiv.ofBijective (fun x : @Set.univ β ↦ (⟨g x, ?_⟩ : (g '' @Set.univ β)))  ?_).symm


theorem hasSum_bij {α β γ : Type*} {a : α} [AddCommMonoid α] [TopologicalSpace α]
  {f : β → α} {i : γ → β} : (Function.Bijective i) →
  (HasSum (f ∘ i) a ↔ HasSum f a) := by
    intro hi
    exact Equiv.hasSum_iff (a := a) (f := f) (by exact Equiv.ofBijective i hi)

theorem hasSum_int_shift_neg {α : Type*} {a : α} [AddCommMonoid α] [TopologicalSpace α]
  {f : ℤ → α} (k₀ : ℤ) : HasSum (fun k ↦ f (k - k₀)) a ↔ HasSum f a := by
    apply hasSum_bij
    exact AddGroup.addRight_bijective (-k₀)

theorem hasSum_int_shift {α : Type*} {a : α} [AddCommMonoid α] [TopologicalSpace α]
  {f : ℤ → α} (k₀ : ℤ) : HasSum (fun k ↦ f (k + k₀)) a ↔ HasSum f a := by
    apply hasSum_bij
    exact AddGroup.addRight_bijective k₀
