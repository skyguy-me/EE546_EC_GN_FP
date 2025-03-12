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


import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed

import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Complex.Basic

import Mathlib.Algebra.Group.Indicator

import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Basic
import Mathlib.Topology.Filter

import Mathlib.Tactic.Linarith


import EE546ECGNFP.Defs -- Useful definitions for implementing engineering Z-transforms
import EE546ECGNFP.Signal -- USeful examining the signal properties

open Filter Topology Controls Controls.Discrete

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000

-- Basic Definiton of Z-transforms
@[simp]
noncomputable def ZTransform (x : DiscreteSignal) (z : ℂ) :=
  ∑' k : ℤ, x (k) * z^(-k : ℤ)

@[simp]
def HasZTransform (f : DiscreteSignal) (F : ℂ → ℂ) (z : ℂ) := HasSum (fun (k : ℤ) ↦ f k * z ^ (-k : ℤ)) (F z)

@[simp]
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

theorem zt_unit_impulse {z : ℂ} (k₀ : ℤ) : HasZTransform (fun k ↦ δ (k - k₀)) (fun z : ℂ ↦ (z ^ (-k₀))) z := by
  simp[Int.sub_eq_zero]
  convert hasSum_ite_eq k₀ (z ^ k₀)⁻¹
