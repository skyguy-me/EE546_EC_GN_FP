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
<center><h1>Lean4 Fourier-transform  implementation</h1></center>
<center><h2>Final Project WI 25 EE-546 B</h2></center>

<center>
Department of Electrical and Computer Engineering<br />
Unviersity of Washington<br />
Ember Chow and Gokul Nathan<br />
Winter 2025<br />
</center>
<br />

-/

import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Data.Real.Basic

set_option maxHeartbeats 1000000

open FourierTransform SchwartzMap

--namespace SchwartzMap

universe u w v

variable
  (k n : ℕ)
  (𝕜 : Type*) [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]

instance : NontriviallyNormedField 𝕜 := by exact DenselyNormedField.toNontriviallyNormedField


noncomputable instance : SeminormedAddCommGroup (𝓢(V, E)) where
  norm := SchwartzMap.seminorm 𝕜 k n
  dist_self := by intro x; simp
  dist_comm := by
    intro x y
    exact map_sub_rev (SchwartzMap.seminorm 𝕜 k n) x y
  dist_triangle := by
    intro x y z
    exact le_map_sub_add_map_sub (SchwartzMap.seminorm 𝕜 k n) x y z


noncomputable instance : SeminormedAddCommGroup (𝓢(V, E) →L[𝕜] 𝕜) where
  norm := fun T => ⨆ (f : 𝓢(V, E)) (hf : SchwartzMap.seminorm 𝕜 k n f ≤ 1), ‖T f‖
  dist_self := by
    intro x
    simp
    change ⨆ f, ⨆ _, ‖0‖ = 0
    simp only[norm_zero, Real.iSup_const_zero]
    --simp only[Real.iSup_const_zero]

  dist_comm := by
    intro T₁ T₂
    simp
    congrm ⨆ f, ⨆ _, ?_
    change ‖T₁ f - T₂ f‖ = ‖T₂ f - T₁ f‖
    exact norm_sub_rev (T₁ f) (T₂ f)

  dist_triangle := by
    intro T₁ T₂ T₃
    simp
    change ⨆ f, ⨆ _, ‖T₁ f - T₃ f‖ ≤ (⨆ f, ⨆ _, ‖T₁ f - T₂ f‖) + ⨆ f, ⨆ _, ‖T₂ f - T₃ f‖
    calc
      ⨆ f, ⨆ _, ‖T₁ f - T₃ f‖ = ⨆ f, ⨆ _, ‖(T₁ f - T₂ f) + (T₂ f - T₃ f)‖ := by
        congrm ⨆ f, ⨆ _, ?_
        simp

      _ ≤ ⨆ f, ⨆ _, ‖T₁ f - T₂ f‖ + ‖T₂ f - T₃ f‖ := by
        have h : ∀ (f : 𝓢(V, E)), ‖(T₁ f - T₂ f) + (T₂ f - T₃ f)‖ ≤ ‖T₁ f - T₂ f‖ + ‖T₂ f - T₃ f‖ := by
          intro f
          apply norm_add_le (T₁ f - T₂ f) (T₂ f - T₃ f)

        refine' ciSup_mono ?hbdd _
        refine bddAbove_def.mpr ?_
        let a := ContinuousLinearMap.isBoundedLinearMap T₁

      _ ≤ ⨆ f, ⨆ _, ‖T₁ f - T₂ f‖ + ⨆ f, ⨆ _, ‖T₂ f - T₃ f‖ := by
        --refine iSup_




        --refine @iSup_mono EReal _  _ (fun f => ‖(T₁ f - T₂ f) + (T₂ f - T₃ f)‖) (fun f => ‖T₁ f - T₂ f‖ + ‖T₂ f - T₃ f‖) ?_



instance : Module 𝕜 (𝓢(V, E) →L[𝕜] 𝕜) where
  add_smul := by exact fun r s x ↦ Module.add_smul r s x
  zero_smul := by exact fun x ↦ Module.zero_smul x



noncomputable def fourierTransformDistribution :
    (𝓢(V, E) →L[𝕜] 𝕜) →L[𝕜] (𝓢(V, E) →L[𝕜] 𝕜) where
  toFun T :=
    { toFun := fun φ => T (fourierTransformCLM 𝕜 φ)
      map_add' := by simp [map_add]
      map_smul' := by simp [map_smul]
      cont := by continuity
    }
  map_add' T₁ T₂ := by ext φ; simp [map_add]
  map_smul' a T := by ext φ; simp [map_smul]
  cont := by
    simp
    refine @continuous_of_linear_of_bound 𝕜 (𝓢(V, E) →L[𝕜] 𝕜) (L[𝕜] (𝓢(V, E) →L[𝕜] 𝕜)) _ _ _ _ _ f hf h_bound
--end SchwartzMap
