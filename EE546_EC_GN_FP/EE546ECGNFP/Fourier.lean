import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Distribution.FourierSchwartz

open FourierTransform SchwartzMap

variable
  (𝕜 : Type*) [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]


noncomputable def fourierTransformDistrMap (T : 𝓢(V, E) →L[𝕜] 𝕜) :
    (𝓢(V, E) → 𝕜) :=
  fun φ => T (fourierTransformCLM 𝕜 φ)

lemma fourierTransformDistrMapAdd : IsBoundedLinearMap 𝕜 fourierTransformDistrMap :=
  sorry


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
    refine continuous_of_linear_of_bound ?_ ?_ _?




    --dsimp[ContinuousLinearMap 𝕜]
