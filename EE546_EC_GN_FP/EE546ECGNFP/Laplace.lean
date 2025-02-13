import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Integral.Lebesgue
--import Mathlib.Data.Set.Basic


open FourierTransform MeasureTheory Real

#check 𝓕


--variable {𝕜 : Type*} [CommRing 𝕜]
  --{V : Type*} [AddCommGroup V] [Module 𝕜 V] [MeasurableSpace V]
  --{W₁ : Type*} [AddCommGroup W₁] [Module 𝕜 W₁]
  --{W₂ : Type*} [AddCommGroup W₂] [Module 𝕜 W₂]
  --{E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  --[NormedAddCommGroup G] [NormedSpace ℂ G]


--def laplaceIntegral (e : AddChar 𝕜 𝕊) (μ : Measure V) (L : V →ₗ[𝕜] W₂ →ₗ[𝕜] 𝕜) (f : V → E)
    --(g : V → W₁ → ℝ) (w₁ : W₁) (w₂ : W₂) : E :=
  --∫ v, (Complex.exp (-g v w₁) * e (-L v w₂)) • f v ∂μ

--noncomputable def laplaceIntegral (μ : Measure ℝ) (f : ℝ → E)  (s : ℂ) : E :=
  --∫ t, Complex.exp (-s * t) • f t ∂μ

--variable (t : ℝ)

def j := Complex.I

noncomputable def f (t : ℝ) : ℂ := Complex.exp (j * t)

noncomputable def F := 𝓕 f

example : 𝓕 f = dirac 1 := sorry



--noncomputable def realLaplaceIntegral (f : ℝ → E)  (s : ℂ) : E := laplaceIntegral Lebesgue.

--notation "𝓛" => laplaceIntegral


open MeasureTheory

/--
A simple example: the integral of a measurable function `f : α → ℝ` with respect to the Dirac
measure at `x : α` is just `f x`.
-/
example {α : Type*} [MeasurableSpace α] (x : α) (f : α → ℝ) (hf : Measurable f) :
  ∫ a, f a ∂(Measure.dirac x) = f x :=
  sorry

def fourierMeasure (μ : Measure ℝ) (w : ℝ) : ℂ :=
∫ x in 𝐞 (-x * w) ∂μ
  sorry
