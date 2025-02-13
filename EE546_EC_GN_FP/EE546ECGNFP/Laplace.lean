import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.Data.Set.Basic


open FourierTransform
open MeasureTheory
open Real

#check 𝓕


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
