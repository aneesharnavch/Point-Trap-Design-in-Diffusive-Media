module

public import TimeTraps.Analysis.ReflectedFoldDensity
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-! The one-time law obtained by folding a real Gaussian. At positive
variance its density on the open interval is the sum over the two lattice
preimages. The total mass is one and the endpoints have no atoms. Zero
variance is kept as the separate Dirac law. These statements do not assert
a Markov property or a conditional transition law. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set TimeTraps.Analysis
open scoped ENNReal NNReal

def reflectedGaussianLaw (L x : ℝ) (v : ℝ≥0) : Measure ℝ :=
  (gaussianReal x v).map (reflectedFold L)

def reflectedGaussianKernel (L x : ℝ) (v : ℝ≥0) (y : ℝ) : ℝ≥0∞ :=
  reflectedFoldDensity L (gaussianPDF x v) y

instance reflectedGaussianLaw_isProbabilityMeasure (L x : ℝ) (v : ℝ≥0) :
    IsProbabilityMeasure (reflectedGaussianLaw L x v) :=
  Measure.isProbabilityMeasure_map (reflectedFold_measurable L).aemeasurable

theorem reflectedGaussianKernel_measurable (L x : ℝ) (v : ℝ≥0) :
    Measurable (reflectedGaussianKernel L x v) :=
  reflectedFoldDensity_measurable L (measurable_gaussianPDF x v)

theorem reflectedGaussianKernel_formula (L x : ℝ) (v : ℝ≥0) (y : ℝ) :
    reflectedGaussianKernel L x v y = ∑' k : ℤ,
      (ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹ *
        Real.exp (-((y + k * (2 * L)) - x) ^ 2 / (2 * v))) +
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹ *
        Real.exp (-((k * (2 * L) - y) - x) ^ 2 / (2 * v)))) := rfl

theorem reflectedGaussianLaw_density (L : ℝ) (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : v ≠ 0) :
    reflectedGaussianLaw L x v =
      (volume.restrict (Ioo 0 L)).withDensity (reflectedGaussianKernel L x v) := by
  rw [reflectedGaussianLaw, gaussianReal_of_var_ne_zero x hv]
  exact reflectedFoldDensity_map L hL (measurable_gaussianPDF x v)

theorem reflectedGaussianKernel_mass (L : ℝ) (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : v ≠ 0) :
    (∫⁻ y in Ioo 0 L, reflectedGaussianKernel L x v y) = 1 := by
  have he : reflectedGaussianLaw L x v univ = 1 := measure_univ
  rw [reflectedGaussianLaw_density L hL x hv, withDensity_apply _ MeasurableSet.univ] at he
  simpa only [Measure.restrict_univ] using he

theorem reflectedGaussianLaw_zero (L x : ℝ) :
    reflectedGaussianLaw L x 0 = Measure.dirac (reflectedFold L x) := by
  rw [reflectedGaussianLaw, gaussianReal_zero_var, Measure.map_dirac' (reflectedFold_measurable L)]

theorem reflectedGaussianLaw_singleton (L : ℝ) (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : v ≠ 0) (y : ℝ) : reflectedGaussianLaw L x v {y} = 0 := by
  rw [reflectedGaussianLaw, gaussianReal_of_var_ne_zero x hv]
  exact reflectedFoldDensity_singleton L hL (gaussianPDF x v) y

end TimeTraps.Probability

end
