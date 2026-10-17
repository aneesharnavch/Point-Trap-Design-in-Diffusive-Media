module

public import TimeTraps.Probability.BrownianBoundedOptionalSampling

@[expose] public section

/-! Two bounded stopping times and zero expectations for the same
completed continuous Brownian integral. All stopping times here are
arbitrary nonnegative real-valued times, without a range restriction. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

theorem brownianCompletedIntegralPath_mean (f : BrownianIntegrand) (T : ℝ≥0) :
    (∫ ω, brownianCompletedIntegralPath f T ω ∂brownianCompletedMeasure) = 0 := by
  calc
    _ = ∫ ω, brownianIntegralGlobalPath f T ω ∂brownianDyadicMeasure :=
      completedMeasure_integral brownianDyadicMeasure (brownianIntegralGlobalPath_measurable f T).aestronglyMeasurable
    _ = ∫ ω, brownianStochasticIntegralProcess f T ω ∂brownianDyadicMeasure :=
      integral_congr_ae (brownianIntegralGlobalPath_martingale_ae f T)
    _ = 0 := brownianIntegralProcess_mean brownianDyadicPath_isPreBrownianReal f T

theorem brownianCompletedIntegralPath_stopped_mean (f : BrownianIntegrand)
    {τ : BrownianCompletedSample → ℝ≥0} {T : ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (hbound : ∀ ω, τ ω ≤ T) :
    (∫ ω, brownianCompletedIntegralPath f (τ ω) ω ∂brownianCompletedMeasure) = 0 := by
  have h := brownianCompletedIntegralPath_stopped_setIntegral f hτ hbound MeasurableSet.univ
  simpa only [setIntegral_univ, brownianCompletedIntegralPath_mean] using h

theorem brownianCompletedIntegralPath_optionalSampling_two (f : BrownianIntegrand)
    {τ ν : BrownianCompletedSample → ℝ≥0} {T : ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (hν : IsStoppingTime brownianCompletedFiltration.rightCont (fun ω => (ν ω : WithTop ℝ≥0)))
    (hle : ∀ ω, τ ω ≤ ν ω) (hbound : ∀ ω, ν ω ≤ T) :
    brownianCompletedMeasure[(fun ω => brownianCompletedIntegralPath f (ν ω) ω) | hτ.measurableSpace]
      =ᵐ[brownianCompletedMeasure] (fun ω => brownianCompletedIntegralPath f (τ ω) ω) := by
  have hs : hτ.measurableSpace ≤ hν.measurableSpace := hτ.measurableSpace_mono hν (fun ω => by
    change (τ ω : WithTop ℝ≥0) ≤ (ν ω : WithTop ℝ≥0)
    exact_mod_cast hle ω)
  exact (condExp_congr_ae (brownianCompletedIntegralPath_optionalSampling f hν hbound).symm).trans
    ((condExp_condExp_of_le hs hν.measurableSpace_le).trans
      (brownianCompletedIntegralPath_optionalSampling f hτ (fun ω => (hle ω).trans (hbound ω))))

end TimeTraps.Probability
