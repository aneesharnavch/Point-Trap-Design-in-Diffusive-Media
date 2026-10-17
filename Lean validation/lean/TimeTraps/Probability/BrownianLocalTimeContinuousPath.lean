module

public import TimeTraps.Probability.BrownianSignIntegralContinuous
public import TimeTraps.Probability.BrownianTanakaCompensation

@[expose] public section

/-! The literal finite-horizon Tanaka candidate, formed from the original
Brownian process and the continuous sign-integral version. Its paths are
continuous almost surely and, at each fixed time in the horizon, it is
the previously constructed L² compensation. No occupation identity or
support property is asserted by this definition. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

def brownianLocalTimeCandidate (a : ℝ) (T t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  |brownianDyadicPath t ω - a| - |brownianDyadicPath 0 ω - a| -
    brownianSignIntegralPath a T t ω

theorem brownianLocalTimeCandidate_continuous (a : ℝ) (T : ℝ≥0) {ω : ℕ → ℝ}
    (hω : Continuous (fun t => brownianDyadicPath t ω)) :
    Continuous (fun t => brownianLocalTimeCandidate a T t ω) :=
  ((hω.sub continuous_const).abs.sub continuous_const).sub
    (brownianSignIntegralPath_continuous a T ω)

theorem brownianLocalTimeCandidate_continuous_ae (a : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, Continuous (fun t => brownianLocalTimeCandidate a T t ω) :=
  brownianDyadicPath_continuous_ae.mono (fun _ hω => brownianLocalTimeCandidate_continuous a T hω)

theorem brownianLocalTimeCandidate_jointlyMeasurable (a : ℝ) (T : ℝ≥0) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => brownianLocalTimeCandidate a T p.1 p.2) :=
  ((brownianDyadicPath_jointly_measurable.sub_const a).abs.sub
    (((brownianDyadicPath_measurable 0).comp measurable_snd).sub_const a).abs).sub
      (brownianSignIntegralPath_jointlyMeasurable a T)

theorem brownianLocalTimeCandidate_compensation_ae (a : ℝ) {T t : ℝ≥0} (ht : t ≤ T) :
    brownianLocalTimeCandidate a T t =ᵐ[brownianDyadicMeasure]
      brownianTanakaCompensation brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
        brownianDyadicPath_jointly_measurable a t := by
  filter_upwards [brownianSignIntegralPath_integral_ae_of_le a ht,
    brownianTanakaCompensation_coe brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
      brownianDyadicPath_jointly_measurable a t] with ω hs hc
  rw [hc]
  change _ - brownianSignIntegralPath a T t ω = _
  rw [hs]
  rfl

theorem brownianLocalTimeCandidate_memLp (a : ℝ) {T t : ℝ≥0} (ht : t ≤ T) :
    MemLp (brownianLocalTimeCandidate a T t) 2 brownianDyadicMeasure :=
  (Lp.memLp (brownianTanakaCompensation brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable a t)).ae_eq
      (brownianLocalTimeCandidate_compensation_ae a ht).symm

theorem brownianLocalTimeCandidate_raw_aestronglyMeasurable (a : ℝ) (T t : ℝ≥0) :
    AEStronglyMeasurable[brownianFiltration t] (brownianLocalTimeCandidate a T t)
      brownianDyadicMeasure := by
  have ht := brownianFiltration_stronglyAdapted t
  have h₀ : StronglyMeasurable[brownianFiltration t] (brownianDyadicPath 0) :=
    (brownianFiltration_stronglyAdapted 0).mono (brownianFiltration.mono (zero_le : (0 : ℝ≥0) ≤ t))
  exact (((ht.sub stronglyMeasurable_const).norm.sub
    (h₀.sub stronglyMeasurable_const).norm).aestronglyMeasurable).sub
      (brownianSignIntegralPath_raw_aestronglyMeasurable a T t)

end TimeTraps.Probability

end
