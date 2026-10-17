module

public import TimeTraps.Probability.BrownianFoldUnitInterval

@[expose] public section

/-! Unit-coefficient sums on clipped dyadic grids converge in actual L²
to increments of the canonical fold-slope integral. The convergence follows
from the continuous linear time cutoff on the completed integrand domain.
This includes zero-length intervals and repeated clipped nodes. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianFoldUnitIntervalIntegrand_tendsto (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    Tendsto (fun n => brownianFoldUnitIntervalIntegrand hB.toIsPreBrownianReal hBm L hL x σ s t n)
      atTop (𝓝 (brownianFoldSlopeIntegrand hB.toIsPreBrownianReal hBm hjoint L hL x hσ t -
        brownianFoldSlopeIntegrand hB.toIsPreBrownianReal hBm hjoint L hL x hσ s)) := by
  have ht := brownianFoldUnitStepIntegrand_tendsto hB hBm hjoint L hL x hσ t
  have hc := (brownianTimeCutoff B hBm P s).continuous.continuousAt.tendsto.comp ht
  have hd := ht.sub hc
  simpa only [Function.comp_def, brownianFoldUnitIntervalIntegrand_eq, brownianFoldSlopeIntegrand_cutoff,
    min_eq_left hst] using hd

theorem brownianFoldUnitIntervalIntegral_tendsto (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    Tendsto (fun n => brownianIntegral hB.toIsPreBrownianReal
      (brownianFoldUnitIntervalIntegrand hB.toIsPreBrownianReal hBm L hL x σ s t n)) atTop
      (𝓝 (brownianFoldSlopeIntegral hB.toIsPreBrownianReal hBm hjoint L hL x hσ t -
        brownianFoldSlopeIntegral hB.toIsPreBrownianReal hBm hjoint L hL x hσ s)) := by
  have h := (brownianIntegral hB.toIsPreBrownianReal).continuous.continuousAt.tendsto.comp
    (brownianFoldUnitIntervalIntegrand_tendsto hB hBm hjoint L hL x hσ hst)
  simpa only [Function.comp_def, map_sub, brownianFoldSlopeIntegral] using h

theorem brownianDyadicFoldUnitIntervalIntegral_tendsto (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) {s t : ℝ≥0} (hst : s ≤ t) :
    Tendsto (fun n => brownianStochasticIntegral
      (brownianFoldUnitIntervalIntegrand brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
        L hL x σ s t n)) atTop
      (𝓝 (brownianDyadicFoldSlopeIntegral L hL x hσ t -
        brownianDyadicFoldSlopeIntegral L hL x hσ s)) :=
  brownianFoldUnitIntervalIntegral_tendsto brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable L hL x hσ hst

end TimeTraps.Probability
