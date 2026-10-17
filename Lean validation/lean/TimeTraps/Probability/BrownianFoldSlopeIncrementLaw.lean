module

public import TimeTraps.Probability.BrownianFoldSlopeMarginal
public import TimeTraps.Probability.BrownianFoldUnitIntervalConvergence

@[expose] public section

/-! Actual fold-integral increments have centered Gaussian law with variance
t-s. Clipping the unit-coefficient grid at s preserves adaptedness and its
exact finite Gaussian law. Actual L2 convergence passes this law to the
canonical increment, including s=t, and then to the continuous version. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianFoldUnitIntervalIntegral_hasLaw (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (x σ : ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) (n : ℕ) :
    HasLaw (brownianIntegral hB (brownianFoldUnitIntervalIntegrand hB hBm L hL x σ s t n))
      (gaussianReal 0 (t - s)) P := by
  have hs := brownian_predictable_sign_hasLaw hB hBm (brownianFoldUnitIntervalGrid s t n)
    (brownianFoldUnitIntervalGrid_monotone s t n) (brownianFoldUnitCoefficient B L x σ t n)
    (brownianFoldUnitIntervalCoefficient_adapted hBm L hL x σ s t n)
    (fun i => Filter.Eventually.of_forall (brownianFoldUnitCoefficient_abs B L hL x σ t n i))
  rw [brownianFoldUnitIntervalGrid_last hst, brownianFoldUnitIntervalGrid_zero] at hs
  exact hs.congr (brownianFoldUnitInterval_integral_ae hB hBm L hL x σ s t n)

theorem brownianFoldSlopeIntegral_increment_hasLaw (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (brownianFoldSlopeIntegral hB.toIsPreBrownianReal hBm hjoint L hL x hσ t -
      brownianFoldSlopeIntegral hB.toIsPreBrownianReal hBm hjoint L hL x hσ s)
      (gaussianReal 0 (t - s)) P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact real_L2_hasLaw_of_tendsto
    (fun n => brownianIntegral hB.toIsPreBrownianReal
      (brownianFoldUnitIntervalIntegrand hB.toIsPreBrownianReal hBm L hL x σ s t n))
    (brownianFoldSlopeIntegral hB.toIsPreBrownianReal hBm hjoint L hL x hσ t -
      brownianFoldSlopeIntegral hB.toIsPreBrownianReal hBm hjoint L hL x hσ s)
    (gaussianReal 0 (t - s)) (brownianFoldUnitIntervalIntegral_tendsto hB hBm hjoint L hL x hσ hst)
    (fun n => brownianFoldUnitIntervalIntegral_hasLaw hB.toIsPreBrownianReal hBm L hL x σ hst n)

theorem brownianFoldSlopeGlobalPath_increment_hasLaw (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω => brownianFoldSlopeGlobalPath L hL x hσ t ω -
      brownianFoldSlopeGlobalPath L hL x hσ s ω) (gaussianReal 0 (t - s)) brownianDyadicMeasure := by
  have hl : HasLaw (brownianDyadicFoldSlopeIntegral L hL x hσ t -
      brownianDyadicFoldSlopeIntegral L hL x hσ s) (gaussianReal 0 (t - s)) brownianDyadicMeasure :=
    brownianFoldSlopeIntegral_increment_hasLaw brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
      brownianDyadicPath_jointly_measurable L hL x hσ hst
  apply hl.congr
  filter_upwards [brownianFoldSlopeGlobalPath_integral_ae L hL x hσ t,
    brownianFoldSlopeGlobalPath_integral_ae L hL x hσ s,
    Lp.coeFn_sub (brownianDyadicFoldSlopeIntegral L hL x hσ t)
      (brownianDyadicFoldSlopeIntegral L hL x hσ s)] with ω ht hs hd
  rw [ht, hs, hd, Pi.sub_apply]

end TimeTraps.Probability
