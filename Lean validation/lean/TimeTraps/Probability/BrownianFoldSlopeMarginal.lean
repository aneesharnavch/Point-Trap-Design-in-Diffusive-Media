module

public import TimeTraps.Analysis.L2LawLimit
public import TimeTraps.Probability.BrownianPredictableSignLaw
public import TimeTraps.Probability.BrownianFoldUnitConvergence
public import TimeTraps.Probability.BrownianFoldSlopeGlobal

@[expose] public section

/-! The actual normalized fold integral has centered Gaussian law with
variance t at each fixed time. Finite predictable unit-sign sums have the
exact same law, and convergence in actual L2 transfers that law to the
canonical integral and its continuous version. Joint laws and independent
increments are separate obligations. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianFoldUnitStepIntegral_hasLaw (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (x σ : ℝ)
    (t : ℝ≥0) (n : ℕ) :
    HasLaw (brownianIntegral hB (brownianFoldUnitStepIntegrand hB hBm L hL x σ t n))
      (gaussianReal 0 t) P := by
  have hs := brownian_predictable_sign_hasLaw hB hBm (brownianDyadicGrid t n)
    (brownianDyadicGrid_monotone t n) (brownianFoldUnitCoefficient B L x σ t n)
    (brownianFoldUnitCoefficient_adapted hBm L hL x σ t n)
    (fun i => Filter.Eventually.of_forall (brownianFoldUnitCoefficient_abs B L hL x σ t n i))
  rw [brownianDyadicGrid_last, brownianDyadicGrid_zero, tsub_zero] at hs
  exact hs.congr (brownianFoldUnitStep_integral_ae hB hBm L hL x σ t n)

theorem brownianFoldSlopeIntegral_hasLaw (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (t : ℝ≥0) :
    HasLaw (brownianFoldSlopeIntegral hB.toIsPreBrownianReal hBm hjoint L hL x hσ t)
      (gaussianReal 0 t) P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact real_L2_hasLaw_of_tendsto
    (fun n => brownianIntegral hB.toIsPreBrownianReal
      (brownianFoldUnitStepIntegrand hB.toIsPreBrownianReal hBm L hL x σ t n))
    (brownianFoldSlopeIntegral hB.toIsPreBrownianReal hBm hjoint L hL x hσ t)
    (gaussianReal 0 t) (brownianFoldUnitStepIntegral_tendsto hB hBm hjoint L hL x hσ t)
    (fun n => brownianFoldUnitStepIntegral_hasLaw hB.toIsPreBrownianReal hBm L hL x σ t n)

theorem brownianFoldSlopeGlobalPath_hasLaw (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (t : ℝ≥0) :
    HasLaw (brownianFoldSlopeGlobalPath L hL x hσ t) (gaussianReal 0 t) brownianDyadicMeasure := by
  have hl : HasLaw (brownianDyadicFoldSlopeIntegral L hL x hσ t)
      (gaussianReal 0 t) brownianDyadicMeasure :=
    brownianFoldSlopeIntegral_hasLaw brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
      brownianDyadicPath_jointly_measurable L hL x hσ t
  exact hl.congr (brownianFoldSlopeGlobalPath_integral_ae L hL x hσ t)

end TimeTraps.Probability
