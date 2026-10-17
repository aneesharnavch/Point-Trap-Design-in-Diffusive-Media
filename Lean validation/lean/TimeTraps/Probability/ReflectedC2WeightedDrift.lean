module

public import TimeTraps.Probability.DyadicTimePrimitiveIntegral
public import TimeTraps.Probability.ReflectedC2ItoDrift

@[expose] public section

/-! Weighted increments of the actual reflected curvature drift. The
pathwise result only uses continuity of the folded path and the C² base.
For the constructed Brownian motion, one path-continuity event works for
every continuous weight and every horizon. No bound or adaptation of
the weight is required for this deterministic drift limit. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

theorem reflectedC2ItoDrift_weighted_tendsto {Ω : Type*} {B : ℝ≥0 → Ω → ℝ}
    {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (L D x : ℝ) (ω : Ω)
    (hpath : Continuous (fun t => foldedTrajectory L D x B t ω))
    (H : ℝ≥0 → ℝ) (hH : Continuous H) (T : ℝ≥0) :
    Tendsto (fun n => dyadicWeightedIncrement H (fun t => reflectedC2ItoDrift F B L D x t ω) T n)
      atTop (𝓝 (∫ r in (0 : ℝ)..T.val,
        H r.toNNReal * deriv (deriv F) (foldedTrajectory L D x B r.toNNReal ω))) := by
  have hc : Continuous (deriv (deriv F)) :=
    (show ContDiff ℝ 1 (deriv F) from hF.deriv').continuous_deriv (by norm_num)
  exact dyadicWeightedIncrement_timePrimitive_tendsto H
    (fun t => deriv (deriv F) (foldedTrajectory L D x B t ω)) hH (hc.comp hpath) T

theorem reflectedC2ItoDrift_weighted_all_ae {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L D x : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ H : ℝ≥0 → ℝ, Continuous H → ∀ T : ℝ≥0,
      Tendsto (fun n => dyadicWeightedIncrement H
        (fun t => reflectedC2ItoDrift F brownianDyadicPath L D x t ω) T n) atTop
        (𝓝 (∫ r in (0 : ℝ)..T.val,
          H r.toNNReal * deriv (deriv F)
            (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω))) := by
  filter_upwards [brownianDyadicPath_isBrownianReal.cont] with ω hω
  intro H hH T
  exact reflectedC2ItoDrift_weighted_tendsto hF L D x ω
    ((reflectedFold_continuous L).comp (continuous_const.add (continuous_const.mul hω))) H hH T

end TimeTraps.Probability
