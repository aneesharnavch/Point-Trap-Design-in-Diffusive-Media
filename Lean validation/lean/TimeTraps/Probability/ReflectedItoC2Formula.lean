module

public import TimeTraps.Probability.ReflectedItoC2Limit
public import TimeTraps.Probability.ReflectedC2ItoDriverSum

@[expose] public section

/-! The general reflected C² Itô formula for the actual folded Brownian
trajectory, its original-Brownian stochastic integral, and the actual
boundary regulators. No Neumann boundary condition is imposed. The
weighted driver sums, quadratic-variation limit, Stieltjes limits and
Taylor remainder are all supplied by proved constructions. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedItoC2_formula {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    (fun ω => F (foldedTrajectory L D x brownianDyadicPath T ω) - F (reflectedFold L x))
      =ᵐ[brownianDyadicMeasure] (fun ω =>
        reflectedC2ItoIntegral hF brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
          brownianDyadicPath_jointly_measurable L hL D hD x T ω +
        D * reflectedC2ItoDrift F brownianDyadicPath L D x T ω +
        deriv F 0 * affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L T ω -
        deriv F L * affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L T ω) := by
  exact reflectedItoC2_of_driver_limit hF L hL D hD x T
    (reflectedC2ItoDriverSumL2 hF L hL D hD x T)
    (reflectedC2ItoDriverSumL2_tendsto hF L hL D hD x T)
    (reflectedC2ItoDriverSumL2_ae hF L hL D hD x T)

end TimeTraps.Probability
