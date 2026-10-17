module

public import TimeTraps.Probability.ReflectedItoFiniteDecomposition
public import TimeTraps.Probability.ReflectedItoC2Remainder
public import TimeTraps.Probability.ReflectedC2ItoIntegrandPath
public import TimeTraps.Probability.ReflectedC2ItoDrift
public import TimeTraps.Probability.BrownianItoPathwiseLimit

@[expose] public section

/-! Assembly of the reflected C² Taylor limits. The stochastic input
is explicitly an L² sequence representing the actual weighted driver
sums and converging to the actual original-Brownian integral. All other
limits are derived from the reflected trajectory and its regulators. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedItoC2_of_driver_limit {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0)
    (S : ℕ → Lp ℝ 2 brownianDyadicMeasure)
    (hS : Tendsto S atTop (𝓝 (reflectedC2ItoIntegral hF brownianDyadicPath_isBrownianReal
      brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL D hD x T)))
    (hrep : ∀ n, S n =ᵐ[brownianDyadicMeasure]
      affineBrownianFoldDriverWeightedSum L hL x
        (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) (deriv F) T n) :
    (fun ω => F (foldedTrajectory L D x brownianDyadicPath T ω) - F (reflectedFold L x))
      =ᵐ[brownianDyadicMeasure] (fun ω =>
        reflectedC2ItoIntegral hF brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
          brownianDyadicPath_jointly_measurable L hL D hD x T ω +
        D * reflectedC2ItoDrift F brownianDyadicPath L D x T ω +
        deriv F 0 * affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L T ω -
        deriv F L * affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L T ω) := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  let R (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
    affineBrownianRegulatorWeightedSum x (Real.sqrt (2 * D)) L 0 (deriv F) T n ω -
      affineBrownianRegulatorWeightedSum x (Real.sqrt (2 * D)) L 1 (deriv F) T n ω +
      (1 / 2 : ℝ) * dyadicWeightedPathQV
        (fun t => foldedTrajectory L D x brownianDyadicPath t ω)
        (fun t => deriv (deriv F) (foldedTrajectory L D x brownianDyadicPath t ω)) T n +
      brownianItoTaylorSum (Ω := ℕ → ℝ) (foldedTrajectory L D x brownianDyadicPath) F
        (N := 2 ^ n) (brownianDyadicGrid T n) ω
  let r (ω : ℕ → ℝ) : ℝ :=
    deriv F 0 * affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L T ω -
      deriv F L * affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L T ω +
      D * reflectedC2ItoDrift F brownianDyadicPath L D x T ω
  have hR : ∀ᵐ ω ∂brownianDyadicMeasure, Tendsto (fun n => R n ω) atTop (𝓝 (r ω)) := by
    filter_upwards [affineBrownianRegulatorWeightedSum_boundary_ae x hσ hL (deriv F)
      (hF.continuous_deriv (by norm_num)) T,
      reflectedItoC2_curvatureQV_ae_tendsto hF L hL D hD x T,
      reflectedItoTaylorDyadic_c2_ae_tendsto hF L hL D hD x T] with ω hK hQ hrem
    have hc := ((hK.1.sub hK.2).add (hQ.const_mul (1 / 2 : ℝ))).add hrem
    convert hc using 1
    dsimp only [r, reflectedC2ItoDrift]
    ring_nf
  have hH (n : ℕ) : (fun ω => F (foldedTrajectory L D x brownianDyadicPath T ω) -
      F (reflectedFold L x)) =ᵐ[brownianDyadicMeasure] (fun ω => S n ω + R n ω) := by
    filter_upwards [hrep n, affineBrownianFold_finite_taylor_ae L hL x hσ] with ω hs ht
    have he := ht F T n
    rw [← hs] at he
    change F (foldedTrajectory L D x brownianDyadicPath T ω) - F (reflectedFold L x) =
      S n ω + affineBrownianRegulatorWeightedSum x (Real.sqrt (2 * D)) L 0 (deriv F) T n ω -
      affineBrownianRegulatorWeightedSum x (Real.sqrt (2 * D)) L 1 (deriv F) T n ω +
      (1 / 2 : ℝ) * dyadicWeightedPathQV
        (fun t => foldedTrajectory L D x brownianDyadicPath t ω)
        (fun t => deriv (deriv F) (foldedTrajectory L D x brownianDyadicPath t ω)) T n +
      brownianItoTaylorSum (Ω := ℕ → ℝ) (foldedTrajectory L D x brownianDyadicPath) F
        (N := 2 ^ n) (brownianDyadicGrid T n) ω at he
    dsimp only [R]
    linarith
  have he := ae_eq_lp_limit_of_pathwise_remainder S
    (reflectedC2ItoIntegral hF brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
      brownianDyadicPath_jointly_measurable L hL D hD x T) R r
    (fun ω => F (foldedTrajectory L D x brownianDyadicPath T ω) - F (reflectedFold L x)) hS hR hH
  filter_upwards [he] with ω hω
  rw [hω]
  dsimp only [r]
  ring

end TimeTraps.Probability
