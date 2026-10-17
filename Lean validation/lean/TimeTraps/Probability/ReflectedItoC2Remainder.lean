module

public import TimeTraps.Probability.DyadicWeightedQuadraticVariationLimit
public import TimeTraps.Probability.ReflectedBrownianQuadraticVariationUniform
public import TimeTraps.Probability.BrownianItoC2Remainder

@[expose] public section

/-! Pathwise weighted quadratic variation and C2 Taylor remainder for
the actual reflected trajectory. Continuous curvature suffices: no
curvature Lipschitz bound, third derivative, or stochastic associativity
is assumed. These are approximation limits, not an Itô formula. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal Topology

theorem foldedTrajectory_weightedQV_ae_tendsto (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc 0 L)) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      Tendsto (dyadicWeightedPathQV
        (fun t => foldedTrajectory L D x brownianDyadicPath t ω)
        (fun t => g (foldedTrajectory L D x brownianDyadicPath t ω)) T)
        atTop (𝓝 (2 * D * ∫ r in (0 : ℝ)..T.val,
          g (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω))) := by
  filter_upwards [brownianDyadicPath_isBrownianReal.cont,
    foldedTrajectory_quadraticVariation_ae_uniform L hL D hD x T] with ω hc hq
  have hpath : Continuous (fun t => foldedTrajectory L D x brownianDyadicPath t ω) :=
    (reflectedFold_continuous L).comp (continuous_const.add (continuous_const.mul hc))
  have hw : ContinuousOn (fun t => g (foldedTrajectory L D x brownianDyadicPath t ω)) (Icc 0 T) :=
    hg.comp hpath.continuousOn (fun t _ => foldedTrajectory_mem L hL D x brownianDyadicPath t ω)
  exact dyadicWeightedPathQV_tendsto _ _ T hpath.continuousOn hw (2 * D) hq

theorem reflectedItoC2_curvatureQV_ae_tendsto {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      Tendsto (dyadicWeightedPathQV
        (fun t => foldedTrajectory L D x brownianDyadicPath t ω)
        (fun t => deriv (deriv F) (foldedTrajectory L D x brownianDyadicPath t ω)) T)
        atTop (𝓝 (2 * D * ∫ r in (0 : ℝ)..T.val,
          deriv (deriv F) (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω))) :=
  foldedTrajectory_weightedQV_ae_tendsto L hL D hD x T _
    (itoC2_secondDerivative_continuous hF).continuousOn

theorem reflectedItoTaylorDyadic_c2_ae_tendsto {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      Tendsto (fun n : ℕ => brownianItoTaylorSum (Ω := ℕ → ℝ)
        (foldedTrajectory L D x brownianDyadicPath) F (N := 2 ^ n)
        (brownianDyadicGrid T n) ω) atTop (𝓝 0) := by
  filter_upwards [brownianDyadicPath_isBrownianReal.cont,
    foldedTrajectory_quadraticVariation_ae_uniform L hL D hD x T] with ω hc hq
  have hpath : Continuous (fun t => foldedTrajectory L D x brownianDyadicPath t ω) :=
    (reflectedFold_continuous L).comp (continuous_const.add (continuous_const.mul hc))
  have hq' : TendstoUniformlyOn
      (stoppedDyadicPathQV (fun t => foldedTrajectory L D x brownianDyadicPath t ω) T)
      (fun s => 2 * D * s.val) atTop (Icc 0 T) := hq
  have ht : Tendsto (dyadicPathQV (fun t => foldedTrajectory L D x brownianDyadicPath t ω) T)
      atTop (𝓝 (2 * D * T.val)) := by
    simpa only [stoppedDyadicPathQV_terminal] using
      hq'.tendsto_at (show T ∈ Icc 0 T from ⟨zero_le, le_rfl⟩)
  exact dyadicItoTaylorSum_c2_tendsto hF
    (fun t => foldedTrajectory L D x brownianDyadicPath t ω) T hpath.continuousOn ht

end TimeTraps.Probability
