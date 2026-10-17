module

public import TimeTraps.Probability.BrownianQuadraticVariationAlmostSure
public import TimeTraps.Probability.ContinuousMonotoneQuadraticVariation
public import TimeTraps.Probability.ReflectedBrownianConstruction

@[expose] public section

/-! Actual squared-increment sums of the reflected path converge almost
surely along the entire dyadic sequence at each fixed horizon. The two
continuous monotone regulators have vanishing quadratic variation, so
the remaining limit is sigma squared times time, exactly 2 D t in the
physical normalization. Uniform-in-time convergence is a separate result. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

theorem affineBrownianFold_dyadicQV_ae_tendsto (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      Tendsto (fun n => brownianDyadicQV (fun t ω => reflectedFold L (affineBrownianInput x σ t ω)) T n ω)
        atTop (𝓝 (σ ^ 2 * T.val)) := by
  filter_upwards [affineBrownianFoldTanaka_global_ae L hL x hσ,
    reflectedFoldRegulatorPaths_ae x hσ hL,
    brownianDyadicQV_ae_tendsto (brownianFoldSlopeGlobalPath_isBrownianReal L hL x hσ).toIsPreBrownianReal T]
    with ω he hp hw
  have hw' : Tendsto (dyadicPathQV (fun t => brownianFoldSlopeGlobalPath L hL x hσ t ω) T)
      atTop (𝓝 T.val) := hw
  have ht := dyadicPathQV_affine_regulators_tendsto
    (fun t => brownianFoldSlopeGlobalPath L hL x hσ t ω)
    (fun t => affineBrownianLowerRegulator x σ L t ω)
    (fun t => affineBrownianUpperRegulator x σ L t ω)
    T σ (reflectedFold L x) T.val hw'
    hp.lower_continuous.continuousOn (hp.lower_monotone.monotoneOn (Set.Icc 0 T))
    hp.upper_continuous.continuousOn (hp.upper_monotone.monotoneOn (Set.Icc 0 T))
  have hpath : (fun t => reflectedFold L (affineBrownianInput x σ t ω)) =
      (fun t => reflectedFold L x + σ * brownianFoldSlopeGlobalPath L hL x hσ t ω +
        affineBrownianLowerRegulator x σ L t ω - affineBrownianUpperRegulator x σ L t ω) := funext he
  change Tendsto (dyadicPathQV (fun t => reflectedFold L (affineBrownianInput x σ t ω)) T)
    atTop (𝓝 (σ ^ 2 * T.val))
  rw [hpath]
  exact ht

theorem foldedTrajectory_dyadicQV_ae_tendsto (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      Tendsto (fun n => brownianDyadicQV (foldedTrajectory L D x brownianDyadicPath) T n ω)
        atTop (𝓝 (2 * D * T.val)) := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (mul_pos (by norm_num) hD)
  have he := affineBrownianFold_dyadicQV_ae_tendsto L hL x hσ T
  rw [Real.sq_sqrt (mul_nonneg (by norm_num) hD.le)] at he
  exact he

theorem foldedTrajectory_dyadicQV_countable_horizons_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℕ → ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ k : ℕ,
      Tendsto (fun n => brownianDyadicQV (foldedTrajectory L D x brownianDyadicPath) (T k) n ω)
        atTop (𝓝 (2 * D * (T k).val)) :=
  ae_all_iff.mpr (fun k => foldedTrajectory_dyadicQV_ae_tendsto L hL D hD x (T k))

end TimeTraps.Probability
