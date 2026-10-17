module

public import TimeTraps.Probability.ReflectedBrownianQuadraticVariationTransfer
public import TimeTraps.Probability.BrownianQuadraticVariationUniform

@[expose] public section

/-! Actual reflected Brownian quadratic variation converges almost surely
uniformly over the entire compact time interval along stopped dyadic grids.
The limit is exactly sigma squared times time, or 2Dt in physical units.
A common event covers any chosen countable family of compact horizons. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

theorem affineBrownianFold_quadraticVariation_ae_uniform (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      TendstoUniformlyOn (stoppedDyadicPathQV (fun t => reflectedFold L (affineBrownianInput x σ t ω)) T)
        (fun s => σ ^ 2 * s.val) atTop (Icc 0 T) := by
  filter_upwards [affineBrownianFold_quadraticVariation_uniform_transfer_ae L hL x hσ,
    brownianStoppedDyadicPathQV_ae_uniform (brownianFoldSlopeGlobalPath_isBrownianReal L hL x hσ) T]
    with ω he hW
  exact he T (fun s => s.val) T.val hW (fun s hs => hs.2)

theorem foldedTrajectory_quadraticVariation_ae_uniform (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      TendstoUniformlyOn (fun n s =>
        brownianStoppedDyadicQV (foldedTrajectory L D x brownianDyadicPath) T n s ω)
        (fun s => 2 * D * s.val) atTop (Icc 0 T) := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (mul_pos (by norm_num) hD)
  have he := affineBrownianFold_quadraticVariation_ae_uniform L hL x hσ T
  rw [Real.sq_sqrt (mul_nonneg (by norm_num) hD.le)] at he
  exact he

theorem foldedTrajectory_quadraticVariation_countable_uniform_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℕ → ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ k : ℕ,
      TendstoUniformlyOn (fun n s =>
        brownianStoppedDyadicQV (foldedTrajectory L D x brownianDyadicPath) (T k) n s ω)
        (fun s => 2 * D * s.val) atTop (Icc 0 (T k)) :=
  ae_all_iff.mpr (fun k => foldedTrajectory_quadraticVariation_ae_uniform L hL D hD x (T k))

end TimeTraps.Probability
