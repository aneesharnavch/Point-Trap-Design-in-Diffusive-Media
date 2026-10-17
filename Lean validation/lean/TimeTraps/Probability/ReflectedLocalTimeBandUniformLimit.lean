module

public import TimeTraps.Probability.ReflectedLocalTimeBandCompact
public import TimeTraps.Probability.ReflectedLocalTimeBandErrorLimit

@[expose] public section

/-! Uniform-in-time mean-square convergence of the genuine reflected
occupation bands to the fixed-site local time. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedOccupationBand_small_eventually (L : ℝ) (a : Ioo (0 : ℝ) L) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h ∧ h < min (a.val / 2) ((L - a.val) / 2) := by
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (reflectedBandWindow_radius_pos a))] with h hh hs
  exact ⟨hh, hs⟩

theorem reflectedOccupationBand_uniform_square_tendsto (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) :
    Tendsto (fun h => ∫ ω, (⨆ t : BrownianCompactTime T,
      |reflectedOccupationBand L D x a.val h t.val ω -
        reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t.val ω|) ^ 2
      ∂brownianDyadicMeasure) (𝓝[>] 0) (𝓝 0) := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  apply squeeze_zero' (Eventually.of_forall (fun h => integral_nonneg (fun ω => sq_nonneg _)))
  · filter_upwards [reflectedOccupationBand_small_eventually L a] with h hh
    exact reflectedOccupationBand_sup_error_secondMoment_le L hL D hD x T a hh.1 hh.2
  · simpa only [zero_div] using
      (reflectedBandErrorAverage_square_tendsto L hL x hσ T a).div_const (((Real.sqrt (2 * D)) ^ 2) ^ 2)

end TimeTraps.Probability
