module

public import TimeTraps.Probability.ReflectedLocalTimeBandSpatialBound
public import TimeTraps.Probability.ReflectedLocalTimeBandErrorAverage
public import TimeTraps.Probability.ReflectedLocalTimeBandAverageEstimate

@[expose] public section

/-! The genuine occupation-band error is bounded by the averaged maximal
error simultaneously at every time in a compact interval. Product
integration is performed first at fixed times, then a countable dense
time set and actual path continuity give the common event. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis TopologicalSpace
open scoped NNReal ENNReal Topology

theorem reflectedOccupationBand_error_fixed_time_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) {h : ℝ}
    (hh : 0 < h) (hsmall : h < min (a.val / 2) ((L - a.val) / 2)) (t : ℝ≥0) (ht : t ≤ T) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      |reflectedOccupationBand L D x a.val h t ω -
        reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t ω| ≤
      reflectedBandErrorAverage L hL x (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) T a h ω /
        (Real.sqrt (2 * D)) ^ 2 := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  filter_upwards [reflectedOccupationBand_spatial_average_ae L hL D hD x a.val,
    reflectedBandErrorVersion_spatial_integrable_ae L hL x hσ T a h,
    reflectedOccupationDensity_band_spatial_bound_ae L hL D hD x T a hsmall t ht] with ω hF hE hb
  rw [(hF t h).2]
  exact reflectedBandAverage_error_bound a.val
    (reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t ω)
    ((Real.sqrt (2 * D)) ^ 2) hh (hF t h).1 hE hb

theorem reflectedOccupationBand_error_compact_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) {h : ℝ}
    (hh : 0 < h) (hsmall : h < min (a.val / 2) ((L - a.val) / 2)) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0, t ≤ T →
      |reflectedOccupationBand L D x a.val h t ω -
        reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t ω| ≤
      reflectedBandErrorAverage L hL x (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) T a h ω /
        (Real.sqrt (2 * D)) ^ 2 := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  have hd : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ n : ℕ,
      |reflectedOccupationBand L D x a.val h (denseSeq (BrownianCompactTime T) n).val ω -
        reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val
          (denseSeq (BrownianCompactTime T) n).val ω| ≤
      reflectedBandErrorAverage L hL x hσ T a h ω / (Real.sqrt (2 * D)) ^ 2 :=
    ae_all_iff.mpr (fun n => reflectedOccupationBand_error_fixed_time_ae L hL D hD x T a hh hsmall
      (denseSeq (BrownianCompactTime T) n).val (denseSeq (BrownianCompactTime T) n).property.2)
  filter_upwards [hd, reflectedInteriorLocalTimeRegular_ae x (Real.sqrt (2 * D)) L a.val] with ω hω hr
  have hc : Continuous (fun t : ℝ≥0 => reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t ω) :=
    (reflectedInteriorCorrection_continuous hσ hL hr).div_const _
  have hb : Continuous (fun t : BrownianCompactTime T =>
      |reflectedOccupationBand L D x a.val h t.val ω -
        reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t.val ω|) :=
    ((reflectedOccupationBand_continuous L D x a.val h ω).sub hc).abs.comp continuous_subtype_val
  let p : BrownianCompactTime T → Prop := fun t =>
    |reflectedOccupationBand L D x a.val h t.val ω -
      reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t.val ω| ≤
    reflectedBandErrorAverage L hL x hσ T a h ω / (Real.sqrt (2 * D)) ^ 2
  have hp : IsClosed {t | p t} := isClosed_le hb continuous_const
  have hdense : ∀ n, p (denseSeq (BrownianCompactTime T) n) := hω
  intro t ht
  exact (denseRange_denseSeq (BrownianCompactTime T)).induction_on (p := p)
    ⟨t, zero_le, ht⟩ hp hdense

end TimeTraps.Probability
