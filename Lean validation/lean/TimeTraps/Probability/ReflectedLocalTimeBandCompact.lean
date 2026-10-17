module

public import TimeTraps.Probability.ReflectedLocalTimeBandCompactData
public import TimeTraps.Probability.ReflectedLocalTimeBandUniformBound

@[expose] public section

/-! Square-integrability and a second-moment bound for the literal
supremum of the genuine occupation-band error on a compact horizon. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedBandErrorCompactPath_bound_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) {h : ℝ}
    (hh : 0 < h) (hsmall : h < min (a.val / 2) ((L - a.val) / 2)) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ‖reflectedBandErrorCompactPath L hL D hD x a.val h T ω‖ ≤
      reflectedBandErrorAverage L hL x (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) T a h ω /
        (Real.sqrt (2 * D)) ^ 2 := by
  filter_upwards [reflectedOccupationBand_error_compact_ae L hL D hD x T a hh hsmall,
    reflectedInteriorLocalTimeRegular_ae x (Real.sqrt (2 * D)) L a.val] with ω hb hr
  apply (reflectedBandErrorCompactPath L hL D hD x a.val h T ω).norm_le_of_nonempty.mpr
  intro t
  rw [reflectedBandErrorCompactPath_apply L hL D hD x a.val h T hr, Real.norm_eq_abs]
  exact hb t.val t.property.2

theorem reflectedBandErrorCompactPath_memLp (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) {h : ℝ}
    (hh : 0 < h) (hsmall : h < min (a.val / 2) ((L - a.val) / 2)) :
    MemLp (reflectedBandErrorCompactPath L hL D hD x a.val h T) 2 brownianDyadicMeasure := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  have hM : MemLp (fun ω => reflectedBandErrorAverage L hL x hσ T a h ω / (Real.sqrt (2 * D)) ^ 2)
      2 brownianDyadicMeasure := by
    simpa only [div_eq_mul_inv] using
      (reflectedBandErrorAverage_memLp L hL x hσ T a h).mul_const ((Real.sqrt (2 * D)) ^ 2)⁻¹
  exact hM.mono' (reflectedBandErrorCompactPath_stronglyMeasurable L hL D hD x a.val h T).aestronglyMeasurable
    (reflectedBandErrorCompactPath_bound_ae L hL D hD x T a hh hsmall)

theorem reflectedOccupationBand_sup_error_memLp (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) {h : ℝ}
    (hh : 0 < h) (hsmall : h < min (a.val / 2) ((L - a.val) / 2)) :
    MemLp (fun ω => ⨆ t : BrownianCompactTime T,
      |reflectedOccupationBand L D x a.val h t.val ω -
        reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t.val ω|)
      2 brownianDyadicMeasure :=
  MemLp.ae_eq (reflectedBandErrorCompactPath_norm_ae L hL D hD x a.val h T)
    (reflectedBandErrorCompactPath_memLp L hL D hD x T a hh hsmall).norm

theorem reflectedOccupationBand_sup_error_secondMoment_le (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) {h : ℝ}
    (hh : 0 < h) (hsmall : h < min (a.val / 2) ((L - a.val) / 2)) :
    (∫ ω, (⨆ t : BrownianCompactTime T,
      |reflectedOccupationBand L D x a.val h t.val ω -
        reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t.val ω|) ^ 2
      ∂brownianDyadicMeasure) ≤
    (∫ ω, reflectedBandErrorAverage L hL x (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) T a h ω ^ 2
      ∂brownianDyadicMeasure) / ((Real.sqrt (2 * D)) ^ 2) ^ 2 := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  have hM : MemLp (fun ω => reflectedBandErrorAverage L hL x hσ T a h ω / (Real.sqrt (2 * D)) ^ 2)
      2 brownianDyadicMeasure := by
    simpa only [div_eq_mul_inv] using
      (reflectedBandErrorAverage_memLp L hL x hσ T a h).mul_const ((Real.sqrt (2 * D)) ^ 2)⁻¹
  calc
    _ ≤ ∫ ω, (reflectedBandErrorAverage L hL x hσ T a h ω / (Real.sqrt (2 * D)) ^ 2) ^ 2
        ∂brownianDyadicMeasure := by
      apply integral_mono_ae
        (reflectedOccupationBand_sup_error_memLp L hL D hD x T a hh hsmall).integrable_sq hM.integrable_sq
      filter_upwards [reflectedBandErrorCompactPath_norm_ae L hL D hD x a.val h T,
        reflectedBandErrorCompactPath_bound_ae L hL D hD x T a hh hsmall] with ω he hb
      rw [← he]
      exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hb)).mpr hb
    _ = _ := by simp only [div_eq_mul_inv, mul_pow, inv_pow, integral_mul_const]

end TimeTraps.Probability
