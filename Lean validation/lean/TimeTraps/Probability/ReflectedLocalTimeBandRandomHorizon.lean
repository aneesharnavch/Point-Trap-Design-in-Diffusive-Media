module

public import TimeTraps.Probability.ReflectedLocalTimeBandUniformLimit

@[expose] public section

/-! Genuine occupation bands at arbitrary measurable bounded random
times converge in mean square, by the simultaneous compact-time bound. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedOccupationBand_random_error_memLp (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) {h : ℝ}
    (hh : 0 < h) (hsmall : h < min (a.val / 2) ((L - a.val) / 2))
    (τ : (ℕ → ℝ) → ℝ≥0) (hτ : Measurable τ) (hτT : ∀ᵐ ω ∂brownianDyadicMeasure, τ ω ≤ T) :
    MemLp (fun ω => reflectedOccupationBand L D x a.val h (τ ω) ω -
      reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val (τ ω) ω)
      2 brownianDyadicMeasure := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  let q : (ℕ → ℝ) → ℝ≥0 × (ℕ → ℝ) := fun ω => (τ ω, ω)
  have hq : Measurable q := hτ.prodMk measurable_id
  have haM := (reflectedOccupationBand_jointlyMeasurable L D x a.val h).comp hq
  have hbM := (reflectedInteriorOccupationCoefficient_time_jointlyMeasurable x (Real.sqrt (2 * D)) L a.val).comp hq
  dsimp only [Function.comp_def, q] at haM hbM
  have hm := haM.sub hbM
  have hM : MemLp (fun ω => reflectedBandErrorAverage L hL x hσ T a h ω / (Real.sqrt (2 * D)) ^ 2)
      2 brownianDyadicMeasure := by
    simpa only [div_eq_mul_inv] using
      (reflectedBandErrorAverage_memLp L hL x hσ T a h).mul_const ((Real.sqrt (2 * D)) ^ 2)⁻¹
  apply hM.mono' hm.aestronglyMeasurable
  filter_upwards [reflectedOccupationBand_error_compact_ae L hL D hD x T a hh hsmall, hτT] with ω hb ht
  exact hb (τ ω) ht

theorem reflectedOccupationBand_random_error_secondMoment_le (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) {h : ℝ}
    (hh : 0 < h) (hsmall : h < min (a.val / 2) ((L - a.val) / 2))
    (τ : (ℕ → ℝ) → ℝ≥0) (hτ : Measurable τ) (hτT : ∀ᵐ ω ∂brownianDyadicMeasure, τ ω ≤ T) :
    (∫ ω, (reflectedOccupationBand L D x a.val h (τ ω) ω -
      reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val (τ ω) ω) ^ 2
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
        (reflectedOccupationBand_random_error_memLp L hL D hD x T a hh hsmall τ hτ hτT).integrable_sq hM.integrable_sq
      filter_upwards [reflectedOccupationBand_error_compact_ae L hL D hD x T a hh hsmall, hτT] with ω hb ht
      have he := hb (τ ω) ht
      have hs := (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans he)).mpr he
      simpa only [sq_abs] using hs
    _ = _ := by simp only [div_eq_mul_inv, mul_pow, inv_pow, integral_mul_const]

theorem reflectedOccupationBand_random_horizon_square_tendsto (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L)
    (τ : (ℕ → ℝ) → ℝ≥0) (hτ : Measurable τ) (hτT : ∀ᵐ ω ∂brownianDyadicMeasure, τ ω ≤ T) :
    Tendsto (fun h => ∫ ω, (reflectedOccupationBand L D x a.val h (τ ω) ω -
      reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val (τ ω) ω) ^ 2
      ∂brownianDyadicMeasure) (𝓝[>] 0) (𝓝 0) := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  apply squeeze_zero' (Eventually.of_forall (fun h => integral_nonneg (fun ω => sq_nonneg _)))
  · filter_upwards [reflectedOccupationBand_small_eventually L a] with h hh
    exact reflectedOccupationBand_random_error_secondMoment_le L hL D hD x T a hh.1 hh.2 τ hτ hτT
  · simpa only [zero_div] using
      (reflectedBandErrorAverage_square_tendsto L hL x hσ T a).div_const (((Real.sqrt (2 * D)) ^ 2) ^ 2)

end TimeTraps.Probability
