module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentRegulator
public import TimeTraps.Probability.ReflectedInteriorOccupationMeasurable

@[expose] public section

/-! A uniform levelwise second-moment estimate for the genuine periodized
occupation coefficient and the folded occupation density. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedInteriorCorrection_secondMoment_uniform_bound (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x a : ℝ) (T : ℝ≥0) :
    (∫ ω, reflectedInteriorCorrection x (Real.sqrt (2 * D)) L a T ω ^ 2 ∂brownianDyadicMeasure) ≤
      4 * (3 * L ^ 2 + 6 * D * T.val + 3 * (D * T.val / L) ^ 2) := by
  let K₁ := affineBrownianLowerRegulator (x - a) (Real.sqrt (2 * D)) L T
  let K₂ := affineBrownianLowerRegulator (x + a) (Real.sqrt (2 * D)) L T
  have h₁ : Integrable (fun ω => K₁ ω ^ 2) brownianDyadicMeasure :=
    (reflectedLowerRegulator_memLp L hL D hD (x - a) T).integrable_sq
  have h₂ : Integrable (fun ω => K₂ ω ^ 2) brownianDyadicMeasure :=
    (reflectedLowerRegulator_memLp L hL D hD (x + a) T).integrable_sq
  have hb : (∫ ω, reflectedInteriorCorrection x (Real.sqrt (2 * D)) L a T ω ^ 2 ∂brownianDyadicMeasure) ≤
      ∫ ω, 2 * (K₁ ω ^ 2 + K₂ ω ^ 2) ∂brownianDyadicMeasure := by
    apply integral_mono (reflectedInteriorCorrection_memLp L hL D hD x a T).integrable_sq ((h₁.add h₂).const_mul 2)
    intro ω
    change (K₁ ω + K₂ ω) ^ 2 ≤ 2 * (K₁ ω ^ 2 + K₂ ω ^ 2)
    nlinarith [sq_nonneg (K₁ ω - K₂ ω)]
  rw [integral_const_mul, integral_add h₁ h₂] at hb
  have hb₁ := reflectedLowerRegulator_secondMoment_uniform_bound L hL D hD (x - a) T
  have hb₂ := reflectedLowerRegulator_secondMoment_uniform_bound L hL D hD (x + a) T
  change (∫ ω, K₁ ω ^ 2 ∂brownianDyadicMeasure) ≤ _ at hb₁
  change (∫ ω, K₂ ω ^ 2 ∂brownianDyadicMeasure) ≤ _ at hb₂
  linarith

theorem reflectedInteriorOccupationCoefficient_secondMoment_uniform_bound (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x a : ℝ) (T : ℝ≥0) :
    (∫ ω, reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a T ω ^ 2 ∂brownianDyadicMeasure) ≤
      (3 * L ^ 2 + 6 * D * T.val + 3 * (D * T.val / L) ^ 2) / D ^ 2 := by
  have hs : (Real.sqrt (2 * D)) ^ 2 = 2 * D := Real.sq_sqrt (by positivity)
  simp only [reflectedInteriorOccupationCoefficient, hs, div_pow, integral_div]
  calc
    _ ≤ (4 * (3 * L ^ 2 + 6 * D * T.val + 3 * (D * T.val / L) ^ 2)) / (2 * D) ^ 2 :=
      div_le_div_of_nonneg_right (reflectedInteriorCorrection_secondMoment_uniform_bound L hL D hD x a T) (sq_nonneg _)
    _ = _ := by field_simp; ring

theorem foldedOccupationDensity_level_memLp_all (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x a : ℝ) (T : ℝ≥0) :
    MemLp (fun ω => foldedOccupationDensity L D x T ω a) 2 brownianDyadicMeasure := by
  by_cases ha : a ∈ Ioo 0 L
  · exact foldedOccupationDensity_level_memLp L hL D hD x a ha T
  · simpa only [foldedOccupationDensity, foldedOccupationDensityENNReal,
      indicator_of_notMem ha, ENNReal.toReal_zero] using
      (memLp_const (μ := brownianDyadicMeasure) (p := 2) (0 : ℝ))

theorem foldedOccupationDensity_level_secondMoment_uniform_bound (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x a : ℝ) (T : ℝ≥0) :
    (∫ ω, foldedOccupationDensity L D x T ω a ^ 2 ∂brownianDyadicMeasure) ≤
      (3 * L ^ 2 + 6 * D * T.val + 3 * (D * T.val / L) ^ 2) / D ^ 2 := by
  by_cases ha : a ∈ Ioo 0 L
  · calc
      _ = ∫ ω, reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a T ω ^ 2 ∂brownianDyadicMeasure := by
        apply integral_congr_ae
        filter_upwards [reflectedInteriorOccupationCoefficient_density_all_times_ae L hL D hD x a ha] with ω hω
        rw [hω T]
      _ ≤ _ := reflectedInteriorOccupationCoefficient_secondMoment_uniform_bound L hL D hD x a T
  · simp only [foldedOccupationDensity, foldedOccupationDensityENNReal,
      indicator_of_notMem ha, ENNReal.toReal_zero, zero_pow (by norm_num : 2 ≠ 0), integral_zero]
    have hT := T.coe_nonneg
    positivity

end TimeTraps.Probability
