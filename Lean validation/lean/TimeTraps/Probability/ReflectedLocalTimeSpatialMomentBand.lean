module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentProduct
public import TimeTraps.Probability.ReflectedLocalTimeBandData

@[expose] public section

/-! The genuine ordinary time spent in a spatial band has a second moment
of order the square of its width, uniformly in the particle's initial state.
The bound uses the actual occupation identity and justified spatial Fubini. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedBandTime_spatial_integral_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x a : ℝ) {h : ℝ} (hh : 0 < h) (T : ℝ≥0) :
    brownianItoDrift (foldedTrajectory L D x brownianDyadicPath) (brownianBandIndicator a h) T =ᵐ[brownianDyadicMeasure]
      fun ω => ∫ b in Ioo (a - h) (a + h), foldedOccupationDensity L D x T ω b := by
  filter_upwards [reflectedOccupationBand_spatial_average_ae L hL D hD x a] with ω hω
  have he := (hω T h).2
  change (1 / (2 * h)) * brownianItoDrift (foldedTrajectory L D x brownianDyadicPath)
    (brownianBandIndicator a h) T ω = (1 / (2 * h)) * _ at he
  exact mul_left_cancel₀ (by positivity : (1 / (2 * h) : ℝ) ≠ 0) he

theorem reflectedBandTime_secondMoment_uniform_bound (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x a : ℝ) {h : ℝ} (hh : 0 < h) (T : ℝ≥0) :
    (∫ ω, brownianItoDrift (foldedTrajectory L D x brownianDyadicPath)
      (brownianBandIndicator a h) T ω ^ 2 ∂brownianDyadicMeasure) ≤
      (2 * h) ^ 2 * ((3 * L ^ 2 + 6 * D * T.val + 3 * (D * T.val / L) ^ 2) / D ^ 2) := by
  have hlen : a + h - (a - h) = 2 * h := by ring
  have hi := foldedOccupationDensity_square_product_integrable L hL D hD x (a - h) (a + h) T
  have hmem : MemLp (brownianItoDrift (foldedTrajectory L D x brownianDyadicPath)
      (brownianBandIndicator a h) T) 2 brownianDyadicMeasure :=
    brownianItoDrift_bounded_memLp (brownianBandIndicator_measurable a h)
      (foldedTrajectory_joint_measurable L D x brownianDyadicPath brownianDyadicPath_jointly_measurable)
      (brownianBandIndicator_abs_le_one a h) T
  have hb : (∫ ω, brownianItoDrift (foldedTrajectory L D x brownianDyadicPath)
      (brownianBandIndicator a h) T ω ^ 2 ∂brownianDyadicMeasure) ≤
      ∫ ω, (2 * h) * (∫ b in Ioo (a - h) (a + h), foldedOccupationDensity L D x T ω b ^ 2) ∂brownianDyadicMeasure := by
    apply integral_mono_ae hmem.integrable_sq (hi.integral_prod_right.const_mul (2 * h))
    filter_upwards [reflectedBandTime_spatial_integral_ae L hL D hD x a hh T,
      foldedOccupationDensity_spatial_integral_square_ae L hL D hD x (a - h) (a + h) (by linarith) T] with ω he hc
    rw [he]
    simpa only [hlen] using hc
  rw [integral_const_mul] at hb
  have hc := foldedOccupationDensity_spatial_square_mean_bound L hL D hD x (a - h) (a + h) (by linarith) T
  rw [hlen] at hc
  calc
    _ ≤ (2 * h) * (∫ ω, (∫ b in Ioo (a - h) (a + h), foldedOccupationDensity L D x T ω b ^ 2) ∂brownianDyadicMeasure) := hb
    _ ≤ (2 * h) * ((2 * h) * ((3 * L ^ 2 + 6 * D * T.val + 3 * (D * T.val / L) ^ 2) / D ^ 2)) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

theorem reflectedBandTime_literal_secondMoment_uniform_bound (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x a : ℝ) {h : ℝ} (hh : 0 < h) (T : ℝ≥0) :
    (∫ ω, (∫ s in (0 : ℝ)..T.val,
      if |foldedTrajectory L D x brownianDyadicPath s.toNNReal ω - a| < h then (1 : ℝ) else 0) ^ 2 ∂brownianDyadicMeasure) ≤
      (2 * h) ^ 2 * ((3 * L ^ 2 + 6 * D * T.val + 3 * (D * T.val / L) ^ 2) / D ^ 2) := by
  simpa only [brownianItoDrift, brownianBandIndicator_apply] using
    reflectedBandTime_secondMoment_uniform_bound L hL D hD x a hh T

theorem reflectedOccupationBand_secondMoment_uniform_bound (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x a : ℝ) {h : ℝ} (hh : 0 < h) (T : ℝ≥0) :
    (∫ ω, reflectedOccupationBand L D x a h T ω ^ 2 ∂brownianDyadicMeasure) ≤
      (3 * L ^ 2 + 6 * D * T.val + 3 * (D * T.val / L) ^ 2) / D ^ 2 := by
  have hb := reflectedBandTime_secondMoment_uniform_bound L hL D hD x a hh T
  have he : (fun ω => reflectedOccupationBand L D x a h T ω ^ 2) =
      fun ω => (1 / (2 * h) ^ 2) * brownianItoDrift (foldedTrajectory L D x brownianDyadicPath) (brownianBandIndicator a h) T ω ^ 2 := by
    funext ω
    unfold reflectedOccupationBand brownianBandOccupation
    ring
  rw [he, integral_const_mul]
  calc
    _ ≤ (1 / (2 * h) ^ 2) * ((2 * h) ^ 2 * ((3 * L ^ 2 + 6 * D * T.val + 3 * (D * T.val / L) ^ 2) / D ^ 2)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (3 * L ^ 2 + 6 * D * T.val + 3 * (D * T.val / L) ^ 2) / D ^ 2 := by
      rw [← mul_assoc, one_div, inv_mul_cancel₀ (by positivity : (2 * h) ^ 2 ≠ 0), one_mul]

end TimeTraps.Probability
