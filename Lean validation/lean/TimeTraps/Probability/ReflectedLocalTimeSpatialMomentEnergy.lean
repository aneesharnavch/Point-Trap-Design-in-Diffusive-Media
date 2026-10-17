module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentEnergyData

@[expose] public section

/-! The quadratic energy of the actual reflected Tanaka difference has
a second moment of order the square of the level separation, uniformly
in the initial state. This bound has no sample spatial-continuity premise. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

noncomputable def reflectedSpatialSecondConstant (L D : ℝ) (T : ℝ≥0) : ℝ :=
  (3 * L ^ 2 + 6 * D * T.val + 3 * (D * T.val / L) ^ 2) / D ^ 2

theorem reflectedSpatialSecondConstant_nonneg (L : ℝ) {D : ℝ} (hD : 0 < D) (T : ℝ≥0) :
    0 ≤ reflectedSpatialSecondConstant L D T := by
  unfold reflectedSpatialSecondConstant
  have hT := T.coe_nonneg
  positivity

theorem reflectedKinkDifferenceEnergy_secondMoment (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x a b : ℝ) (T : ℝ≥0) :
    (∫ ω, reflectedKinkDifferenceEnergy L D x a b T ω ^ 2 ∂brownianDyadicMeasure) ≤
      256 * Real.sqrt (2 * D) ^ 4 * reflectedSpatialSecondConstant L D T * |a - b| ^ 2 := by
  by_cases hab : a = b
  · subst b
    simp [reflectedKinkDifferenceEnergy, brownianItoDrift, reflectedKinkDifference]
  have hd : 0 < 2 * |a - b| := by positivity
  let W := brownianItoDrift (foldedTrajectory L D x brownianDyadicPath)
    (brownianBandIndicator a (2 * |a - b|)) T
  have hW : MemLp W 2 brownianDyadicMeasure :=
    brownianItoDrift_bounded_memLp (brownianBandIndicator_measurable a (2 * |a - b|))
      (foldedTrajectory_joint_measurable L D x brownianDyadicPath brownianDyadicPath_jointly_measurable)
      (brownianBandIndicator_abs_le_one a (2 * |a - b|)) T
  have he : (∫ ω, reflectedKinkDifferenceEnergy L D x a b T ω ^ 2 ∂brownianDyadicMeasure) ≤
      ∫ ω, (4 * Real.sqrt (2 * D) ^ 2) ^ 2 * W ω ^ 2 ∂brownianDyadicMeasure := by
    apply integral_mono_ae (reflectedKinkDifferenceEnergy_memLp L hL D hD x a b T).integrable_sq
      (hW.integrable_sq.const_mul _)
    exact Eventually.of_forall (fun ω => by
      have hb := reflectedKinkDifferenceEnergy_band_bound L hL D hD x a b T ω
      have hn := reflectedKinkDifferenceEnergy_nonneg L D x a b T ω
      have hsq := (sq_le_sq₀ hn (hn.trans hb)).mpr hb
      simpa only [mul_pow] using hsq)
  rw [integral_const_mul] at he
  have hband := reflectedBandTime_secondMoment_uniform_bound L hL D hD x a hd T
  calc
    _ ≤ (4 * Real.sqrt (2 * D) ^ 2) ^ 2 * ∫ ω, W ω ^ 2 ∂brownianDyadicMeasure := he
    _ ≤ (4 * Real.sqrt (2 * D) ^ 2) ^ 2 * ((2 * (2 * |a - b|)) ^ 2 *
        reflectedSpatialSecondConstant L D T) :=
      mul_le_mul_of_nonneg_left hband (sq_nonneg _)
    _ = _ := by ring

end TimeTraps.Probability
