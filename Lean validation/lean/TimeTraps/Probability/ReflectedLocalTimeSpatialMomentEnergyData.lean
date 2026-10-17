module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentCoefficient
public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentBand

@[expose] public section

/-! Integrability and the deterministic band bound for the genuine time
integral of the squared reflected Tanaka difference coefficient. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

noncomputable def reflectedKinkDifferenceEnergy (L D x a b : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  brownianItoDrift brownianDyadicPath (fun z => reflectedKinkDifference L a b x (Real.sqrt (2 * D)) z ^ 2) T ω

theorem reflectedKinkDifference_square_abs_bound (L : ℝ) (hL : 0 < L) (a b x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (z : ℝ) :
    |reflectedKinkDifference L a b x σ z ^ 2| ≤ 4 * σ ^ 2 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  have h := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * σ)).mpr
    (reflectedKinkDifference_bound L hL a b x hσ z)
  rw [sq_abs] at h
  nlinarith

theorem reflectedKinkDifferenceEnergy_memLp (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x a b : ℝ) (T : ℝ≥0) :
    MemLp (reflectedKinkDifferenceEnergy L D x a b T) 2 brownianDyadicMeasure :=
  brownianItoDrift_bounded_memLp ((reflectedKinkDifference_measurable L hL a b x _).pow_const 2)
    brownianDyadicPath_jointly_measurable
    (reflectedKinkDifference_square_abs_bound L hL a b x (Real.sqrt_pos.mpr (by positivity))) T

theorem reflectedKinkDifferenceEnergy_nonneg (L D x a b : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) :
    0 ≤ reflectedKinkDifferenceEnergy L D x a b T ω :=
  intervalIntegral.integral_nonneg_of_forall T.coe_nonneg (fun _ => sq_nonneg _)

theorem reflectedKinkDifferenceEnergy_band_bound (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x a b : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) :
    reflectedKinkDifferenceEnergy L D x a b T ω ≤ 4 * Real.sqrt (2 * D) ^ 2 *
      brownianItoDrift (foldedTrajectory L D x brownianDyadicPath)
        (brownianBandIndicator a (2 * |a - b|)) T ω := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  have hg := brownianItoDrift_bounded_intervalIntegrable
    ((reflectedKinkDifference_measurable L hL a b x _).pow_const 2)
    brownianDyadicPath_jointly_measurable (reflectedKinkDifference_square_abs_bound L hL a b x hσ) T ω
  have hi := brownianItoDrift_bounded_intervalIntegrable
    (brownianBandIndicator_measurable a (2 * |a - b|))
    (foldedTrajectory_joint_measurable L D x brownianDyadicPath brownianDyadicPath_jointly_measurable)
    (brownianBandIndicator_abs_le_one a (2 * |a - b|)) T ω
  change (∫ r in (0 : ℝ)..T.val, reflectedKinkDifference L a b x (Real.sqrt (2 * D))
    (brownianDyadicPath r.toNNReal ω) ^ 2) ≤ _
  calc
    _ ≤ ∫ r in (0 : ℝ)..T.val, (4 * Real.sqrt (2 * D) ^ 2) *
        brownianBandIndicator a (2 * |a - b|) (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω) := by
      apply intervalIntegral.integral_mono_on T.coe_nonneg hg (hi.const_mul _)
      intro r _
      simpa only [foldedTrajectory, brownianBandIndicator_apply] using
        reflectedKinkDifference_square_band L hL a b x hσ (brownianDyadicPath r.toNNReal ω)
    _ = _ := intervalIntegral.integral_const_mul _ _

end TimeTraps.Probability
