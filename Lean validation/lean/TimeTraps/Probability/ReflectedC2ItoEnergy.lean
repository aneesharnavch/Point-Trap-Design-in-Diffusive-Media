module

public import TimeTraps.Probability.ReflectedC2ItoIsometry

@[expose] public section

/-! Expected time-integral and compact derivative-norm energy bounds for
the actual original-Brownian integral of a general reflected C² test. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedC2Ito_slope_time_integrable {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (T : ℝ≥0) :
    Integrable (fun ω => ∫ r in (0 : ℝ)..T.val,
      deriv F (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω) ^ 2)
      brownianDyadicMeasure := by
  apply (reflectedC2Ito_slope_square_integrable hF L hL D x T).integral_prod_right.congr
  filter_upwards [] with ω
  exact (intervalIntegral.integral_of_le T.coe_nonneg).symm

theorem reflectedC2ItoIntegral_secondMoment {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, reflectedC2ItoIntegral hF brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL D hD x T ω ^ 2
      ∂brownianDyadicMeasure) =
    2 * D * ∫ ω, (∫ r in (0 : ℝ)..T.val,
      deriv F (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω) ^ 2)
      ∂brownianDyadicMeasure := by
  calc
    _ = 2 * D * ∫ p : ℝ × (ℕ → ℝ),
        deriv F (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2) ^ 2
        ∂(((volume : Measure ℝ).restrict (Ioc (0 : ℝ) T.val)).prod brownianDyadicMeasure) :=
      reflectedC2ItoIntegral_isometry hF L hL D hD x T
    _ = _ := by
      apply congrArg (fun z : ℝ => 2 * D * z)
      refine (integral_prod_symm _ (reflectedC2Ito_slope_square_integrable hF L hL D x T)).trans ?_
      apply integral_congr_ae
      filter_upwards [] with ω
      exact (intervalIntegral.integral_of_le T.coe_nonneg).symm

theorem reflectedC2ItoIntegral_secondMoment_bound {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, reflectedC2ItoIntegral hF brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL D hD x T ω ^ 2
      ∂brownianDyadicMeasure) ≤ 2 * D * T.val * ‖(reflectedC2DerivativeMap hF L)‖ ^ 2 := by
  have hi := reflectedC2Ito_slope_square_integrable hF L hL D x T
  have hb : (∫ p : ℝ × (ℕ → ℝ),
      deriv F (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2) ^ 2
      ∂(((volume : Measure ℝ).restrict (Ioc (0 : ℝ) T.val)).prod brownianDyadicMeasure)) ≤
      ∫ _ : ℝ × (ℕ → ℝ), ‖(reflectedC2DerivativeMap hF L)‖ ^ 2
        ∂(((volume : Measure ℝ).restrict (Ioc (0 : ℝ) T.val)).prod brownianDyadicMeasure) := by
    apply integral_mono hi (integrable_const _)
    intro p
    have hp : |deriv F (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2)| ≤
        ‖(reflectedC2DerivativeMap hF L)‖ := reflectedFellerExtension_bound L hL (reflectedC2DerivativeMap hF L)
          (x + Real.sqrt (2 * D) * brownianDyadicPath p.1.toNNReal p.2)
    nlinarith [sq_abs (deriv F (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2)),
      abs_nonneg (deriv F (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2)),
      norm_nonneg (reflectedC2DerivativeMap hF L)]
  have hm : (((volume : Measure ℝ).restrict (Ioc (0 : ℝ) T.val)).prod
      brownianDyadicMeasure).real univ = T.val := by
    rw [← univ_prod_univ, measureReal_prod_prod]
    simp [Measure.real, Real.volume_Ioc]
  rw [integral_const, hm, smul_eq_mul] at hb
  calc
    _ = 2 * D * ∫ p : ℝ × (ℕ → ℝ),
        deriv F (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2) ^ 2
        ∂(((volume : Measure ℝ).restrict (Ioc (0 : ℝ) T.val)).prod brownianDyadicMeasure) :=
      reflectedC2ItoIntegral_isometry hF L hL D hD x T
    _ ≤ 2 * D * (T.val * ‖(reflectedC2DerivativeMap hF L)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end TimeTraps.Probability
