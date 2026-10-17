module

public import TimeTraps.Probability.ReflectedNeumannItoFormula
public import TimeTraps.Probability.ReflectedNeumannItoIsometry

@[expose] public section

/-! Expectation and energy of the literal reflected Neumann Dynkin
expression. Product integrability justifies the physical expected time
integral in the isometry. The initial value is evaluated at fold(x), so
the starting input is arbitrary. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedNeumannIto_slope_time_integrable {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D x : ℝ) (T : ℝ≥0) :
    Integrable (fun ω => ∫ r in (0 : ℝ)..T.val,
      F.slope (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω) ^ 2)
      brownianDyadicMeasure := by
  apply (reflectedNeumannIto_slope_square_integrable F hL D x T).integral_prod_right.congr
  filter_upwards [] with ω
  exact (intervalIntegral.integral_of_le T.coe_nonneg).symm

theorem reflectedNeumannDynkin_ito_mean {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, reflectedNeumannDynkin F hL brownianDyadicPath D x T ω
      ∂brownianDyadicMeasure) = 0 := by
  rw [integral_congr_ae (reflectedNeumannDynkin_eq_stochasticIntegral_ae F hL D hD x T)]
  exact reflectedNeumannItoIntegral_mean F hL D x T

theorem reflectedNeumannDynkin_ito_secondMoment {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, reflectedNeumannDynkin F hL brownianDyadicPath D x T ω ^ 2
      ∂brownianDyadicMeasure) =
    2 * D * ∫ ω, (∫ r in (0 : ℝ)..T.val,
      F.slope (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω) ^ 2)
      ∂brownianDyadicMeasure := by
  have he : (fun ω => reflectedNeumannDynkin F hL brownianDyadicPath D x T ω ^ 2)
      =ᵐ[brownianDyadicMeasure] (fun ω =>
        brownianStochasticIntegral (reflectedNeumannItoIntegrand F hL D x T) ω ^ 2) := by
    filter_upwards [reflectedNeumannDynkin_eq_stochasticIntegral_ae F hL D hD x T] with ω hω
    exact congrArg (fun z : ℝ => z ^ 2) hω
  calc
    _ = ∫ ω, brownianStochasticIntegral (reflectedNeumannItoIntegrand F hL D x T) ω ^ 2
        ∂brownianDyadicMeasure := integral_congr_ae he
    _ = 2 * D * ∫ p : ℝ × (ℕ → ℝ),
        F.slope (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2) ^ 2
        ∂(((volume : Measure ℝ).restrict (Ioc (0 : ℝ) T.val)).prod brownianDyadicMeasure) :=
      reflectedNeumannItoIntegral_isometry F hL D hD x T
    _ = _ := by
      apply congrArg (fun z : ℝ => 2 * D * z)
      refine (integral_prod_symm _ (reflectedNeumannIto_slope_square_integrable F hL D x T)).trans ?_
      apply integral_congr_ae
      filter_upwards [] with ω
      exact (intervalIntegral.integral_of_le T.coe_nonneg).symm

theorem reflectedNeumannIto_expected_value {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, F.value (foldedTrajectory L D x brownianDyadicPath T ω) ∂brownianDyadicMeasure) -
      F.value (reflectedFold L x) =
    D * ∫ ω, (∫ r in (0 : ℝ)..T.val,
      F.curvature (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω))
      ∂brownianDyadicMeasure := by
  have he := brownianDiffusionItoTanakaC2_mean
    (F.extension_global_contDiff hL) (M₂ := ‖F.curvatureMap‖₊)
    (F.extension_global_second_bound hL) (∅ : Finset Unit)
    (fun _ => 0) (fun _ => 0) x hD T
  simp only [finiteKinkPotential, Finset.sum_empty, add_zero, mul_zero] at he
  have hd : brownianItoDrift (affineBrownianInput x (Real.sqrt (2 * D)))
      (deriv (deriv (reflectedFellerExtension L hL F.valueMap))) T =
      (fun ω => ∫ r in (0 : ℝ)..T.val,
        F.curvature (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)) := by
    funext ω
    unfold brownianItoDrift
    congr 1
    funext r
    exact F.extension_global_second hL _
  rw [hd] at he
  change (∫ ω, F.value (foldedTrajectory L D x brownianDyadicPath T ω) -
    F.value (reflectedFold L x) ∂brownianDyadicMeasure) = _ at he
  have hv : Integrable (fun ω => F.value (foldedTrajectory L D x brownianDyadicPath T ω))
      brownianDyadicMeasure :=
    (reflectedContinuousInput_eval_memLp (P := brownianDyadicMeasure)
      brownianDyadicPath_measurable L hL D x F.valueMap T).integrable (by norm_num)
  simpa only [integral_sub hv (integrable_const _), integral_const,
    probReal_univ, one_smul] using he

theorem reflectedNeumannDynkin_ito_secondMoment_bound {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, reflectedNeumannDynkin F hL brownianDyadicPath D x T ω ^ 2
      ∂brownianDyadicMeasure) ≤ 2 * D * T.val * ‖F.slopeMap‖ ^ 2 := by
  have he : (fun ω => reflectedNeumannDynkin F hL brownianDyadicPath D x T ω ^ 2)
      =ᵐ[brownianDyadicMeasure] (fun ω =>
        brownianStochasticIntegral (reflectedNeumannItoIntegrand F hL D x T) ω ^ 2) := by
    filter_upwards [reflectedNeumannDynkin_eq_stochasticIntegral_ae F hL D hD x T] with ω hω
    exact congrArg (fun z : ℝ => z ^ 2) hω
  have hi := reflectedNeumannIto_slope_square_integrable F hL D x T
  have hb : (∫ p : ℝ × (ℕ → ℝ),
      F.slope (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2) ^ 2
      ∂(((volume : Measure ℝ).restrict (Ioc (0 : ℝ) T.val)).prod brownianDyadicMeasure)) ≤
      ∫ _ : ℝ × (ℕ → ℝ), ‖F.slopeMap‖ ^ 2
        ∂(((volume : Measure ℝ).restrict (Ioc (0 : ℝ) T.val)).prod brownianDyadicMeasure) := by
    apply integral_mono hi (integrable_const _)
    intro p
    have hp : |F.slope (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2)| ≤
        ‖F.slopeMap‖ := reflectedFellerExtension_bound L hL F.slopeMap
          (x + Real.sqrt (2 * D) * brownianDyadicPath p.1.toNNReal p.2)
    nlinarith [sq_abs (F.slope (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2)),
      abs_nonneg (F.slope (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2)),
      norm_nonneg F.slopeMap]
  have hm : (((volume : Measure ℝ).restrict (Ioc (0 : ℝ) T.val)).prod
      brownianDyadicMeasure).real univ = T.val := by
    rw [← univ_prod_univ, measureReal_prod_prod]
    simp [Measure.real, Real.volume_Ioc]
  rw [integral_const, hm, smul_eq_mul] at hb
  calc
    _ = ∫ ω, brownianStochasticIntegral (reflectedNeumannItoIntegrand F hL D x T) ω ^ 2
        ∂brownianDyadicMeasure := integral_congr_ae he
    _ = 2 * D * ∫ p : ℝ × (ℕ → ℝ),
        F.slope (foldedTrajectory L D x brownianDyadicPath p.1.toNNReal p.2) ^ 2
        ∂(((volume : Measure ℝ).restrict (Ioc (0 : ℝ) T.val)).prod brownianDyadicMeasure) :=
      reflectedNeumannItoIntegral_isometry F hL D hD x T
    _ ≤ 2 * D * (T.val * ‖F.slopeMap‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end TimeTraps.Probability
