module

public import TimeTraps.Probability.ReversibleResistanceBandApproximation

@[expose] public section

/-! Dominated convergence for the actual physical transition and for
its finite initial-state pairings against continuous occupation-band
approximations. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Interval
open scoped NNReal Topology BoundedContinuousFunction

theorem reversibleResistanceTransition_band_tendsto (A : IntervalMedium)
    (a h : ℝ) (t : ℝ≥0) (x : ℝ) :
    Tendsto (fun n => reversibleResistanceTransition A t
      (resistanceOpenApproximation (Ioo (a - h) (a + h)) n) x) atTop
      (𝓝 (reversibleResistanceTransition A t (brownianBandIndicator a h) x)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ : BrownianCompletedSample => (1 : ℝ))
  · intro n
    exact (reversibleResistancePath_borel_integrable A x t
      (resistanceOpenApproximation (Ioo (a - h) (a + h)) n).measurable
      (resistanceOpenApproximation_norm_le _ n)).aestronglyMeasurable
  · exact integrable_const _
  · exact fun n => Eventually.of_forall (fun ω => resistanceOpenApproximation_norm_le _ n _)
  · exact Eventually.of_forall (fun ω => resistanceBandApproximation_tendsto a h _)

theorem reversibleResistanceWeightedTransition_band_tendsto (A : IntervalMedium)
    (w : C(Icc A.source.left A.source.right, ℝ)) (a h : ℝ) (t : ℝ≥0) :
    Tendsto (fun n => reversibleResistanceWeightedTransition A w
      (resistanceOpenApproximation (Ioo (a - h) (a + h)) n) t) atTop
      (𝓝 (∫ x, w x * reversibleResistanceTransition A t (brownianBandIndicator a h) x.val
        ∂reversibleResistanceLengthMeasure A)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖w‖)
  · intro n
    exact (reversibleResistanceWeightedTransition_integrable A w _ t).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    apply Eventually.of_forall
    intro x
    rw [norm_mul]
    calc
      _ ≤ ‖w‖ * 1 := mul_le_mul (w.norm_coe_le_norm x)
        (reversibleResistanceTransition_bound A t (resistanceOpenApproximation_norm_le _ n) x.val)
        (abs_nonneg _) (norm_nonneg _)
      _ = ‖w‖ := mul_one _
  · exact Eventually.of_forall (fun x =>
      (reversibleResistanceTransition_band_tendsto A a h t x.val).const_mul (w x))

theorem reversibleResistanceBandWeightedTransition_tendsto (A : IntervalMedium)
    (w : C(Icc A.source.left A.source.right, ℝ)) (f : ℝ →ᵇ ℝ) (a h : ℝ) (t : ℝ≥0) :
    Tendsto (fun n => ∫ x, w x * resistanceOpenApproximation (Ioo (a - h) (a + h)) n x.val *
        reversibleResistanceTransition A t f x.val ∂reversibleResistanceLengthMeasure A)
      atTop (𝓝 (∫ x, w x * brownianBandIndicator a h x.val *
        reversibleResistanceTransition A t f x.val ∂reversibleResistanceLengthMeasure A)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖w‖ * ‖f‖)
  · intro n
    exact ((w.continuous.measurable.mul
      ((resistanceOpenApproximation (Ioo (a - h) (a + h)) n).measurable.comp measurable_subtype_coe)).mul
        (reversibleResistanceTransition_measurable_interval A t f.measurable)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    apply Eventually.of_forall
    intro x
    rw [norm_mul, norm_mul]
    have hb : ‖w x‖ * ‖resistanceOpenApproximation (Ioo (a - h) (a + h)) n x.val‖ ≤ ‖w‖ := by
      exact (mul_le_mul (w.norm_coe_le_norm x) (resistanceOpenApproximation_norm_le _ n x.val)
        (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_one _)
    exact mul_le_mul hb (reversibleResistanceTransition_bound A t f.norm_coe_le_norm x.val)
      (norm_nonneg _) (norm_nonneg _)
  · exact Eventually.of_forall (fun x =>
      ((resistanceBandApproximation_tendsto a h x.val).const_mul (w x)).mul_const _)

end TimeTraps.Probability

end
