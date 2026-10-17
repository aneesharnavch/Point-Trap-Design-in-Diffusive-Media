module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeRevuzState

@[expose] public section

/-! Integrability and Fubini for bounded transition observations integrated
over physical time and the initial interval. No unproved Feller regularity
of a discontinuous band indicator is used. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

theorem reversibleResistance_transition_time_initial_integrable (A : IntervalMedium) (T : ℝ≥0)
    {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ z, |f z| ≤ M)
    (w : C(Icc A.source.left A.source.right, ℝ)) :
    Integrable (fun p : ℝ × Icc A.source.left A.source.right =>
      w p.2 * reversibleResistanceTransition A (resistanceRealTimeClip T p.1).val f p.2.val)
      ((volume.restrict (Ioc (0 : ℝ) T.val)).prod (reversibleResistanceLengthMeasure A)) := by
  let Q : ℝ × Icc A.source.left A.source.right →
      BrownianCompactTime T × Icc A.source.left A.source.right :=
    fun p => (resistanceRealTimeClip T p.1, p.2)
  have hQ : Measurable Q := ((resistanceRealTimeClip_measurable T).comp measurable_fst).prodMk measurable_snd
  have hm := (w.continuous.measurable.comp measurable_snd).mul
    ((reversibleResistanceTransition_compact_jointlyMeasurable_borel A T hf).comp hQ)
  apply (integrable_const (‖w‖ * M)).mono' hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  change ‖w p.2 * reversibleResistanceTransition A (resistanceRealTimeClip T p.1).val f p.2.val‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul (w.norm_coe_le_norm p.2)
    (reversibleResistanceTransition_bound A _ hb p.2.val) (norm_nonneg _) (norm_nonneg _)

theorem reversibleResistancePhysicalOccupationBand_initial_time (A : IntervalMedium) (a h : ℝ) (T : ℝ≥0)
    (w : C(Icc A.source.left A.source.right, ℝ)) :
    (∫ x, w x * (∫ ω, reversibleResistancePhysicalOccupationBand A x.val a h T ω ∂brownianDyadicMeasure)
      ∂reversibleResistanceLengthMeasure A) =
      (∫ s in Ioc (0 : ℝ) T.val, ∫ x, w x *
        reversibleResistanceTransition A s.toNNReal (brownianBandIndicator a h) x.val
          ∂reversibleResistanceLengthMeasure A) / resistancePhysicalBandMass A a h := by
  let F : ℝ × Icc A.source.left A.source.right → ℝ := fun p =>
    w p.2 * reversibleResistanceTransition A (resistanceRealTimeClip T p.1).val (brownianBandIndicator a h) p.2.val
  have hi : Integrable F ((volume.restrict (Ioc (0 : ℝ) T.val)).prod (reversibleResistanceLengthMeasure A)) :=
    reversibleResistance_transition_time_initial_integrable A T (brownianBandIndicator_measurable a h)
      (brownianBandIndicator_abs_le_one a h) w
  have he (x : Icc A.source.left A.source.right) :
      w x * (∫ ω, reversibleResistancePhysicalOccupationBand A x.val a h T ω ∂brownianDyadicMeasure) =
        (∫ s in Ioc (0 : ℝ) T.val, F (s, x)) / resistancePhysicalBandMass A a h := by
    have hc : (∫ s in Ioc (0 : ℝ) T.val, F (s, x)) =
        w x * ∫ s in (0 : ℝ)..T.val, reversibleResistanceTransition A s.toNNReal (brownianBandIndicator a h) x.val := by
      calc
        _ = ∫ s in Ioc (0 : ℝ) T.val, w x *
            reversibleResistanceTransition A s.toNNReal (brownianBandIndicator a h) x.val := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro s hs
          dsimp only [F]
          rw [resistanceRealTimeClip_of_mem T ⟨hs.1.le, hs.2⟩]
        _ = w x * ∫ s in Ioc (0 : ℝ) T.val,
            reversibleResistanceTransition A s.toNNReal (brownianBandIndicator a h) x.val := integral_const_mul _ _
        _ = _ := congrArg (fun v : ℝ => w x * v) (intervalIntegral.integral_of_le T.coe_nonneg).symm
    rw [hc, reversibleResistancePhysicalOccupationBand_mean_time A x.val a h T]
    ring
  calc
    _ = (∫ x, (∫ s in Ioc (0 : ℝ) T.val, F (s, x)) ∂reversibleResistanceLengthMeasure A) /
        resistancePhysicalBandMass A a h := by
      rw [← integral_div]
      exact integral_congr_ae (Eventually.of_forall he)
    _ = (∫ s in Ioc (0 : ℝ) T.val, ∫ x, F (s, x) ∂reversibleResistanceLengthMeasure A) /
        resistancePhysicalBandMass A a h := congrArg (fun v : ℝ => v / resistancePhysicalBandMass A a h)
          (integral_integral_swap hi).symm
    _ = _ := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only [F]
      rw [resistanceRealTimeClip_of_mem T ⟨hs.1.le, hs.2⟩]

end TimeTraps.Probability
