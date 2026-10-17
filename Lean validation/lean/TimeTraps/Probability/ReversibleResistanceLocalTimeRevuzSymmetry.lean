module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeRevuzFubini
public import TimeTraps.Probability.ReversibleResistanceBandSymmetry
public import TimeTraps.Probability.ReversibleResistanceFeller

@[expose] public section

/-! Actual transition symmetry and product integrability turn the
initially averaged physical band into the speed-mass spatial average of
the finite-time transition potential. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal Topology BoundedContinuousFunction

theorem reversibleResistance_band_transition_time_integrable (A : IntervalMedium)
    (a h : ℝ) (T : ℝ≥0) (f : ℝ →ᵇ ℝ) :
    Integrable (fun p : ℝ × Icc A.source.left A.source.right =>
      A.source.density p.2.val * brownianBandIndicator a h p.2.val *
        reversibleResistanceTransition A (resistanceRealTimeClip T p.1).val f p.2.val)
      ((volume.restrict (Ioc (0 : ℝ) T.val)).prod (reversibleResistanceLengthMeasure A)) := by
  let w : C(Icc A.source.left A.source.right, ℝ) :=
    ⟨fun x => A.source.density x.val,
      A.source.continuous.comp_continuous continuous_subtype_val (fun x => x.property)⟩
  have hi := reversibleResistance_transition_time_initial_integrable A T f.measurable f.norm_coe_le_norm w
  have hm : Measurable (fun p : ℝ × Icc A.source.left A.source.right => brownianBandIndicator a h p.2.val) :=
    (brownianBandIndicator_measurable a h).comp (measurable_subtype_coe.comp measurable_snd)
  have hb := hi.bdd_mul hm.aestronglyMeasurable
    (Eventually.of_forall (fun p => brownianBandIndicator_abs_le_one a h p.2.val))
  apply hb.congr
  apply Eventually.of_forall
  intro p
  change brownianBandIndicator a h p.2.val * (A.source.density p.2.val *
    reversibleResistanceTransition A (resistanceRealTimeClip T p.1).val f p.2.val) = _
  ring

theorem reversibleResistancePhysicalOccupationBand_initial_potential (A : IntervalMedium)
    (a h : ℝ) (T : ℝ≥0) (f : ℝ →ᵇ ℝ) :
    (∫ x, A.source.density x.val * f x.val *
      (∫ ω, reversibleResistancePhysicalOccupationBand A x.val a h T ω ∂brownianDyadicMeasure)
        ∂reversibleResistanceLengthMeasure A) =
      (∫ x, A.source.density x.val * brownianBandIndicator a h x.val *
        (∫ s in (0 : ℝ)..T.val, reversibleResistanceTransition A s.toNNReal f x.val)
          ∂reversibleResistanceLengthMeasure A) / resistancePhysicalBandMass A a h := by
  let F : ℝ × Icc A.source.left A.source.right → ℝ := fun p =>
    A.source.density p.2.val * brownianBandIndicator a h p.2.val *
      reversibleResistanceTransition A (resistanceRealTimeClip T p.1).val f p.2.val
  have hi : Integrable F ((volume.restrict (Ioc (0 : ℝ) T.val)).prod (reversibleResistanceLengthMeasure A)) :=
    reversibleResistance_band_transition_time_integrable A a h T f
  have hs (s : ℝ) :
      (∫ x, A.source.density x.val * f x.val *
        reversibleResistanceTransition A s.toNNReal (brownianBandIndicator a h) x.val
          ∂reversibleResistanceLengthMeasure A) =
      ∫ x, A.source.density x.val * brownianBandIndicator a h x.val *
        reversibleResistanceTransition A s.toNNReal f x.val ∂reversibleResistanceLengthMeasure A :=
    (reversibleResistanceLengthMeasure_integral A _).trans
      ((reversibleResistanceTransition_speed_band_symmetric A f a h s.toNNReal).trans
        (reversibleResistanceLengthMeasure_integral A _).symm)
  have he (x : Icc A.source.left A.source.right) :
      (∫ s in Ioc (0 : ℝ) T.val, F (s, x)) =
        A.source.density x.val * brownianBandIndicator a h x.val *
          (∫ s in (0 : ℝ)..T.val, reversibleResistanceTransition A s.toNNReal f x.val) := by
    calc
      _ = ∫ s in Ioc (0 : ℝ) T.val, A.source.density x.val * brownianBandIndicator a h x.val *
          reversibleResistanceTransition A s.toNNReal f x.val := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro s hs
        dsimp only [F]
        rw [resistanceRealTimeClip_of_mem T ⟨hs.1.le, hs.2⟩]
      _ = (A.source.density x.val * brownianBandIndicator a h x.val) *
          (∫ s in Ioc (0 : ℝ) T.val, reversibleResistanceTransition A s.toNNReal f x.val) :=
        integral_const_mul _ _
      _ = _ := congrArg (fun v : ℝ => A.source.density x.val * brownianBandIndicator a h x.val * v)
        (intervalIntegral.integral_of_le T.coe_nonneg).symm
  calc
    _ = (∫ s in Ioc (0 : ℝ) T.val, ∫ x, A.source.density x.val * f x.val *
        reversibleResistanceTransition A s.toNNReal (brownianBandIndicator a h) x.val
          ∂reversibleResistanceLengthMeasure A) / resistancePhysicalBandMass A a h :=
      reversibleResistancePhysicalOccupationBand_initial_time A a h T (reversibleResistanceSpeedWeight A f)
    _ = (∫ s in Ioc (0 : ℝ) T.val, ∫ x, F (s, x) ∂reversibleResistanceLengthMeasure A) /
        resistancePhysicalBandMass A a h := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs'
      apply (hs s).trans
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only [F]
      rw [resistanceRealTimeClip_of_mem T ⟨hs'.1.le, hs'.2⟩]
    _ = (∫ x, (∫ s in Ioc (0 : ℝ) T.val, F (s, x)) ∂reversibleResistanceLengthMeasure A) /
        resistancePhysicalBandMass A a h :=
      congrArg (fun v : ℝ => v / resistancePhysicalBandMass A a h) (integral_integral_swap hi)
    _ = _ := congrArg (fun v : ℝ => v / resistancePhysicalBandMass A a h)
      (integral_congr_ae (Eventually.of_forall he))

end TimeTraps.Probability
