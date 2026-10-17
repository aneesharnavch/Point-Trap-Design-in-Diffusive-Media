module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeRevuzAverage
public import TimeTraps.Probability.ReversibleResistanceLocalTimeRevuzSymmetry
public import TimeTraps.Probability.ReversibleResistanceLocalTimeRevuzInitial

@[expose] public section

/-! The actual physical local time has the exact finite-time speed
pairing. Both band limits are proved independently, so this identifies
the literal local time without postulating a Revuz normalization. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal Topology BoundedContinuousFunction

theorem reversibleResistanceLocalTime_speed_mean (A : IntervalMedium)
    (a : Ioo A.source.left A.source.right) (T : ℝ≥0) (f : ℝ →ᵇ ℝ) :
    (∫ x, A.source.density x.val * f x.val *
      (∫ ω, reversibleResistanceLocalTime A x.val a.val T ω ∂brownianDyadicMeasure)
        ∂reversibleResistanceLengthMeasure A) =
      ∫ s in (0 : ℝ)..T.val, reversibleResistanceTransition A s.toNNReal f a.val := by
  let q : C(Icc A.source.left A.source.right, ℝ) :=
    ⟨fun x => ∫ s in (0 : ℝ)..T.val, reversibleResistanceTransition A s.toNNReal f x.val,
      reversibleResistanceTransition_potential_continuous A f.continuous.continuousOn T⟩
  have hl := reversibleResistancePhysicalOccupationBand_initial_tendsto A a T
    (reversibleResistanceSpeedWeight A f)
  have hr := resistanceRevuzField_average_tendsto A a q
  exact tendsto_nhds_unique hl (hr.congr (fun h =>
    (reversibleResistancePhysicalOccupationBand_initial_potential A a.val h T f).symm))

theorem reversibleResistanceLocalTime_speed_mean_continuous (A : IntervalMedium)
    (a : Ioo A.source.left A.source.right) (T : ℝ≥0)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc A.source.left A.source.right)) :
    (∫ x, A.source.density x.val * f x.val *
      (∫ ω, reversibleResistanceLocalTime A x.val a.val T ω ∂brownianDyadicMeasure)
        ∂reversibleResistanceLengthMeasure A) =
      ∫ s in (0 : ℝ)..T.val, reversibleResistanceTransition A s.toNNReal f a.val := by
  let F := reversibleResistanceContinuousExtension A f hf
  have hF := reversibleResistanceContinuousExtension_eq A f hf
  calc
    _ = ∫ x, A.source.density x.val * F x.val *
        (∫ ω, reversibleResistanceLocalTime A x.val a.val T ω ∂brownianDyadicMeasure)
          ∂reversibleResistanceLengthMeasure A := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => congrArg
        (fun v : ℝ => A.source.density x.val * v *
          (∫ ω, reversibleResistanceLocalTime A x.val a.val T ω ∂brownianDyadicMeasure))
        (hF x.property).symm)
    _ = ∫ s in (0 : ℝ)..T.val, reversibleResistanceTransition A s.toNNReal F a.val :=
      reversibleResistanceLocalTime_speed_mean A a T F
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro s _
      exact reversibleResistanceTransition_congr_interval A hF s.toNNReal a.val

theorem reversibleResistanceLocalTime_speed_integrable_continuous (A : IntervalMedium)
    (a : Ioo A.source.left A.source.right) (T : ℝ≥0)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc A.source.left A.source.right)) :
    Integrable (fun x => A.source.density x.val * f x.val *
      (∫ ω, reversibleResistanceLocalTime A x.val a.val T ω ∂brownianDyadicMeasure))
        (reversibleResistanceLengthMeasure A) := by
  let w : C(Icc A.source.left A.source.right, ℝ) :=
    ⟨fun x => A.source.density x.val * f x.val,
      (A.source.continuous.comp_continuous continuous_subtype_val (fun x => x.property)).mul
        (hf.comp_continuous continuous_subtype_val (fun x => x.property))⟩
  exact reversibleResistanceLocalTime_initial_integrable A a T w

theorem reversibleResistanceLocalTime_speed_interval_integrable (A : IntervalMedium)
    (a : Ioo A.source.left A.source.right) (T : ℝ≥0)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc A.source.left A.source.right)) :
    IntegrableOn (fun x => A.source.density x * f x *
      (∫ ω, reversibleResistanceLocalTime A x a.val T ω ∂brownianDyadicMeasure))
        (Icc A.source.left A.source.right) volume := by
  exact (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mpr
    (reversibleResistanceLocalTime_speed_integrable_continuous A a T hf)

theorem reversibleResistanceLocalTime_speed_interval (A : IntervalMedium)
    (a : Ioo A.source.left A.source.right) (T : ℝ≥0)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc A.source.left A.source.right)) :
    (∫ x in A.source.left..A.source.right, A.source.density x * f x *
      (∫ ω, reversibleResistanceLocalTime A x a.val T ω ∂brownianDyadicMeasure)) =
      ∫ s in (0 : ℝ)..T.val, reversibleResistanceTransition A s.toNNReal f a.val :=
  (reversibleResistanceLengthMeasure_integral A (fun x => A.source.density x * f x *
    (∫ ω, reversibleResistanceLocalTime A x a.val T ω ∂brownianDyadicMeasure))).symm.trans
      (reversibleResistanceLocalTime_speed_mean_continuous A a T hf)

end TimeTraps.Probability
