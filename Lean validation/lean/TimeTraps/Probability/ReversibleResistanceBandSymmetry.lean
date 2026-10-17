module

public import TimeTraps.Probability.ReversibleResistanceBandSymmetryData

@[expose] public section

/-! Speed-measure symmetry with one literal open occupation-band
indicator. This is derived from continuous-test symmetry by dominated
convergence and does not assume any Borel symmetry principle. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Interval
open scoped NNReal Topology BoundedContinuousFunction

theorem reversibleResistanceTransition_speed_band_symmetric (A : IntervalMedium)
    (f : ℝ →ᵇ ℝ) (a h : ℝ) (t : ℝ≥0) :
    (∫ x in A.source.left..A.source.right, A.source.density x * f x *
      reversibleResistanceTransition A t (brownianBandIndicator a h) x) =
      ∫ x in A.source.left..A.source.right, A.source.density x * brownianBandIndicator a h x *
        reversibleResistanceTransition A t f x := by
  let w : C(Icc A.source.left A.source.right, ℝ) :=
    ⟨fun x => A.source.density x.val,
      A.source.continuous.comp_continuous continuous_subtype_val (fun x => x.property)⟩
  have hl := reversibleResistanceWeightedTransition_band_tendsto A
    (reversibleResistanceSpeedWeight A f) a h t
  have hr := reversibleResistanceBandWeightedTransition_tendsto A w f a h t
  have he (n : ℕ) :
      reversibleResistanceWeightedTransition A (reversibleResistanceSpeedWeight A f)
        (resistanceOpenApproximation (Ioo (a - h) (a + h)) n) t =
      ∫ x, w x * resistanceOpenApproximation (Ioo (a - h) (a + h)) n x.val *
        reversibleResistanceTransition A t f x.val ∂reversibleResistanceLengthMeasure A := by
    let b := resistanceOpenApproximation (Ioo (a - h) (a + h)) n
    change (∫ x, A.source.density x.val * f x.val * reversibleResistanceTransition A t b x.val
      ∂reversibleResistanceLengthMeasure A) =
      ∫ x, A.source.density x.val * b x.val * reversibleResistanceTransition A t f x.val
        ∂reversibleResistanceLengthMeasure A
    exact (reversibleResistanceLengthMeasure_integral A (fun x =>
      A.source.density x * f x * reversibleResistanceTransition A t b x)).trans
        ((reversibleResistanceTransition_speed_symmetric A f b t).trans
          (reversibleResistanceLengthMeasure_integral A (fun x =>
            A.source.density x * b x * reversibleResistanceTransition A t f x)).symm)
  have hp := tendsto_nhds_unique hl (hr.congr (fun n => (he n).symm))
  exact (reversibleResistanceLengthMeasure_integral A (fun x =>
    A.source.density x * f x * reversibleResistanceTransition A t (brownianBandIndicator a h) x)).symm.trans
      (hp.trans (reversibleResistanceLengthMeasure_integral A (fun x =>
        A.source.density x * brownianBandIndicator a h x * reversibleResistanceTransition A t f x)))

theorem reversibleResistanceTransition_speed_band_symmetric_continuous (A : IntervalMedium)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc A.source.left A.source.right)) (a h : ℝ) (t : ℝ≥0) :
    (∫ x in A.source.left..A.source.right, A.source.density x * f x *
      reversibleResistanceTransition A t (brownianBandIndicator a h) x) =
      ∫ x in A.source.left..A.source.right, A.source.density x * brownianBandIndicator a h x *
        reversibleResistanceTransition A t f x := by
  let F := reversibleResistanceContinuousExtension A f hf
  have hF := reversibleResistanceContinuousExtension_eq A f hf
  have hs := reversibleResistanceTransition_speed_band_symmetric A F a h t
  calc
    _ = ∫ x in A.source.left..A.source.right, A.source.density x * F x *
        reversibleResistanceTransition A t (brownianBandIndicator a h) x := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [hF (uIcc_of_le A.source.increasing.le ▸ hx)]
    _ = _ := hs.trans (by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [reversibleResistanceTransition_congr_interval A hF])

theorem reversibleResistanceTransition_speed_band_invariant (A : IntervalMedium)
    (a h : ℝ) (t : ℝ≥0) :
    (∫ x in A.source.left..A.source.right, A.source.density x *
      reversibleResistanceTransition A t (brownianBandIndicator a h) x) =
      ∫ x in A.source.left..A.source.right, A.source.density x * brownianBandIndicator a h x := by
  have hs := reversibleResistanceTransition_speed_band_symmetric_continuous A
    (f := fun _ => (1 : ℝ)) continuousOn_const a h t
  simpa only [mul_one, reversibleResistanceTransition_one] using hs

end TimeTraps.Probability

end
