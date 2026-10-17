module

public import TimeTraps.Probability.ReflectedTimeChangedOperatorContinuous
public import TimeTraps.Probability.ReversibleResistanceSpeedContinuous

@[expose] public section

/-! Spatial continuity of the actual physical transition and of its
finite-time potential. Both conclusions retain tests continuous only
on the original closed physical interval. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Interval
open scoped NNReal Topology

theorem reversibleResistanceTransition_continuous_interval (A : IntervalMedium)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc A.source.left A.source.right)) (t : ℝ≥0) :
    Continuous (fun x : Icc A.source.left A.source.right => reversibleResistanceTransition A t f x.val) := by
  let R : Icc A.source.left A.source.right → Icc (0 : ℝ) A.resistanceLength :=
    fun x => ⟨A.resistance x.val, A.resistance_mem x.property⟩
  have hR : Continuous R := A.resistance_continuous.domRestrict.subtype_mk _
  have hg : ContinuousOn (fun y => f (A.resistanceInverse y)) (Icc 0 A.resistanceLength) :=
    hf.comp A.resistanceInverse_continuous.continuousOn (fun y _ => A.resistanceInverse_mem y)
  have hc := (reflectedTimeChangedOperator_continuous_interval A.resistanceLength
    A.resistanceLength_pos 1 A.resistanceSpeed A.resistanceSpeed_continuous.continuousOn
      (fun y _ => A.resistanceSpeed_pos y) t hg).comp hR
  have he : (fun x : Icc A.source.left A.source.right => reversibleResistanceTransition A t f x.val) =
      (fun y : Icc (0 : ℝ) A.resistanceLength => reflectedTimeChangedOperator A.resistanceLength
        1 A.resistanceSpeed t (fun z => f (A.resistanceInverse z)) y.val) ∘ R := by
    funext x
    exact reversibleResistanceTransition_reference A t f x.val
  exact he.symm ▸ hc

theorem reversibleResistanceTransition_potential_continuous (A : IntervalMedium)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc A.source.left A.source.right)) (T : ℝ≥0) :
    Continuous (fun x : Icc A.source.left A.source.right =>
      ∫ t in (0 : ℝ)..T.val, reversibleResistanceTransition A t.toNNReal f x.val) := by
  let F := reversibleResistanceContinuousExtension A f hf
  have hF := reversibleResistanceContinuousExtension_eq A f hf
  have he (x : Icc A.source.left A.source.right) (t : ℝ) :
      reversibleResistanceTransition A t.toNNReal f x.val =
        reversibleResistanceTransition A t.toNNReal F x.val :=
    (reversibleResistanceTransition_congr_interval A hF _ _).symm
  have hI : (fun x : Icc A.source.left A.source.right =>
      ∫ t in (0 : ℝ)..T.val, reversibleResistanceTransition A t.toNNReal f x.val) =
      (fun x : Icc A.source.left A.source.right =>
        ∫ t in Ioc (0 : ℝ) T.val, reversibleResistanceTransition A t.toNNReal f x.val) := by
    funext x
    exact intervalIntegral.integral_of_le T.coe_nonneg
  rw [hI]
  apply continuous_of_dominated
    (fun x => (((reversibleResistanceTransition_continuous_time A x.property hf).comp
      continuous_real_toNNReal).measurable.aestronglyMeasurable.restrict))
    (fun x => Eventually.of_forall (fun t => ?_)) (integrable_const ‖F‖)
    (Eventually.of_forall (fun t => reversibleResistanceTransition_continuous_interval A hf t.toNNReal))
  change ‖reversibleResistanceTransition A t.toNNReal f x.val‖ ≤ ‖F‖
  rw [he]
  exact reversibleResistanceTransition_bound A _ F.norm_coe_le_norm _

theorem reversibleResistanceTransition_zero (A : IntervalMedium)
    (f : ℝ → ℝ) {x : ℝ} (hx : x ∈ Icc A.source.left A.source.right) :
    reversibleResistanceTransition A 0 f x = f x := by
  change (∫ ω : BrownianCompletedSample, f (reversibleResistancePath A x 0 ω)
    ∂brownianCompletedMeasure) = f x
  have he : ∀ᵐ ω ∂brownianCompletedMeasure, reversibleResistancePath A x 0 ω = x :=
    (reversibleResistancePath_martingaleProblem A hx).initial
  calc
    _ = ∫ _ω : BrownianCompletedSample, f x ∂brownianCompletedMeasure :=
      integral_congr_ae (he.mono (fun ω hω => congrArg f hω))
    _ = f x := by simp

end TimeTraps.Probability

end
