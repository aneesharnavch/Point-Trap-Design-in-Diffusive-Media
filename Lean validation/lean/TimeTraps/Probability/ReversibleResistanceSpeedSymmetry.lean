module

public import TimeTraps.Probability.ReversibleResistancePairingLaplace
public import TimeTraps.Probability.ReversibleNeumannResolventSymmetry
public import TimeTraps.Probability.BoundedContinuousLaplaceUniqueness

@[expose] public section

/-! The actual variable-coefficient transition is symmetric with respect
to the original speed density. Original Neumann resolvent symmetry gives
every discounted pairing; Laplace uniqueness gives each individual time.
Conservation of one then gives speed-measure invariance. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal Topology BoundedContinuousFunction

def reversibleResistanceSpeedWeight (A : IntervalMedium) (f : ℝ →ᵇ ℝ) :
    C(Icc A.source.left A.source.right, ℝ) :=
  ⟨fun x => A.source.density x.val * f x.val,
    (A.source.continuous.comp_continuous continuous_subtype_val (fun x => x.property)).mul
      (f.continuous.comp continuous_subtype_val)⟩

theorem reversibleResistanceTransition_speed_symmetric (A : IntervalMedium)
    (f g : ℝ →ᵇ ℝ) (t : ℝ≥0) :
    (∫ x in A.source.left..A.source.right,
      A.source.density x * f x * reversibleResistanceTransition A t g x) =
      ∫ x in A.source.left..A.source.right,
        A.source.density x * g x * reversibleResistanceTransition A t f x := by
  let wf := reversibleResistanceSpeedWeight A f
  let wg := reversibleResistanceSpeedWeight A g
  have he := boundedContinuous_nonnegativeTime_laplace_unique
    (reversibleResistanceWeightedTransition_continuous A wf g)
    (reversibleResistanceWeightedTransition_continuous A wg f)
    (reversibleResistanceWeightedTransition_bound A wf g)
    (reversibleResistanceWeightedTransition_bound A wg f) (fun α hα => ?_)
  · have ht := congrFun he t
    change (∫ x, A.source.density x.val * f x.val * reversibleResistanceTransition A t g x.val
        ∂reversibleResistanceLengthMeasure A) =
      (∫ x, A.source.density x.val * g x.val * reversibleResistanceTransition A t f x.val
        ∂reversibleResistanceLengthMeasure A) at ht
    exact (reversibleResistanceLengthMeasure_integral A (fun x =>
      A.source.density x * f x * reversibleResistanceTransition A t g x)).symm.trans
        (ht.trans (reversibleResistanceLengthMeasure_integral A (fun x =>
          A.source.density x * g x * reversibleResistanceTransition A t f x)))
  · obtain ⟨H, hH⟩ := reversibleNeumann_resolvent_test_exists A f.continuous.continuousOn hα
    obtain ⟨K, hK⟩ := reversibleNeumann_resolvent_test_exists A g.continuous.continuousOn hα
    rw [reversibleResistanceWeightedTransition_laplace A wf g K hα hK,
      reversibleResistanceWeightedTransition_laplace A wg f H hα hH]
    change (∫ x, A.source.density x.val * f x.val * K.value x.val ∂reversibleResistanceLengthMeasure A) =
      ∫ x, A.source.density x.val * g x.val * H.value x.val ∂reversibleResistanceLengthMeasure A
    exact (reversibleResistanceLengthMeasure_integral A (fun x => A.source.density x * f x * K.value x)).trans
      ((H.resolvent_symmetric K α hH hK).trans
        (reversibleResistanceLengthMeasure_integral A (fun x => A.source.density x * g x * H.value x)).symm)

theorem reversibleResistanceTransition_one (A : IntervalMedium) (t : ℝ≥0) (x : ℝ) :
    reversibleResistanceTransition A t (fun _ => 1) x = 1 := by
  change (∫ _ω : BrownianCompletedSample, (1 : ℝ) ∂brownianCompletedMeasure) = 1
  simp

theorem reversibleResistanceTransition_speed_invariant (A : IntervalMedium)
    (g : ℝ →ᵇ ℝ) (t : ℝ≥0) :
    (∫ x in A.source.left..A.source.right,
      A.source.density x * reversibleResistanceTransition A t g x) =
      ∫ x in A.source.left..A.source.right, A.source.density x * g x := by
  have hs := reversibleResistanceTransition_speed_symmetric A (1 : ℝ →ᵇ ℝ) g t
  change (∫ x in A.source.left..A.source.right,
    A.source.density x * 1 * reversibleResistanceTransition A t g x) =
    ∫ x in A.source.left..A.source.right,
      A.source.density x * g x * reversibleResistanceTransition A t (fun _ => 1) x at hs
  simpa only [mul_one, reversibleResistanceTransition_one] using hs

end TimeTraps.Probability

end
