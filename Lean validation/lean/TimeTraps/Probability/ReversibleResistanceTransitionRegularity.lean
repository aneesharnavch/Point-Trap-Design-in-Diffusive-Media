module

public import TimeTraps.Probability.ReversibleNeumannMartingaleProblemLaplace

@[expose] public section

/-! The actual resistance-process transition expectation is measurable
in the initial physical point and continuous in time on continuous tests.
These properties concern the constructed process and are derived directly. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal Topology

theorem reversibleResistanceTransition_measurable_interval (A : IntervalMedium) (t : ℝ≥0)
    {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun x : Icc A.source.left A.source.right => reversibleResistanceTransition A t f x.val) := by
  let R : Icc A.source.left A.source.right → Icc (0 : ℝ) A.resistanceLength :=
    fun x => ⟨A.resistance x.val, A.resistance_mem x.property⟩
  have hR : Measurable R := A.resistance_continuous.domRestrict.measurable.subtype_mk
  have hm := (reflectedTimeChangedOperator_measurable_interval A.resistanceLength A.resistanceLength_pos
    1 A.resistanceSpeed A.resistanceSpeed_continuous.continuousOn (fun y _ => A.resistanceSpeed_pos y)
      t (hf.comp A.resistanceInverse_continuous.measurable)).comp hR
  have he : (fun x : Icc A.source.left A.source.right => reversibleResistanceTransition A t f x.val) =
      (fun y : Icc (0 : ℝ) A.resistanceLength => reflectedTimeChangedOperator
        A.resistanceLength 1 A.resistanceSpeed t (f ∘ A.resistanceInverse) y.val) ∘ R := by
    funext x
    exact reversibleResistanceTransition_reference A t f x.val
  exact he.symm ▸ hm

theorem reversibleResistanceTransition_continuous_time (A : IntervalMedium) {x : ℝ}
    (hx : x ∈ Icc A.source.left A.source.right) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc A.source.left A.source.right)) :
    Continuous (fun t : ℝ≥0 => reversibleResistanceTransition A t f x) :=
  ReversibleNeumannMartingaleProblem.observation_mean_continuous (Ω := BrownianCompletedSample)
    (X := fun t (ω : BrownianCompletedSample) => reversibleResistancePath A x t ω)
    (reversibleResistancePath_martingaleProblem A hx) hf

theorem reversibleResistanceTransition_jointlyMeasurable_interval (A : IntervalMedium)
    {f : ℝ → ℝ} (hf : Continuous f) :
    Measurable (fun p : ℝ≥0 × Icc A.source.left A.source.right =>
      reversibleResistanceTransition A p.1 f p.2.val) :=
  measurable_uncurry_of_continuous_of_measurable
    (fun x => reversibleResistanceTransition_continuous_time A x.property hf.continuousOn)
    (fun t => reversibleResistanceTransition_measurable_interval A t hf.measurable)

end TimeTraps.Probability

end
