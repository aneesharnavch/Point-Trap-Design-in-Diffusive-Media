module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeSpatialInverse

@[expose] public section

/-! Measurability of the explicit physical continuous version, including
the jointly measurable dependence on physical site, time and sample. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal Topology

theorem reversibleResistanceLocalTimeSpatialVersion_evaluation_measurable (A : IntervalMedium) (x : ℝ)
    (T S : ℝ≥0) (hS : ∀ ω, reversibleResistanceInversePath A x T ω ≤ S)
    (a : Ioo A.source.left A.source.right) (t : BrownianCompactTime T) :
    Measurable (fun ω => reversibleResistanceLocalTimeSpatialVersion A x T S hS a ω t) := by
  simp only [reversibleResistanceLocalTimeSpatialVersion_apply]
  have hI : Measurable (fun ω => reversibleResistanceCompactInverseTime A x T S hS t ω) :=
    reversibleResistanceCompactInverseTime_measurable A x T S hS t
  exact (continuous_eval.comp_stronglyMeasurable
    ((reflectedLocalTimeSpatialVersion_stronglyMeasurable A.resistanceLength A.resistanceLength_pos
      1 zero_lt_one (A.resistance x) S (resistanceInteriorCoordinate A a)).prodMk
        hI.stronglyMeasurable)).measurable

theorem reversibleResistanceLocalTimeSpatialVersion_stronglyMeasurable (A : IntervalMedium) (x : ℝ)
    (T S : ℝ≥0) (hS : ∀ ω, reversibleResistanceInversePath A x T ω ≤ S)
    (a : Ioo A.source.left A.source.right) :
    StronglyMeasurable (reversibleResistanceLocalTimeSpatialVersion A x T S hS a) :=
  compactPath_stronglyMeasurable _
    (reversibleResistanceLocalTimeSpatialVersion_evaluation_measurable A x T S hS a)

theorem reversibleResistanceLocalTimeSpatialVersion_jointlyMeasurable (A : IntervalMedium) (x : ℝ)
    (T S : ℝ≥0) (hS : ∀ ω, reversibleResistanceInversePath A x T ω ≤ S) :
    Measurable (fun p : (Ioo A.source.left A.source.right × BrownianCompactTime T) × (ℕ → ℝ) =>
      reversibleResistanceLocalTimeSpatialVersion A x T S hS p.1.1 p.2 p.1.2) := by
  apply measurable_uncurry_of_continuous_of_measurable
    (reversibleResistanceLocalTimeSpatialVersion_joint_continuous A x T S hS)
  intro p
  exact reversibleResistanceLocalTimeSpatialVersion_evaluation_measurable A x T S hS p.1 p.2

end TimeTraps.Probability
