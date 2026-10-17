module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeSpatialData

@[expose] public section

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal Topology

theorem reversibleResistanceCompactInverseTime_measurable (A : IntervalMedium) (x : ℝ)
    (T S : ℝ≥0) (hS : ∀ ω, reversibleResistanceInversePath A x T ω ≤ S)
    (t : BrownianCompactTime T) :
    Measurable (fun ω => reversibleResistanceCompactInverseTime A x T S hS t ω) :=
  (reversibleResistanceInversePath_measurable A x t.val).subtype_mk

theorem reversibleResistanceLocalTimeSpatialVersion_apply (A : IntervalMedium) (x : ℝ)
    (T S : ℝ≥0) (hS : ∀ ω, reversibleResistanceInversePath A x T ω ≤ S)
    (a : Ioo A.source.left A.source.right) (ω : ℕ → ℝ) (t : BrownianCompactTime T) :
    reversibleResistanceLocalTimeSpatialVersion A x T S hS a ω t =
      reflectedLocalTimeSpatialVersion A.resistanceLength A.resistanceLength_pos
        1 zero_lt_one (A.resistance x) S (resistanceInteriorCoordinate A a) ω
          (reversibleResistanceCompactInverseTime A x T S hS t ω) := rfl

end TimeTraps.Probability
