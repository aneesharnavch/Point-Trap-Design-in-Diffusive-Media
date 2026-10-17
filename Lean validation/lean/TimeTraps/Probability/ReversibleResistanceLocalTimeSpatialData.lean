module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeBandContinuousOccupation

@[expose] public section

/-! Explicit physical spatial version: compose the continuous reference
local-time field with the resistance coordinate and actual inverse clock.
The compact reference horizon is justified by a deterministic bound. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal Topology

noncomputable def resistanceInteriorCoordinate (A : IntervalMedium)
    (a : Ioo A.source.left A.source.right) : Ioo (0 : ℝ) A.resistanceLength :=
  ⟨A.resistance a.val, reversibleResistance_site_interior A a.property⟩

theorem resistanceInteriorCoordinate_continuous (A : IntervalMedium) :
    Continuous (resistanceInteriorCoordinate A) :=
  (A.resistance_continuous.comp_continuous continuous_subtype_val
    (fun a => Ioo_subset_Icc_self a.property)).subtype_mk _

noncomputable def reversibleResistanceCompactInverseMap (A : IntervalMedium) (x : ℝ)
    (T S : ℝ≥0) (hS : ∀ ω, reversibleResistanceInversePath A x T ω ≤ S)
    (ω : ℕ → ℝ) : C(BrownianCompactTime T, BrownianCompactTime S) :=
  ⟨fun t => reversibleResistanceCompactInverseTime A x T S hS t ω,
    ((reflectedPositiveTimeInversePath_continuous A.resistanceLength A.resistanceLength_pos
      1 (A.resistance x) A.resistanceSpeed A.resistanceSpeed_continuous.continuousOn
        (fun y _ => A.resistanceSpeed_pos y) ω).comp continuous_subtype_val).subtype_mk _⟩

noncomputable def reversibleResistanceLocalTimeSpatialVersion (A : IntervalMedium) (x : ℝ)
    (T S : ℝ≥0) (hS : ∀ ω, reversibleResistanceInversePath A x T ω ≤ S)
    (a : Ioo A.source.left A.source.right) (ω : ℕ → ℝ) : C(BrownianCompactTime T, ℝ) :=
  (reflectedLocalTimeSpatialVersion A.resistanceLength A.resistanceLength_pos 1 zero_lt_one
    (A.resistance x) S (resistanceInteriorCoordinate A a) ω).comp
      (reversibleResistanceCompactInverseMap A x T S hS ω)

theorem reversibleResistanceLocalTimeSpatialVersion_continuous (A : IntervalMedium) (x : ℝ)
    (T S : ℝ≥0) (hS : ∀ ω, reversibleResistanceInversePath A x T ω ≤ S) (ω : ℕ → ℝ) :
    Continuous (fun a => reversibleResistanceLocalTimeSpatialVersion A x T S hS a ω) :=
  ((ContinuousMap.compCLM ℝ ℝ (reversibleResistanceCompactInverseMap A x T S hS ω)).continuous).comp
    ((reflectedLocalTimeSpatialVersion_continuous A.resistanceLength A.resistanceLength_pos
      1 zero_lt_one (A.resistance x) S ω).comp (resistanceInteriorCoordinate_continuous A))

theorem reversibleResistanceLocalTimeSpatialVersion_joint_continuous (A : IntervalMedium) (x : ℝ)
    (T S : ℝ≥0) (hS : ∀ ω, reversibleResistanceInversePath A x T ω ≤ S) (ω : ℕ → ℝ) :
    Continuous (fun p : Ioo A.source.left A.source.right × BrownianCompactTime T =>
      reversibleResistanceLocalTimeSpatialVersion A x T S hS p.1 ω p.2) :=
  continuous_eval.comp (((reversibleResistanceLocalTimeSpatialVersion_continuous A x T S hS ω).comp
    continuous_fst).prodMk continuous_snd)

end TimeTraps.Probability
