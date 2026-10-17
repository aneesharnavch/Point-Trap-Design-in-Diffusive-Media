module

public import TimeTraps.Probability.ContinuousPathPositiveHitting
public import TimeTraps.Probability.ReversibleResistanceCanonicalLocalTimeData
public import TimeTraps.Probability.ReversibleResistanceTimeChangeClockIdentities

@[expose] public section

/-! Measurable strict hitting events for the literal physical process,
and positivity of the actual clock at every positive reference time. -/

namespace TimeTraps.Probability

open Set MeasureTheory TopologicalSpace TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal Topology

theorem reversibleResistanceCanonicalPath_original_measurable (A : IntervalMedium) (x : ℝ) :
    Measurable (fun ω : ℕ → ℝ => reversibleResistanceCanonicalPath A x ω) := by
  apply reversibleNeumannFullPathSample_measurableEmbedding.measurable_comp_iff.mp
  apply measurable_pi_lambda
  intro n
  change Measurable (fun ω : ℕ → ℝ => reversibleResistancePath A x (denseSeq ℝ≥0 n) ω)
  exact (reversibleResistancePath_jointlyMeasurable A x).of_uncurry_left

def reversibleResistancePointHit (A : IntervalMedium) (x a : ℝ) : Set (ℕ → ℝ) :=
  {ω | ∃ t : ℝ≥0, 0 < t ∧ reversibleResistancePath A x t ω = a}

def reversibleResistancePointHitBetween (A : IntervalMedium) (x a : ℝ)
    (S T : ℝ≥0) : Set (ℕ → ℝ) :=
  {ω | ∃ t ∈ Icc S T, reversibleResistancePath A x t ω = a}

theorem reversibleResistancePointHit_measurable (A : IntervalMedium) (x a : ℝ) :
    MeasurableSet (reversibleResistancePointHit A x a) :=
  (reversibleResistanceCanonicalPath_original_measurable A x)
    (continuousPathHitsPositive_measurable a)

theorem reversibleResistancePointHitBetween_measurable (A : IntervalMedium) (x a : ℝ)
    (S T : ℝ≥0) : MeasurableSet (reversibleResistancePointHitBetween A x a S T) :=
  (reversibleResistanceCanonicalPath_original_measurable A x)
    (continuousPathHitsBetween_closed a S T).measurableSet

theorem reversibleResistanceClock_pos (A : IntervalMedium) (x : ℝ)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) {s : ℝ≥0} (hs : 0 < s) :
    0 < reversibleResistanceClock A x s ω := by
  let v := reflectedPositiveTimeSpeed A.resistanceLength A.resistanceLength_pos 1
    (A.resistance x) brownianDyadicPath A.resistanceSpeed
      A.resistanceSpeed_continuous.continuousOn (fun y _ => A.resistanceSpeed_pos y)
        ω hω.continuous
  have he := congrFun (reflectedPositiveTimeClock_eq A.resistanceLength A.resistanceLength_pos 1
    (A.resistance x) brownianDyadicPath A.resistanceSpeed
      A.resistanceSpeed_continuous.continuousOn (fun y _ => A.resistanceSpeed_pos y)
        ω hω.continuous) s
  change reversibleResistanceClock A x s ω = v.clock s at he
  rw [he, ← v.clock_zero]
  exact v.clock_strictMono hs

theorem reversibleResistancePointHit_of_reference_crossing (A : IntervalMedium) (x : ℝ)
    {a : ℝ} (ha : a ∈ Icc A.source.left A.source.right)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω)
    (hcross : reversibleResistanceReference A x 1 ω < A.resistance a ∧
      A.resistance a < reversibleResistanceReference A x 2 ω) :
    ω ∈ reversibleResistancePointHit A x a := by
  have hc : Continuous (fun t => reversibleResistanceReference A x t ω) :=
    (reflectedFold_continuous A.resistanceLength).comp
      (continuous_const.add (continuous_const.mul hω.continuous))
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ≥0) ≤ 2)
    hc.continuousOn ⟨hcross.1.le, hcross.2.le⟩
  refine ⟨reversibleResistanceClock A x s ω,
    reversibleResistanceClock_pos A x hω (lt_of_lt_of_le (by norm_num) hs.1), ?_⟩
  change reversibleResistanceReference A x s ω = A.resistance a at he
  rw [reversibleResistancePath_clock A x hω s, he, A.resistanceInverse_resistance ha]

end TimeTraps.Probability
