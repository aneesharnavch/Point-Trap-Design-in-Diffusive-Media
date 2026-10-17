module

public import TimeTraps.Probability.ReversibleResistancePointHittingData
public import TimeTraps.Probability.ReflectedBrownianCrossing

@[expose] public section

/-! Every interior site of the actual reversible reflected diffusion is
hit with positive probability at a strictly positive time, including when
the initial point is that site. The event is Borel and a deterministic
compact time window bounded away from zero already has positive mass. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal Topology

theorem reversibleResistancePointHit_probability_pos (A : IntervalMedium) (x : ℝ)
    {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right) :
    0 < brownianDyadicMeasure (reversibleResistancePointHit A x a) := by
  have hac := Ioo_subset_Icc_self ha
  have haR : A.resistance a ∈ Ioo 0 A.resistanceLength := by
    constructor
    · have h := A.resistance_strictMono (left_mem_Icc.mpr A.source.increasing.le) hac ha.1
      rwa [A.resistance_left] at h
    · have h := A.resistance_strictMono hac (right_mem_Icc.mpr A.source.increasing.le) ha.2
      rwa [A.resistance_right] at h
  have hp := foldedTrajectory_crossing_probability_pos A.resistanceLength A.resistanceLength_pos
    1 (by norm_num) (A.resistance x) haR
  apply hp.trans_le
  apply measure_mono_ae
  filter_upwards [brownianDyadic_regular_ae] with ω hω
  intro hcross
  exact reversibleResistancePointHit_of_reference_crossing A x hac hω hcross

theorem reversibleResistancePointHit_compact_probability_pos (A : IntervalMedium) (x : ℝ)
    {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right) :
    ∃ S T : ℝ≥0, 0 < S ∧ S ≤ T ∧
      MeasurableSet (reversibleResistancePointHitBetween A x a S T) ∧
      0 < brownianDyadicMeasure (reversibleResistancePointHitBetween A x a S T) := by
  obtain ⟨n,m,hm⟩ := continuousPathHitsPositive_compact brownianDyadicMeasure
    (fun ω : ℕ → ℝ => reversibleResistanceCanonicalPath A x ω) a
      (reversibleResistancePointHit_probability_pos A x ha)
  change 0 < brownianDyadicMeasure
    (reversibleResistancePointHitBetween A x a (1 / (n+1 : ℝ≥0)) m) at hm
  obtain ⟨ω,t,ht,_he⟩ := nonempty_of_measure_ne_zero hm.ne'
  exact ⟨1 / (n+1 : ℝ≥0),m,by positivity,ht.1.trans ht.2,
    reversibleResistancePointHitBetween_measurable A x a _ _,hm⟩

theorem reversibleResistancePoint_nonpolar (A : IntervalMedium)
    {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right) :
    ∀ x ∈ Icc A.source.left A.source.right,
      MeasurableSet {ω : ℕ → ℝ | ∃ t : ℝ≥0, 0 < t ∧ reversibleResistancePath A x t ω = a} ∧
      brownianDyadicMeasure
        {ω : ℕ → ℝ | ∃ t : ℝ≥0, 0 < t ∧ reversibleResistancePath A x t ω = a} ≠ 0 := by
  intro x _hx
  exact ⟨reversibleResistancePointHit_measurable A x a,
    (reversibleResistancePointHit_probability_pos A x ha).ne'⟩

end TimeTraps.Probability
