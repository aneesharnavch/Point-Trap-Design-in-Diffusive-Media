module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeBandContinuousTransport

@[expose] public section

/-! A single event identifies every sufficiently interior physical band,
at every time in a compact horizon, with the speed-mass weighted average
of the continuous reference field evaluated at the actual inverse clock. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal Topology

noncomputable def reversibleResistanceCompactInverseTime (A : IntervalMedium) (x : ℝ)
    (T S : ℝ≥0) (hS : ∀ ω, reversibleResistanceInversePath A x T ω ≤ S)
    (t : BrownianCompactTime T) (ω : ℕ → ℝ) : BrownianCompactTime S :=
  ⟨reversibleResistanceInversePath A x t.val ω,
    ⟨zero_le, (reversibleResistanceInversePath_monotone A x ω t.property.2).trans (hS ω)⟩⟩

theorem reversibleResistancePhysicalBand_continuous_average_ae (A : IntervalMedium) (x : ℝ)
    (T S : ℝ≥0) (hS : ∀ ω, reversibleResistanceInversePath A x T ω ≤ S)
    (l r : ℝ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < A.resistanceLength) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ a h : ℝ, 0 < h →
      (Ioo (a - h) (a + h) ⊆ Ioo A.source.left A.source.right) →
      (∀ z, |z - a| < h → A.resistance z ∈ Icc l r) →
      ∀ t : BrownianCompactTime T,
        reversibleResistancePhysicalOccupationBand A x a h t.val ω =
          resistancePhysicalWeightedAverage A
            (fun y => reflectedLocalTimeWindowVersion A.resistanceLength A.resistanceLength_pos
              1 zero_lt_one (A.resistance x) S l r hl hlr hr y ω) a h
            (reversibleResistanceCompactInverseTime A x T S hS t ω) := by
  filter_upwards [resistanceBandReferenceTest_time_substitution A x,
    reflectedLocalTimeWindow_occupation_all_tests_times_ae A.resistanceLength A.resistanceLength_pos
      1 zero_lt_one (A.resistance x) S l r hl hlr hr] with ω hsub hocc
  intro a h hh hband hw t
  let s := reversibleResistanceCompactInverseTime A x T S hS t ω
  obtain ⟨C, hb⟩ := resistanceBandReferenceTest_bound A a h
  have hq := resistanceBandReferenceTest_measurable A a h
  have he := hocc (resistanceBandReferenceTest A a h) hq C hb
    (resistanceBandReferenceTest_support A a h l r hw) s
  have hV := reflectedLocalTimeWindowVersion_continuous A.resistanceLength A.resistanceLength_pos
    1 zero_lt_one (A.resistance x) S l r hl hlr hr ω
  change _ = resistancePhysicalWeightedAverage A
    (fun y => reflectedLocalTimeWindowVersion A.resistanceLength A.resistanceLength_pos
      1 zero_lt_one (A.resistance x) S l r hl hlr hr y ω) a h s
  rw [resistancePhysicalWeightedAverage_apply A S hV a hh
    (fun z hz => Ioo_subset_Icc_self (hband hz)) s]
  unfold reversibleResistancePhysicalOccupationBand
  congr 1
  calc
    _ = brownianItoDrift (reversibleResistanceReference A x)
        (resistanceBandReferenceTest A a h) s.val ω := hsub a h t.val
    _ = reflectedLocalTimeWindowTestPath A.resistanceLength A.resistanceLength_pos
        1 zero_lt_one (A.resistance x) S l r hl hlr hr (resistanceBandReferenceTest A a h) ω s := he
    _ = ∫ y in Icc l r, resistanceBandReferenceTest A a h y *
        reflectedLocalTimeWindowVersion A.resistanceLength A.resistanceLength_pos
          1 zero_lt_one (A.resistance x) S l r hl hlr hr y ω s :=
      reflectedLocalTimeWindowTestPath_apply A.resistanceLength A.resistanceLength_pos
        1 zero_lt_one (A.resistance x) S l r hl hlr hr hq hb ω s
    _ = _ := resistanceBandReferenceTest_window_integral A a h l r hw hband _

end TimeTraps.Probability
