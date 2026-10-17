module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentSpatialData

@[expose] public section

/-! The two continuous half-line versions are joined at their common
midpoint. The result is continuous in the spatial level on every sample,
strongly measurable at each level, and agrees almost surely with the
original C([0,T])-valued local time at every fixed level. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedLocalTimeSpatialVersion_stronglyMeasurable (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) :
    StronglyMeasurable (reflectedLocalTimeSpatialVersion L hL D hD x T a) := by
  classical
  have hm : MeasurableSet {ω | reflectedLocalTimeHalfVersion L hL D hD x T false 0 ω =
      reflectedLocalTimeHalfVersion L hL D hD x T true 0 ω} :=
    (reflectedLocalTimeHalfVersion_stronglyMeasurable L hL D hD x T false 0).measurableSet_eq_fun
      (reflectedLocalTimeHalfVersion_stronglyMeasurable L hL D hD x T true 0)
  unfold reflectedLocalTimeSpatialVersion
  apply StronglyMeasurable.ite hm _ stronglyMeasurable_const
  by_cases ha : a.val ≤ L / 2
  · simpa only [if_pos ha] using reflectedLocalTimeHalfVersion_stronglyMeasurable L hL D hD x T false
      (reflectedSpatialLeftInverse L a)
  · simpa only [if_neg ha] using reflectedLocalTimeHalfVersion_stronglyMeasurable L hL D hD x T true
      (reflectedSpatialRightInverse L a)

end TimeTraps.Probability
