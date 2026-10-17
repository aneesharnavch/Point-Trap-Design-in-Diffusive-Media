module

public import TimeTraps.Probability.ReversibleResistancePhysicalBandData

@[expose] public section

/-! Every singleton has zero ordinary occupation time for the physical
path, on one event for every finite horizon and every level. Nonzero
local-time contact is therefore distinct from ordinary residence time. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

theorem reversibleResistanceOccupationMeasure_singleton_ae (A : IntervalMedium) (x : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ (T : ℝ≥0) (a : ℝ),
      brownianOccupationMeasure (reversibleResistancePath A x) T ω {a} = 0 := by
  filter_upwards [reversibleResistanceOccupationDensity_measure A x] with ω hω T a
  rw [← hω T]
  exact measure_singleton a

theorem reversibleResistancePath_zero_time_at_points_ae (A : IntervalMedium) (x : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ (T : ℝ≥0) (a : ℝ),
      (volume.restrict (Ioc (0 : ℝ) T.val))
        {t : ℝ | reversibleResistancePath A x t.toNNReal ω = a} = 0 := by
  filter_upwards [reversibleResistanceOccupationMeasure_singleton_ae A x] with ω hω T a
  have he := hω T a
  change ((volume.restrict (Ioc (0 : ℝ) T.val)).map
    (fun t => reversibleResistancePath A x t.toNNReal ω)) {a} = 0 at he
  rw [Measure.map_apply
    (brownianOccupationMeasure_path_measurable (reversibleResistancePath_jointlyMeasurable A x) ω)
    (measurableSet_singleton a)] at he
  simpa only [Set.preimage, Set.mem_singleton_iff] using he

end TimeTraps.Probability
