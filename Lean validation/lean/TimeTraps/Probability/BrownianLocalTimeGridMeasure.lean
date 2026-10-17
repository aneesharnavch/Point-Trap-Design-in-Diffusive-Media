module

public import TimeTraps.Probability.BrownianLocalTimeGridEvent
public import TimeTraps.Probability.BrownianLocalTimeMeasureTests

@[expose] public section

/-! The countably sampled jointly measurable version has the actual
occupation density measures on one full-probability event. The same
event can be intersected with the proved spatial grid-order event. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

theorem brownianDyadicLocalTimeJointVersion_level_sections_ae (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      (fun a => brownianDyadicLocalTimeJointVersion a T ω) =ᵐ[volume]
        (fun a => brownianDyadicLocalTimeLevelVersion T a ω) := by
  apply (Measure.ae_ae_comm (μ := volume) (ν := brownianDyadicMeasure)
    (p := fun a ω => brownianDyadicLocalTimeJointVersion a T ω =
      brownianDyadicLocalTimeLevelVersion T a ω)
    (measurableSet_eq_fun (brownianDyadicLocalTimeJointVersion_timeSlice_measurable T)
      (brownianDyadicLocalTimeLevelVersion_jointlyMeasurable T))).mp
  exact Eventually.of_forall (fun a => brownianLocalTimeJointVersion_levelVersion_ae
    brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable a T)

theorem brownianDyadicLocalTimeJointVersion_measure_eq_ae (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      volume.withDensity (fun a => ENNReal.ofReal (brownianDyadicLocalTimeJointVersion a T ω)) =
        brownianOccupationMeasure brownianDyadicPath T ω := by
  filter_upwards [brownianDyadicLocalTimeJointVersion_level_sections_ae T,
    brownianDyadicLocalTimeLevelMeasure_eq_ae T] with ω he ho
  exact (withDensity_congr_ae (he.fun_comp ENNReal.ofReal)).trans ho

theorem brownianLocalTimeGridOccupation_ae :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ i : ℕ,
      volume.withDensity (fun a => ENNReal.ofReal
        (brownianDyadicLocalTimeJointVersion a (brownianDyadicTime i) ω)) =
          brownianOccupationMeasure brownianDyadicPath (brownianDyadicTime i) ω :=
  ae_all_iff.mpr (fun i => brownianDyadicLocalTimeJointVersion_measure_eq_ae (brownianDyadicTime i))

end TimeTraps.Probability
