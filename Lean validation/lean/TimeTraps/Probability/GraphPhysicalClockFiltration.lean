module

public import TimeTraps.Probability.GraphPhysicalClockPath

@[expose] public section

/-! The physical filtration on the original path probability space is
the original stopping field at the actual inverse speed clock. -/

namespace TimeTraps.Graph

open Set MeasureTheory ProbabilityTheory TimeTraps.Analysis
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def MetricGraph.physicalFiltration (G : MetricGraph V E) (b : ℝ) (hb : 0 < b) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (GraphContinuousPath G)) where
  seq t := (G.physicalInverseClock_isStoppingTime b hb t).measurableSpace
  mono' s t hst := IsStoppingTime.measurableSpace_mono
    (G.physicalInverseClock_isStoppingTime b hb s)
    (G.physicalInverseClock_isStoppingTime b hb t)
    (fun p => WithTop.coe_le_coe.mpr ((G.physicalClockSpeed b hb p).inverse_strictMono.monotone hst))
  le' t := (G.physicalInverseClock_isStoppingTime b hb t).measurableSpace_le

theorem MetricGraph.physicalFiltration_apply (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (t : ℝ≥0) : G.physicalFiltration b hb t =
      (G.physicalInverseClock_isStoppingTime b hb t).measurableSpace := rfl

theorem MetricGraph.physicalPath_stronglyAdapted (G : MetricGraph V E) (b : ℝ) (hb : 0 < b) :
    StronglyAdapted (G.physicalFiltration b hb) (fun t p => G.physicalPath b hb p t) :=
  fun t => (G.physicalPath_eval_measurable b hb t).stronglyMeasurable

theorem MetricGraph.physicalInverseClock_jointlyMeasurable (G : MetricGraph V E)
    (b : ℝ) (hb : 0 < b) :
    Measurable (fun q : ℝ≥0 × GraphContinuousPath G => G.physicalInverseClock b hb q.1 q.2) :=
  measurable_uncurry_of_continuous_of_measurable
    (fun p => (G.physicalClockSpeed b hb p).inverse_continuous)
    (G.physicalInverseClock_measurable b hb)

end TimeTraps.Graph
