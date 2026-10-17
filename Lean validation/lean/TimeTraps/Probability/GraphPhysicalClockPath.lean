module

public import TimeTraps.Probability.GraphPhysicalClockAdapted

@[expose] public section

/-! The physical trajectory is the original continuous graph path at the
true inverse speed clock. It is a measurable continuous-path transform
and is adapted at those bounded inverse stopping times. -/

namespace TimeTraps.Graph

open Set MeasureTheory ProbabilityTheory TimeTraps.Analysis
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def MetricGraph.physicalPath (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (p : GraphContinuousPath G) : GraphContinuousPath G :=
  ⟨fun t => p (G.physicalInverseClock b hb t p),
    p.continuous.comp (G.physicalClockSpeed b hb p).inverse_continuous⟩

theorem MetricGraph.physicalPath_apply (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (p : GraphContinuousPath G) (t : ℝ≥0) :
    G.physicalPath b hb p t = p (G.physicalInverseClock b hb t p) := rfl

theorem MetricGraph.physicalPath_zero (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (p : GraphContinuousPath G) : G.physicalPath b hb p 0 = p 0 := by
  change p ((G.physicalClockSpeed b hb p).inverse 0) = p 0
  rw [(G.physicalClockSpeed b hb p).inverse_zero]

theorem MetricGraph.physicalPath_at_clock (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (p : GraphContinuousPath G) (t : ℝ≥0) :
    G.physicalPath b hb p (G.physicalClock b hb t p) = p t := by
  rw [G.physicalPath_apply, G.physicalInverseClock_clock]

theorem MetricGraph.physicalPath_eval_measurable (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (t : ℝ≥0) :
    Measurable[(G.physicalInverseClock_isStoppingTime b hb t).measurableSpace]
      (fun p => G.physicalPath b hb p t) :=
  graphContinuousPath_stopped_measurable G (G.physicalInverseClock_isStoppingTime b hb t)

theorem MetricGraph.physicalPath_measurable (G : MetricGraph V E) (b : ℝ) (hb : 0 < b) :
    Measurable (G.physicalPath b hb) := by
  apply (graphContinuousPathSample_measurableEmbedding G).measurable_comp_iff.mp
  apply measurable_pi_lambda
  intro n
  exact (G.physicalPath_eval_measurable b hb _).mono
    (G.physicalInverseClock_isStoppingTime b hb _).measurableSpace_le le_rfl

theorem MetricGraph.physicalPath_jointlyMeasurable (G : MetricGraph V E) (b : ℝ) (hb : 0 < b) :
    Measurable (fun q : ℝ≥0 × GraphContinuousPath G => G.physicalPath b hb q.2 q.1) :=
  continuous_eval.measurable.comp ((G.physicalPath_measurable b hb).comp measurable_snd |>.prodMk measurable_fst)

end TimeTraps.Graph
