module

public import TimeTraps.Probability.GraphConservativeContinuousPathData

@[expose] public section

/-! The Borel space of continuous graph paths over the entire nonnegative
time axis. Countable dense evaluations embed it measurably, so the
coordinate reconstruction defines a genuine path-valued random variable. -/

namespace TimeTraps.Graph

open Set MeasureTheory Topology TopologicalSpace TimeTraps.Probability
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E]

abbrev GraphContinuousPath (G : MetricGraph V E) := C(ℝ≥0, GraphRealization G)

instance graphContinuousPathMeasurableSpace (G : MetricGraph V E) :
    MeasurableSpace (GraphContinuousPath G) := borel _

instance graphContinuousPathBorelSpace (G : MetricGraph V E) :
    BorelSpace (GraphContinuousPath G) := ⟨rfl⟩

noncomputable def graphContinuousPathSample (G : MetricGraph V E) (p : GraphContinuousPath G) :
    ℕ → GraphRealization G := fun n => p (denseSeq ℝ≥0 n)

theorem graphContinuousPathSample_measurableEmbedding (G : MetricGraph V E) :
    MeasurableEmbedding (graphContinuousPathSample G) := by
  have hc : Continuous (graphContinuousPathSample G) :=
    continuous_pi (fun _ => continuous_eval_const _)
  apply hc.measurableEmbedding
  intro p q hpq
  apply ContinuousMap.coe_injective
  exact (denseRange_denseSeq ℝ≥0).equalizer p.continuous q.continuous hpq

variable [Nonempty E]

noncomputable def MetricGraph.reconstructedFullPath (G : MetricGraph V E)
    (x₀ : GraphRealization G) (v : ℕ → GraphRealization G) : GraphContinuousPath G :=
  ⟨G.reconstructedPath x₀ v, G.reconstructedPath_continuous x₀ v⟩

theorem MetricGraph.reconstructedFullPath_measurable (G : MetricGraph V E)
    (x₀ : GraphRealization G) : Measurable (G.reconstructedFullPath x₀) := by
  apply (graphContinuousPathSample_measurableEmbedding G).measurable_comp_iff.mp
  exact measurable_pi_lambda _ (fun n => G.reconstructedPath_measurable x₀ _)

theorem MetricGraph.reconstructedFullPath_eval (G : MetricGraph V E)
    (x₀ : GraphRealization G) (v : ℕ → GraphRealization G) (t : ℝ≥0) :
    G.reconstructedFullPath x₀ v t = G.reconstructedPath x₀ v t := rfl

end TimeTraps.Graph
