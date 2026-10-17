module

public import TimeTraps.Probability.SampledClosedEmbeddingMeasure
public import TimeTraps.Analysis.GraphConservativeCoordinateEmbedding
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

@[expose] public section

/-! Measurable reconstruction into the original compact graph. The
coordinate embedding is proved closed from compactness and injectivity;
each reconstructed path is continuous even on the exceptional set. -/

namespace TimeTraps.Graph

open Set MeasureTheory Topology TimeTraps.Probability
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

omit [Fintype V] in
theorem MetricGraph.smoothCoordinates_closedEmbedding (G : MetricGraph V E) :
    IsClosedEmbedding G.smoothCoordinates :=
  G.smoothCoordinates_continuous.isClosedEmbedding G.smoothCoordinates_injective

noncomputable def MetricGraph.reconstructedPath (G : MetricGraph V E)
    (x₀ : GraphRealization G) (v : ℕ → GraphRealization G) (t : ℝ≥0) : GraphRealization G :=
  sampledEmbeddedPath G.smoothCoordinates_closedEmbedding x₀ v t

theorem MetricGraph.reconstructedPath_continuous (G : MetricGraph V E)
    (x₀ : GraphRealization G) (v : ℕ → GraphRealization G) :
    Continuous (G.reconstructedPath x₀ v) :=
  sampledEmbeddedPath_continuous G.smoothCoordinates_closedEmbedding x₀ v

theorem MetricGraph.reconstructedPath_measurable (G : MetricGraph V E)
    (x₀ : GraphRealization G) (t : ℝ≥0) :
    Measurable (fun v => G.reconstructedPath x₀ v t) := by
  apply sampledEmbeddedPath_measurable
  intro i
  exact (G.smoothCoordinates_continuous.measurable.comp (measurable_pi_apply i)).stronglyMeasurable

theorem MetricGraph.reconstructedPath_jointlyMeasurable (G : MetricGraph V E)
    (x₀ : GraphRealization G) :
    Measurable (fun p : ℝ≥0 × (ℕ → GraphRealization G) => G.reconstructedPath x₀ p.2 p.1) :=
  measurable_uncurry_of_continuous_of_measurable (G.reconstructedPath_continuous x₀)
    (G.reconstructedPath_measurable x₀)

end TimeTraps.Graph
