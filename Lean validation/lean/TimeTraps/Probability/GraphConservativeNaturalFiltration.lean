module

public import TimeTraps.Probability.GraphConservativeContinuousFiniteLaw
public import TimeTraps.Probability.MarkovProcessHistoryIntegral
public import Mathlib.Probability.Process.Filtration

@[expose] public section

/-! The raw natural filtration of the actual continuous graph paths.
It contains exactly their observations up to the stated time. -/

namespace TimeTraps.Graph

open Set MeasureTheory TimeTraps.Probability
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def graphContinuousNaturalFiltration (G : MetricGraph V E) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (GraphContinuousPath G)) :=
  Filtration.natural (fun t (p : GraphContinuousPath G) => p t)
    (fun t => (continuous_eval_const t).stronglyMeasurable)

theorem graphContinuousNaturalFiltration_eq_history (G : MetricGraph V E) (s : ℝ≥0) :
    graphContinuousNaturalFiltration G s = processHistorySigma (fun t (p : GraphContinuousPath G) => p t) s :=
  Filtration.natural_eq_comap _ _ s

theorem graphContinuousPath_current_measurable (G : MetricGraph V E) (s : ℝ≥0) :
    Measurable[graphContinuousNaturalFiltration G s] (fun p : GraphContinuousPath G => p s) := by
  rw [graphContinuousNaturalFiltration_eq_history]
  exact processHistory_current_measurable _ s

theorem graphContinuousPath_past_measurable (G : MetricGraph V E) {r s : ℝ≥0} (hrs : r ≤ s) :
    Measurable[graphContinuousNaturalFiltration G s] (fun p : GraphContinuousPath G => p r) :=
  (graphContinuousPath_current_measurable G r).mono ((graphContinuousNaturalFiltration G).mono hrs) le_rfl

end TimeTraps.Graph
