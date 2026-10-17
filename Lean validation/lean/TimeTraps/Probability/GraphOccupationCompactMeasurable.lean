module

public import TimeTraps.Probability.GraphOccupationCompactBound

@[expose] public section

/-! The genuine compact-time occupation curve is a strongly measurable
random variable in the uniform-norm continuous-function space. Dense
compact evaluations recover its Borel measurability. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E]

theorem graphOccupationCompactPath_stronglyMeasurable (G : MetricGraph V E)
    (f : C(GraphRealization G, ℝ)) (T : ℝ≥0) :
    StronglyMeasurable (graphOccupationCompactPath G f T) := by
  let : Nonempty (Icc (0 : ℝ≥0) T) := ⟨⟨0, by simp⟩⟩
  apply compactPath_stronglyMeasurable
  intro t
  exact (graphOccupation_stronglyMeasurable G f t.val).measurable

theorem graphOccupationCompactPath_norm_measurable (G : MetricGraph V E)
    (f : C(GraphRealization G, ℝ)) (T : ℝ≥0) :
    Measurable (fun p => ‖graphOccupationCompactPath G f T p‖) :=
  (graphOccupationCompactPath_stronglyMeasurable G f T).norm.measurable

theorem graphOccupationCompactPath_sub_norm_measurable (G : MetricGraph V E)
    (f g : C(GraphRealization G, ℝ)) (T : ℝ≥0) :
    Measurable (fun p => ‖graphOccupationCompactPath G f T p - graphOccupationCompactPath G g T p‖) :=
  ((graphOccupationCompactPath_stronglyMeasurable G f T).sub
    (graphOccupationCompactPath_stronglyMeasurable G g T)).norm.measurable

end TimeTraps.Analysis
