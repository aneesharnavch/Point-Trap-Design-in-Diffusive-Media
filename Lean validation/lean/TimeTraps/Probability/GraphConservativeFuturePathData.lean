module

public import TimeTraps.Probability.GraphConservativePathKernel
public import TimeTraps.Probability.GraphConservativeMarkovWordData
public import TimeTraps.Probability.GraphOccupationShiftData

@[expose] public section

/-! Literal future paths at stopping times are measurable random paths;
their initial state is measurable in the actual stopped sigma algebra. -/

namespace TimeTraps.Graph

open Set MeasureTheory ProbabilityTheory TimeTraps.Probability
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E]

theorem graphContinuousPath_stopped_measurable (G : MetricGraph V E)
    {τ : GraphContinuousPath G → ℝ≥0}
    (hτ : IsStoppingTime (graphContinuousNaturalFiltration G) (fun p => (τ p : WithTop ℝ≥0))) :
    Measurable[hτ.measurableSpace] (fun p => p (τ p)) := by
  have ha : StronglyAdapted (graphContinuousNaturalFiltration G)
      (fun t (p : GraphContinuousPath G) => p t) :=
    Filtration.stronglyAdapted_natural _
  exact measurable_stoppedValue
    (ha.isStronglyProgressive_of_continuous (fun p => p.continuous)) hτ

theorem graphContinuousPathShift_stopped_measurable (G : MetricGraph V E)
    {τ : GraphContinuousPath G → ℝ≥0}
    (hτ : IsStoppingTime (graphContinuousNaturalFiltration G) (fun p => (τ p : WithTop ℝ≥0))) :
    Measurable (fun p => graphContinuousPathShift G (τ p) p) := by
  apply (graphContinuousPathSample_measurableEmbedding G).measurable_comp_iff.mp
  apply measurable_pi_lambda
  intro n
  exact (graphContinuousPath_stopped_measurable G (finiteStoppingTime_add hτ _)).mono
    (finiteStoppingTime_add hτ _).measurableSpace_le le_rfl

end TimeTraps.Graph
