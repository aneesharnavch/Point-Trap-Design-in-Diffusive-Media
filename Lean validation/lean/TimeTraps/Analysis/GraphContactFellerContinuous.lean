module

public import TimeTraps.Analysis.GraphContactFellerSobolev
public import TimeTraps.Analysis.GraphContactFellerSemigroup
public import TimeTraps.Analysis.DenseContractionLimit

@[expose] public section

/-! Strong continuity of the actual graph transition semigroup in the
uniform norm, including time zero. It follows from actual weak-solution
range density and the original L2 heat continuity. -/

namespace TimeTraps.Analysis

open Filter TimeTraps.Graph
open scoped NNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem GraphContactOperatorProblem.realizedFeller_solution_continuous
    (P : GraphContactOperatorProblem V E) (f : GraphL2Product P.geometry) :
    Continuous (fun t : ℝ≥0 => P.realizedFeller t (P.realizedSolutionL f)) := by
  have hc : Continuous (fun t : ℝ≥0 => P.heatSemigroup t f) :=
    P.operatorCompactPositiveInverse.heatSemigroup_strong_continuous f
  have h := P.realizedSolutionL.continuous.comp hc
  exact h.congr (fun t => (P.realizedFeller_solution t f).symm)

theorem GraphContactOperatorProblem.realizedFeller_strong_continuous
    (P : GraphContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ)) :
    Continuous (fun t : ℝ≥0 => P.realizedFeller t f) := by
  apply contraction_denseRange_continuous (fun t g => P.realizedFeller t g)
    P.realizedSolutionL P.realizedSolutionL_denseRange ?_
    P.realizedFeller_solution_continuous f
  intro t g h
  simpa only [dist_eq_norm] using P.realizedFeller_contraction t g h

theorem GraphContactOperatorProblem.realizedFeller_tendsto_zero
    (P : GraphContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ)) :
    Tendsto (fun t : ℝ≥0 => P.realizedFeller t f) (𝓝 0) (𝓝 f) := by
  have h := (P.realizedFeller_strong_continuous f).tendsto 0
  simpa only [P.realizedFeller_zero, ContinuousLinearMap.id_apply] using h

theorem GraphContactOperatorProblem.realizedFeller_uniform_initial
    (P : GraphContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ)) :
    Tendsto (fun t : ℝ≥0 => ‖P.realizedFeller t f - f‖) (𝓝 0) (𝓝 0) := by
  simpa only [sub_self, norm_zero] using (P.realizedFeller_tendsto_zero f).sub_const f |>.norm

end TimeTraps.Analysis
