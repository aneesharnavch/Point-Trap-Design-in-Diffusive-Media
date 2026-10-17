module

public import TimeTraps.Analysis.GraphConservativeVariationData

@[expose] public section

/-! The actual continuous transition action intertwines the original
edge-length L2 heat evolution. Density of the constructed source inverse
extends the identity to every continuous observable. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph
open scoped NNReal ENNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.continuousState_solution
    (P : GraphShiftedContactOperatorProblem V E) (f : GraphL2Product P.geometry) :
    graphConservativeContinuousStateL P.geometry (P.realizedSolutionL f) = P.operatorInverse f := by
  rw [P.realizedSolutionL_apply, graphConservativeContinuousStateL_sobolev]
  rfl

theorem GraphShiftedContactOperatorProblem.continuousState_feller
    (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0)
    (f : C(GraphRealization P.geometry, ℝ)) :
    graphConservativeContinuousStateL P.geometry (P.realizedFeller t f) =
      P.heatSemigroup t (graphConservativeContinuousStateL P.geometry f) := by
  let J := graphConservativeContinuousStateL P.geometry
  have he : (fun g => J (P.realizedFeller t g)) = (fun g => P.heatSemigroup t (J g)) := by
    apply P.realizedSolutionL_denseRange.equalizer
      (J.continuous.comp (P.realizedFeller t).continuous)
      ((P.heatSemigroup t).continuous.comp J.continuous)
    funext r
    change graphConservativeContinuousStateL P.geometry (P.realizedFeller t (P.realizedSolutionL r)) =
      P.heatSemigroup t (graphConservativeContinuousStateL P.geometry (P.realizedSolutionL r))
    rw [P.realizedFeller_solution, P.continuousState_solution, P.continuousState_solution]
    change P.operatorInverse (Real.exp (t : ℝ) • P.operatorCompactPositiveInverse.heatSemigroup t r) =
      Real.exp (t : ℝ) • P.operatorCompactPositiveInverse.heatSemigroup t (P.operatorInverse r)
    rw [map_smul, P.operatorCompactPositiveInverse.heatSemigroup_commutes]
  exact congrFun he f

end TimeTraps.Analysis
