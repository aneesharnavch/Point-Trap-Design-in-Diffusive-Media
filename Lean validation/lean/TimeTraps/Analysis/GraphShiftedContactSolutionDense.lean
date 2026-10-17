module

public import TimeTraps.Analysis.GraphShiftedContactOperatorInverse
public import TimeTraps.Analysis.CoerciveSolutionDense
public import TimeTraps.Analysis.GraphRealizedSobolevBound
public import TimeTraps.Analysis.GraphRealizedSobolevDense

@[expose] public section

/-! The actual mass-shifted weak source solutions are dense both in the full graph
H1 space and uniformly in continuous functions on the compact graph. -/

namespace TimeTraps.Analysis

open TimeTraps.Graph

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable local instance shiftedGraphSolutionInnerProduct (G : MetricGraph V E) :
    InnerProductSpace ℝ (GraphSobolevSpace G) := Submodule.innerProductSpace (graphSobolevSubspace G)

theorem GraphShiftedContactOperatorProblem.operatorSolution_denseRange (P : GraphShiftedContactOperatorProblem V E) :
    DenseRange P.operatorSolution := by
  apply coerciveSolution_denseRange P.operatorForm ?_ P.operatorForm_symmetric
    (graphSobolevSpaceStateL P.geometry) (graphSobolevSpaceStateL_injective P.geometry)
    P.operatorSolution P.operatorSolution_spec
  obtain ⟨c, hc, hb⟩ := P.operatorForm_coercive
  exact ⟨c, hc, fun u => hb u⟩

noncomputable def GraphShiftedContactOperatorProblem.realizedSolutionL (P : GraphShiftedContactOperatorProblem V E) :
    GraphL2Product P.geometry →L[ℝ] C(GraphRealization P.geometry, ℝ) :=
  (graphRealizedSobolevL P.geometry).comp P.operatorSolution

theorem GraphShiftedContactOperatorProblem.realizedSolutionL_apply (P : GraphShiftedContactOperatorProblem V E)
    (f : GraphL2Product P.geometry) :
    P.realizedSolutionL f = graphRealizedSobolev P.geometry (P.operatorSolution f) := rfl

theorem GraphShiftedContactOperatorProblem.realizedSolutionL_denseRange (P : GraphShiftedContactOperatorProblem V E) :
    DenseRange P.realizedSolutionL :=
  (graphRealizedSobolev_denseRange P.geometry).comp P.operatorSolution_denseRange
    (graphRealizedSobolevL P.geometry).continuous

end TimeTraps.Analysis
