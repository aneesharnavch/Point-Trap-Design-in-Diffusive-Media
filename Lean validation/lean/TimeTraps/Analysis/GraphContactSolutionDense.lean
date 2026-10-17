module

public import TimeTraps.Analysis.GraphContactOperatorInverse
public import TimeTraps.Analysis.CoerciveSolutionDense
public import TimeTraps.Analysis.GraphRealizedSobolevBound
public import TimeTraps.Analysis.GraphRealizedSobolevDense

@[expose] public section

/-! The original weak source solutions are dense both in the full graph
H1 space and uniformly in continuous functions on the compact graph. -/

namespace TimeTraps.Analysis

open TimeTraps.Graph

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable local instance graphSolutionInnerProduct (G : MetricGraph V E) :
    InnerProductSpace ℝ (GraphSobolevSpace G) := Submodule.innerProductSpace (graphSobolevSubspace G)

theorem GraphContactOperatorProblem.operatorSolution_denseRange (P : GraphContactOperatorProblem V E) :
    DenseRange P.operatorSolution := by
  apply coerciveSolution_denseRange P.operatorForm ?_ P.operatorForm_symmetric
    (graphSobolevSpaceStateL P.geometry) (graphSobolevSpaceStateL_injective P.geometry)
    P.operatorSolution P.operatorSolution_spec
  obtain ⟨c, hc, hb⟩ := P.operatorForm_coercive
  exact ⟨c, hc, fun u => hb u⟩

noncomputable def GraphContactOperatorProblem.realizedSolutionL (P : GraphContactOperatorProblem V E) :
    GraphL2Product P.geometry →L[ℝ] C(GraphRealization P.geometry, ℝ) :=
  (graphRealizedSobolevL P.geometry).comp P.operatorSolution

theorem GraphContactOperatorProblem.realizedSolutionL_apply (P : GraphContactOperatorProblem V E)
    (f : GraphL2Product P.geometry) :
    P.realizedSolutionL f = graphRealizedSobolev P.geometry (P.operatorSolution f) := rfl

theorem GraphContactOperatorProblem.realizedSolutionL_denseRange (P : GraphContactOperatorProblem V E) :
    DenseRange P.realizedSolutionL :=
  (graphRealizedSobolev_denseRange P.geometry).comp P.operatorSolution_denseRange
    (graphRealizedSobolevL P.geometry).continuous

end TimeTraps.Analysis
