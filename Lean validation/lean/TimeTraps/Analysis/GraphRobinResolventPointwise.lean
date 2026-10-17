module

public import TimeTraps.Analysis.GraphRobinResolventForm
public import TimeTraps.Analysis.GraphHeatPointResolventL2

@[expose] public section

/-! The original Robin weak solution decomposes pointwise into the
conservative resolvent of its mass plus physical edge source, minus the
original finite vertex reaction potentials. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter InnerProductSpace

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.robinWeak_resolvent_pointwise
    (P : GraphShiftedContactOperatorProblem V E) (hP : ∀ v, P.strength v = 0)
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (hu : WeakGraphEquation P.geometry κ U u)
    (x : GraphRealization P.geometry) :
    graphRealizedSobolev P.geometry (graphSobolevSpaceOfEnergy P.geometry hu.energy) x =
      P.realizedSolutionL (graphSobolevSpaceStateL P.geometry (graphSobolevSpaceOfEnergy P.geometry hu.energy) +
        graphPhysicalSourceL2 P.geometry) x -
      ∑ z, κ z * U z * P.pointLocalTimeDiscountedPotential (P.geometry.vertexPoint z) 1 x := by
  let L : GraphSobolevSpace P.geometry →L[ℝ] ℝ :=
    (ContinuousMap.evalCLM ℝ x).comp (graphRealizedSobolevL P.geometry)
  have h := congrArg L (P.robinWeak_resolvent_decomposition hP hu)
  simp only [map_sub, map_sum, map_smul, smul_eq_mul] at h
  have hL (w : GraphSobolevSpace P.geometry) : L w = graphRealizedSobolev P.geometry w x := rfl
  simp only [hL] at h
  change _ = P.realizedSolutionL _ x -
    ∑ z, κ z * U z * graphRealizedSobolev P.geometry
      (P.pointResolventSolution (P.geometry.vertexPoint z)) x at h
  simpa only [P.pointLocalTimeDiscountedPotential_one_eq] using h

theorem GraphShiftedContactOperatorProblem.robinWeak_resolvent_edge
    (P : GraphShiftedContactOperatorProblem V E) (hP : ∀ v, P.strength v = 0)
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (hu : WeakGraphEquation P.geometry κ U u)
    (e : E) (x : Icc (0 : ℝ) (P.geometry.length e)) :
    u e x.val =
      P.realizedSolutionL (graphSobolevSpaceStateL P.geometry (graphSobolevSpaceOfEnergy P.geometry hu.energy) +
        graphPhysicalSourceL2 P.geometry) (P.geometry.edgePoint e x) -
      ∑ z, κ z * U z * P.pointLocalTimeDiscountedPotential (P.geometry.vertexPoint z) 1
        (P.geometry.edgePoint e x) := by
  simpa only [graphRealizedSobolev_ofEnergy] using
    P.robinWeak_resolvent_pointwise hP hu (P.geometry.edgePoint e x)

theorem GraphShiftedContactOperatorProblem.robinWeak_resolvent_vertex
    (P : GraphShiftedContactOperatorProblem V E) (hP : ∀ v, P.strength v = 0)
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (hu : WeakGraphEquation P.geometry κ U u) (v : V) :
    U v =
      P.realizedSolutionL (graphSobolevSpaceStateL P.geometry (graphSobolevSpaceOfEnergy P.geometry hu.energy) +
        graphPhysicalSourceL2 P.geometry) (P.geometry.vertexPoint v) -
      ∑ z, κ z * U z * P.pointLocalTimeDiscountedPotential (P.geometry.vertexPoint z) 1
        (P.geometry.vertexPoint v) := by
  simpa only [graphRealizedSobolev_vertex, graphSobolevSpaceOfEnergy_node] using
    P.robinWeak_resolvent_pointwise hP hu (P.geometry.vertexPoint v)

end TimeTraps.Analysis
