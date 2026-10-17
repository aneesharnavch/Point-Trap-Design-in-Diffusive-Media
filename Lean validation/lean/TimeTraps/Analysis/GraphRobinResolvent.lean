module

public import TimeTraps.Analysis.GraphRobinResolventForcing
public import TimeTraps.Analysis.GraphHeatResolventBorel

@[expose] public section

/-! Direct source-faithful Robin resolvent decomposition on the original
metric graph: the conservative resolvent of u+rho minus the original
vertex reaction resolvents. Rho is the actual bounded Borel physical
speed, with an arbitrary positive value at vertices. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.robinWeak_resolvent_borel
    (P : GraphShiftedContactOperatorProblem V E) (hP : ∀ v, P.strength v = 0)
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (hu : WeakGraphEquation P.geometry κ U u)
    (b : ℝ) (hb : 0 < b) (x : GraphRealization P.geometry) :
    graphRealizedSobolev P.geometry (graphSobolevSpaceOfEnergy P.geometry hu.energy) x =
      P.borelResolventOne
        (fun y => graphRealizedSobolev P.geometry (graphSobolevSpaceOfEnergy P.geometry hu.energy) y +
          P.geometry.physicalSpeed b y) x -
      ∑ z, κ z * U z * P.pointLocalTimeDiscountedPotential (P.geometry.vertexPoint z) 1 x := by
  obtain ⟨C, hC⟩ := graphRobinResolventForcing_bounded P.geometry hu.energy b hb
  rw [P.borelResolventOne_eq_solution (graphRobinResolventForcing_measurable P.geometry hu.energy b)
    hC (graphSobolevSpaceStateL P.geometry (graphSobolevSpaceOfEnergy P.geometry hu.energy) +
      graphPhysicalSourceL2 P.geometry) (graphRobinResolventForcing_ae P.geometry hu.energy b)]
  exact P.robinWeak_resolvent_pointwise hP hu x

theorem GraphShiftedContactOperatorProblem.robinWeak_resolvent_borel_edge
    (P : GraphShiftedContactOperatorProblem V E) (hP : ∀ v, P.strength v = 0)
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (hu : WeakGraphEquation P.geometry κ U u)
    (b : ℝ) (hb : 0 < b) (e : E) (x : Icc (0 : ℝ) (P.geometry.length e)) :
    u e x.val =
      P.borelResolventOne
        (fun y => graphRealizedSobolev P.geometry (graphSobolevSpaceOfEnergy P.geometry hu.energy) y +
          P.geometry.physicalSpeed b y) (P.geometry.edgePoint e x) -
      ∑ z, κ z * U z * P.pointLocalTimeDiscountedPotential (P.geometry.vertexPoint z) 1
        (P.geometry.edgePoint e x) := by
  simpa only [graphRealizedSobolev_ofEnergy] using
    P.robinWeak_resolvent_borel hP hu b hb (P.geometry.edgePoint e x)

theorem GraphShiftedContactOperatorProblem.robinWeak_resolvent_borel_vertex
    (P : GraphShiftedContactOperatorProblem V E) (hP : ∀ v, P.strength v = 0)
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (hu : WeakGraphEquation P.geometry κ U u)
    (b : ℝ) (hb : 0 < b) (v : V) :
    U v =
      P.borelResolventOne
        (fun y => graphRealizedSobolev P.geometry (graphSobolevSpaceOfEnergy P.geometry hu.energy) y +
          P.geometry.physicalSpeed b y) (P.geometry.vertexPoint v) -
      ∑ z, κ z * U z * P.pointLocalTimeDiscountedPotential (P.geometry.vertexPoint z) 1
        (P.geometry.vertexPoint v) := by
  simpa only [graphRealizedSobolev_vertex, graphSobolevSpaceOfEnergy_node] using
    P.robinWeak_resolvent_borel hP hu b hb (P.geometry.vertexPoint v)

end TimeTraps.Analysis
