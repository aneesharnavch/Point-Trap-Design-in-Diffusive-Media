module

public import TimeTraps.Probability.GraphPhysicalClockPairFunctional
public import TimeTraps.Probability.GraphConservativeStationaryPathMeasure
public import TimeTraps.Probability.GraphPhysicalClockLaplaceStartData

@[expose] public section

/-! The stationary path functional is exactly the original length
integral of the actual clock correlation, including both speed factors. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.physicalClockPairFunctional_integrable
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) {α : ℝ} (hα : 0 ≤ α)
    (f g : C(GraphRealization P.geometry, ℝ)) (T : ℝ≥0) :
    Integrable (graphPhysicalClockPairFunctional P.geometry b hb α f g T)
      (P.stationaryPathMeasure h0) :=
  P.stationaryPathMeasure_bounded_integrable h0
    (graphPhysicalClockPairFunctional_measurable P.geometry b hb α f g T)
    (graphPhysicalClockPairFunctional_bound P.geometry b hb hα f g T)

theorem GraphShiftedContactOperatorProblem.physicalClockPairFunctional_integral
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) {α : ℝ} (hα : 0 ≤ α)
    (f g : C(GraphRealization P.geometry, ℝ)) (T : ℝ≥0) :
    (∫ p, graphPhysicalClockPairFunctional P.geometry b hb α f g T p
      ∂P.stationaryPathMeasure h0) =
      ∫ x, P.geometry.physicalSpeed b x * f x *
        P.physicalClockLaplaceIntegrand h0 b hb α g (T : ℝ) x ∂P.geometry.lengthMeasure := by
  rw [P.stationaryPathMeasure_integral h0
    (P.physicalClockPairFunctional_integrable h0 b hb hα f g T)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  dsimp only [physicalClockLaplaceIntegrand]
  rw [Real.toNNReal_coe, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [P.continuousPathLaw_initial h0 x] with p hp
  dsimp only [graphPhysicalClockPairFunctional]
  rw [hp]
  ring

end TimeTraps.Analysis
