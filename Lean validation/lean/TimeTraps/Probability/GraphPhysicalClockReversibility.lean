module

public import TimeTraps.Probability.GraphPhysicalClockPairStationary
public import TimeTraps.Probability.GraphConservativeStationaryReversal

@[expose] public section

/-! Reversal of the genuine stationary conservative path measure
makes the actual physical clock correlation symmetric. The original
Borel speed appears at both endpoints and throughout the clock. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.physicalClockPairFunctional_symmetric
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (α : ℝ)
    (f g : C(GraphRealization P.geometry, ℝ)) (T : ℝ≥0) :
    (∫ p, graphPhysicalClockPairFunctional P.geometry b hb α f g T p
      ∂P.stationaryPathMeasure h0) =
    ∫ p, graphPhysicalClockPairFunctional P.geometry b hb α g f T p
      ∂P.stationaryPathMeasure h0 := by
  have hm := graphPhysicalClockPairFunctional_measurable P.geometry b hb α f g T
  have hS := integral_map (μ := P.stationaryPathMeasure h0) (graphContinuousPathStop_measurable P.geometry T).aemeasurable
    hm.aestronglyMeasurable
  have hR := integral_map (μ := P.stationaryPathMeasure h0) (graphContinuousPathReverse_measurable P.geometry T).aemeasurable
    hm.aestronglyMeasurable
  calc
    _ = ∫ p, graphPhysicalClockPairFunctional P.geometry b hb α f g T p
        ∂(P.stationaryPathMeasure h0).map (graphContinuousPathStop P.geometry T) := by
      simpa only [graphPhysicalClockPairFunctional_stop] using hS.symm
    _ = ∫ p, graphPhysicalClockPairFunctional P.geometry b hb α f g T p
        ∂(P.stationaryPathMeasure h0).map (graphContinuousPathReverse P.geometry T) := by
      rw [P.stationaryPathMeasure_stop_reverse h0 T]
    _ = _ := by
      simpa only [graphPhysicalClockPairFunctional_reverse] using hR

theorem GraphShiftedContactOperatorProblem.physicalClockLaplaceIntegrand_symmetric
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) {α : ℝ} (hα : 0 ≤ α)
    (f g : C(GraphRealization P.geometry, ℝ)) (r : ℝ) :
    (∫ x, P.geometry.physicalSpeed b x * f x *
      P.physicalClockLaplaceIntegrand h0 b hb α g r x ∂P.geometry.lengthMeasure) =
      ∫ x, P.geometry.physicalSpeed b x * g x *
        P.physicalClockLaplaceIntegrand h0 b hb α f r x ∂P.geometry.lengthMeasure := by
  calc
    _ = ∫ p, graphPhysicalClockPairFunctional P.geometry b hb α f g r.toNNReal p
        ∂P.stationaryPathMeasure h0 := by
      simpa only [physicalClockLaplaceIntegrand, Real.toNNReal_coe] using
        (P.physicalClockPairFunctional_integral h0 b hb hα f g r.toNNReal).symm
    _ = ∫ p, graphPhysicalClockPairFunctional P.geometry b hb α g f r.toNNReal p
        ∂P.stationaryPathMeasure h0 :=
      P.physicalClockPairFunctional_symmetric h0 b hb α f g r.toNNReal
    _ = _ := by
      simpa only [physicalClockLaplaceIntegrand, Real.toNNReal_coe] using
        P.physicalClockPairFunctional_integral h0 b hb hα g f r.toNNReal

end TimeTraps.Analysis
