module

public import TimeTraps.Probability.GraphConservativeStationaryPathMeasure
public import TimeTraps.Probability.GraphConservativeCylinderExpectation
public import TimeTraps.Probability.GraphConservativeStationarySpacedAction
public import TimeTraps.Probability.GraphConservativePathProductReversal

@[expose] public section

/-! Finite-horizon time reversal for the actual continuous graph path
measure with original length initial distribution. The equality of all
Borel path measures is derived from chronological finite observations
and the original symmetric conservative heat operators. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.stationaryPathMeasure_sortedCylinder
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (w : GraphMarkovWord P.geometry) (hw : w.Pairwise (fun a b => a.1 ≤ b.1)) :
    (∫ p, graphMarkovAbsoluteCylinder P.geometry w 0 p ∂P.stationaryPathMeasure h0) =
      ∫ x, P.markovCylinderKernel (graphMarkovDurations 0 w) x ∂P.geometry.lengthMeasure := by
  have hi : Integrable (fun p => graphMarkovAbsoluteCylinder P.geometry w 0 p)
      (P.stationaryPathMeasure h0) := by
    exact ((graphMarkovPathProduct P.geometry w).integrable (P.stationaryPathMeasure h0)).congr
      (Eventually.of_forall (fun p => graphMarkovPathProduct_eq_absolute P.geometry w p))
  rw [P.stationaryPathMeasure_integral h0 hi]
  exact integral_congr_ae (Eventually.of_forall (fun x =>
    P.markovSortedCylinder_expectation h0 x w hw))

theorem GraphShiftedContactOperatorProblem.stationaryPathMeasure_cylinder_reverse
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (w : GraphMarkovWord P.geometry) (T : ℝ≥0)
    (hw : w.Pairwise (fun a b => a.1 ≤ b.1)) (hT : ∀ a ∈ w, a.1 ≤ T) :
    (∫ p, graphMarkovAbsoluteCylinder P.geometry w 0 p ∂P.stationaryPathMeasure h0) =
      ∫ p, graphMarkovAbsoluteCylinder P.geometry
        (w.reverse.map (fun a => (T - a.1, a.2))) 0 p ∂P.stationaryPathMeasure h0 := by
  rw [P.stationaryPathMeasure_sortedCylinder h0 w hw,
    P.stationaryPathMeasure_sortedCylinder h0 _ (graphMarkov_reverse_times_pairwise w T hw)]
  exact P.markovCylinder_length_reverse h0 w T hT

theorem GraphShiftedContactOperatorProblem.stationaryPathMeasure_stop_reverse
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (T : ℝ≥0) :
    (P.stationaryPathMeasure h0).map (graphContinuousPathStop P.geometry T) =
      (P.stationaryPathMeasure h0).map (graphContinuousPathReverse P.geometry T) := by
  apply graphMarkovPath_measure_ext P.geometry
  intro w
  rw [integral_map (graphContinuousPathStop_measurable P.geometry T).aemeasurable
      (graphMarkovPathProduct P.geometry w).continuous.measurable.aestronglyMeasurable,
    integral_map (graphContinuousPathReverse_measurable P.geometry T).aemeasurable
      (graphMarkovPathProduct P.geometry w).continuous.measurable.aestronglyMeasurable]
  simp_rw [graphMarkovPathProduct_stop, graphMarkovPathProduct_reverse]
  exact P.stationaryPathMeasure_cylinder_reverse h0 (graphMarkovWindowWord T w) T
    (graphMarkovWindowWord_pairwise T w) (graphMarkovWindowWord_le T w)

end TimeTraps.Analysis
