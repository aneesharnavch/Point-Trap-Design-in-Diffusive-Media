module

public import TimeTraps.Analysis.GraphConservativeMomentCoordinateData

@[expose] public section

/-! Uniform actual transition moments for every scalar component of the
separating graph coordinates. The operator memberships and all constants
are now discharged from the original continuous conductance. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph
open scoped NNReal ENNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.coordinate_transition_moments
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (T : ℝ≥0) (x : GraphRealization P.geometry) :
    (∫ y, (φ (P.geometry.smoothCoordinates y) - φ (P.geometry.smoothCoordinates x)) ^ 2
      ∂P.realizedTransition T x) ≤ P.geometry.coordinateSecondMomentConstant φ * T.val ∧
    (∫ y, (φ (P.geometry.smoothCoordinates y) - φ (P.geometry.smoothCoordinates x)) ^ 4
      ∂P.realizedTransition T x) ≤ P.geometry.coordinateSecondMomentConstant φ *
        P.geometry.coordinateFourthGeneratorConstant φ * T.val ^ 2 / 2 := by
  apply P.realizedTransition_coordinate_moments hκ (P.geometry.coordinateTest φ)
    (fun z => P.geometry.coordinateSquareGenerator φ (P.geometry.coordinateTest φ z))
    (fun z => P.geometry.coordinateFourthGenerator φ (P.geometry.coordinateTest φ z))
  · intro z
    simpa only [map_neg, graphConservativeCenteredPower, MetricGraph.coordinateCentered] using
      P.coordinate_square_operator_graph hκ φ (P.geometry.coordinateTest φ z)
  · intro z
    simpa only [map_neg, graphConservativeCenteredPower, MetricGraph.coordinateCentered] using
      P.coordinate_fourth_operator_graph hκ φ (P.geometry.coordinateTest φ z)
  · exact (P.geometry.coordinateMomentConstants_nonneg φ).2
  · exact P.geometry.coordinateSquareGenerator_bound φ
  · exact P.geometry.coordinateFourthGenerator_bound φ

theorem GraphShiftedContactOperatorProblem.coordinate_transition_fourth_bound
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (x : GraphRealization P.geometry),
      Integrable (fun y => (φ (P.geometry.smoothCoordinates y) - φ (P.geometry.smoothCoordinates x)) ^ 4)
        (P.realizedTransition T x) ∧
      (∫ y, (φ (P.geometry.smoothCoordinates y) - φ (P.geometry.smoothCoordinates x)) ^ 4
        ∂P.realizedTransition T x) ≤ C * T.val ^ 2 := by
  refine ⟨P.geometry.coordinateSecondMomentConstant φ * P.geometry.coordinateFourthGeneratorConstant φ / 2,
    div_nonneg (mul_nonneg (P.geometry.coordinateMomentConstants_nonneg φ).1
      (P.geometry.coordinateMomentConstants_nonneg φ).2) (by norm_num), fun T x => ?_⟩
  refine ⟨P.realizedTransition_coordinate_moment_integrable (P.geometry.coordinateTest φ) x 4 T, ?_⟩
  exact (P.coordinate_transition_moments hκ φ T x).2.trans_eq (by ring)

end TimeTraps.Analysis
