module

public import TimeTraps.Analysis.GraphContactFellerOperator
public import TimeTraps.Analysis.GraphContactSolutionDense

@[expose] public section

/-! Identification of the continuous transition action with the original
H1 heat solution and its physical weak inverse. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph
open scoped NNReal ENNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphContactOperatorProblem.realizedHeatC_sobolev_apply
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t)
    (u : GraphSobolevSpace P.geometry) (x : GraphRealization P.geometry) :
    P.realizedHeatC t ht (graphRealizedSobolev P.geometry u) x =
      P.realizedHeatEvaluation t ht x (graphSobolevSpaceStateL P.geometry u) := by
  change (∫ y, P.realizedHeatKernel t ht x y * graphRealizedSobolev P.geometry u y
    ∂P.geometry.lengthMeasure) = _
  rw [P.geometry.lengthMeasure_integral
    (fun y => P.realizedHeatKernel t ht x y * graphRealizedSobolev P.geometry u y)
    ((P.realizedHeatKernel_right_continuous t ht x).mul
      (graphRealizedSobolev P.geometry u).continuous), P.realizedHeatEvaluation_integral_apply]
  apply Finset.sum_congr rfl
  intro e _
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    graphSobolevRepresentative_state_ae P.geometry u.val e] with y hy he
  change P.realizedHeatKernel t ht x (P.geometry.edgePointClamped e y) *
    graphRealizedSobolev P.geometry u
      (P.geometry.edgePoint e (projIcc 0 (P.geometry.length e) (P.geometry.length_pos e).le y)) = _
  rw [graphRealizedSobolev_edge]
  simp only [projIcc_of_mem (P.geometry.length_pos e).le (Ioo_subset_Icc_self hy)]
  exact congrArg (fun z : ℝ => P.realizedHeatKernel t ht x
    (P.geometry.edgePointClamped e y) * z) he.symm

theorem GraphContactOperatorProblem.realizedHeatC_sobolev
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t)
    (u : GraphSobolevSpace P.geometry) :
    P.realizedHeatC t ht (graphRealizedSobolev P.geometry u) =
      graphRealizedSobolev P.geometry (P.heatSobolevL t ht (graphSobolevSpaceStateL P.geometry u)) := by
  ext x
  rw [P.realizedHeatC_sobolev_apply]
  obtain ⟨e, y, rfl⟩ := P.geometry.edgePoint_surjective x
  rw [P.realizedHeatEvaluation_edge, P.heatPointEvaluation_apply, graphRealizedSobolev_edge]
  rfl

theorem GraphContactOperatorProblem.heatSobolevL_inverse
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t)
    (f : GraphL2Product P.geometry) :
    P.heatSobolevL t ht (P.operatorInverse f) = P.operatorSolution (P.heatSemigroup t f) := by
  apply graphSobolevSpaceStateL_injective P.geometry
  rw [P.heatSobolevL_state, ← P.operatorInverse_apply]
  exact (P.operatorCompactPositiveInverse.heatSemigroup_commutes t f).symm

theorem GraphContactOperatorProblem.realizedFeller_solution
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0)
    (f : GraphL2Product P.geometry) :
    P.realizedFeller t (P.realizedSolutionL f) = P.realizedSolutionL (P.heatSemigroup t f) := by
  by_cases ht : 0 < t
  · rw [P.realizedFeller_pos t ht, P.realizedHeatCL_apply, P.realizedSolutionL_apply,
      P.realizedHeatC_sobolev, ← P.operatorInverse_apply, P.heatSobolevL_inverse,
      P.realizedSolutionL_apply]
  · have hz : t = 0 := le_antisymm (le_of_not_gt ht) (show 0 ≤ t from zero_le)
    subst t
    rw [P.realizedFeller_zero, P.heatSemigroup_zero]
    rfl

end TimeTraps.Analysis
