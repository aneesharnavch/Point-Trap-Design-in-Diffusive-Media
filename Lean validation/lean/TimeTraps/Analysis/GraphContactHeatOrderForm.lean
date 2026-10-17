module

public import TimeTraps.Analysis.GraphContactOperatorOrderLoad

@[expose] public section

/-! The full H1 resolvent pairing is edge L2 mass plus the positive step
times the original network form. Taking the actual graph absolute value
preserves both mass and quadratic energy. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace TimeTraps.Analysis
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphContactOperatorProblem.heatResolventPairing (P : GraphContactOperatorProblem V E)
    (s : ℝ≥0) (u v : GraphSobolevSpace P.geometry) : ℝ :=
  inner ℝ (graphSobolevSpaceStateL P.geometry u) (graphSobolevSpaceStateL P.geometry v) +
    (s : ℝ) * P.operatorForm u v

omit [Fintype V] in
theorem GraphContactOperatorProblem.operatorOrderAbs_mass (P : GraphContactOperatorProblem V E)
    (u : GraphSobolevSpace P.geometry) :
    inner ℝ (graphSobolevSpaceStateL P.geometry (P.operatorOrderAbs u))
      (graphSobolevSpaceStateL P.geometry (P.operatorOrderAbs u)) =
    inner ℝ (graphSobolevSpaceStateL P.geometry u) (graphSobolevSpaceStateL P.geometry u) := by
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  change ‖graphSobolevStateL P.geometry (P.operatorOrderAbs u).val‖ ^ 2 =
    ‖graphSobolevStateL P.geometry u.val‖ ^ 2
  rw [graphSobolevStateL_norm_sq_integral P.geometry,
    graphSobolevStateL_norm_sq_integral P.geometry]
  change (∑ e, ∫ x in (0 : ℝ)..P.geometry.length e, P.operatorRep (P.operatorOrderAbs u) e x ^ 2) =
    ∑ e, ∫ x in (0 : ℝ)..P.geometry.length e, P.operatorRep u e x ^ 2
  apply Finset.sum_congr rfl
  intro e _
  apply intervalIntegral.integral_congr_Ioo_of_le (P.geometry.length_pos e).le
  intro x hx
  change P.operatorRep (P.operatorOrderAbs u) e x ^ 2 = P.operatorRep u e x ^ 2
  rw [P.operatorOrderAbs_representative u e (Ioo_subset_Icc_self hx), sq_abs]

theorem GraphContactOperatorProblem.heatResolventPairing_orderAbs (P : GraphContactOperatorProblem V E)
    (s : ℝ≥0) (u : GraphSobolevSpace P.geometry) :
    P.heatResolventPairing s (P.operatorOrderAbs u) (P.operatorOrderAbs u) =
      P.heatResolventPairing s u u := by
  rw [heatResolventPairing, heatResolventPairing, P.operatorOrderAbs_mass, P.operatorForm_orderAbs]

-- The edge Hilbert product and its closed subspace require additional
-- instance normalization when both mass and form differences are expanded.
set_option maxHeartbeats 800000 in
theorem GraphContactOperatorProblem.heatResolventPairing_abs_difference (P : GraphContactOperatorProblem V E)
    (s : ℝ≥0) (u : GraphSobolevSpace P.geometry) :
    P.heatResolventPairing s (u - P.operatorOrderAbs u) (u - P.operatorOrderAbs u) =
      2 * P.heatResolventPairing s u (u - P.operatorOrderAbs u) := by
  simp only [heatResolventPairing, map_sub, inner_sub_left, inner_sub_right, sub_apply]
  rw [P.operatorOrderAbs_mass, P.operatorForm_orderAbs,
    real_inner_comm (graphSobolevSpaceStateL P.geometry u)
      (graphSobolevSpaceStateL P.geometry (P.operatorOrderAbs u)),
    P.operatorForm_symmetric (P.operatorOrderAbs u) u]
  ring

end TimeTraps.Analysis
