module

public import TimeTraps.Analysis.GraphShiftedContactOrderLoad

@[expose] public section

/-! The full H1 resolvent pairing is edge L2 mass plus the positive step
times the actual mass-shifted graph form. Taking the actual graph absolute value
preserves both mass and quadratic energy. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace TimeTraps.Analysis
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.shiftedHeatResolventPairing (P : GraphShiftedContactOperatorProblem V E)
    (s : ℝ≥0) (u v : GraphSobolevSpace P.geometry) : ℝ :=
  inner ℝ (graphSobolevSpaceStateL P.geometry u) (graphSobolevSpaceStateL P.geometry v) +
    (s : ℝ) * P.operatorForm u v

theorem GraphShiftedContactOperatorProblem.shiftedHeatResolventPairing_orderAbs (P : GraphShiftedContactOperatorProblem V E)
    (s : ℝ≥0) (u : GraphSobolevSpace P.geometry) :
    P.shiftedHeatResolventPairing s (P.operatorOrderAbs u) (P.operatorOrderAbs u) =
      P.shiftedHeatResolventPairing s u u := by
  rw [shiftedHeatResolventPairing, shiftedHeatResolventPairing, P.operatorOrderAbs_mass, P.operatorForm_orderAbs]

-- The edge Hilbert product and its closed subspace require additional
-- instance normalization when both mass and form differences are expanded.
set_option maxHeartbeats 800000 in
theorem GraphShiftedContactOperatorProblem.shiftedHeatResolventPairing_abs_difference (P : GraphShiftedContactOperatorProblem V E)
    (s : ℝ≥0) (u : GraphSobolevSpace P.geometry) :
    P.shiftedHeatResolventPairing s (u - P.operatorOrderAbs u) (u - P.operatorOrderAbs u) =
      2 * P.shiftedHeatResolventPairing s u (u - P.operatorOrderAbs u) := by
  simp only [shiftedHeatResolventPairing, map_sub, inner_sub_left, inner_sub_right, sub_apply]
  rw [P.operatorOrderAbs_mass, P.operatorForm_orderAbs,
    real_inner_comm (graphSobolevSpaceStateL P.geometry u)
      (graphSobolevSpaceStateL P.geometry (P.operatorOrderAbs u)),
    P.operatorForm_symmetric (P.operatorOrderAbs u) u]
  ring

end TimeTraps.Analysis
