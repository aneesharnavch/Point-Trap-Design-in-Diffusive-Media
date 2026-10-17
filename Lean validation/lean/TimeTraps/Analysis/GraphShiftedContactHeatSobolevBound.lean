module

public import TimeTraps.Analysis.GraphShiftedContactHeatSobolev

@[expose] public section

namespace TimeTraps.Analysis

open TimeTraps.Analysis IntervalSobolevSpace
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

theorem GraphShiftedContactOperatorProblem.heatSobolevL_norm_le (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) :
    ‖P.heatSobolevL t ht‖ ≤ Real.exp (t : ℝ) * (‖P.operatorSolution‖ / (t : ℝ)) := by
  let : NormedSpace ℝ (GraphSobolevSpace P.geometry) :=
    Submodule.normedSpace (graphSobolevSubspace P.geometry)
  change ‖Real.exp (t : ℝ) • P.operatorSolution.comp
    (P.operatorCompactPositiveInverse.heatInverseL t ht)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left
    (P.operatorCompactPositiveInverse.heatInverseL_comp_norm_le P.operatorSolution t ht)
    (Real.exp_pos _).le

end TimeTraps.Analysis
