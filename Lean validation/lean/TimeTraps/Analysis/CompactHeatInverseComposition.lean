module

public import TimeTraps.Analysis.CompactHeatInverseContinuous

@[expose] public section

namespace TimeTraps.Analysis

open scoped NNReal

variable {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem CompactPositiveInverse.heatInverseL_comp_norm_le {T : H →L[ℝ] H}
    (h : CompactPositiveInverse T) (S : H →L[ℝ] F) (t : ℝ≥0) (ht : 0 < t) :
    ‖S.comp (h.heatInverseL t ht)‖ ≤ ‖S‖ / (t : ℝ) := by
  calc
    _ ≤ ‖S‖ * ‖h.heatInverseL t ht‖ := ContinuousLinearMap.opNorm_comp_le S _
    _ ≤ ‖S‖ * (1 / (t : ℝ)) :=
      mul_le_mul_of_nonneg_left (h.heatInverseL_norm_le t ht) (norm_nonneg S)
    _ = _ := by ring

end TimeTraps.Analysis
