module

public import TimeTraps.Probability.GraphOccupationCompactData

@[expose] public section

/-! Uniform pathwise bounds for the original compact-time occupation
curve and the exact expression for its difference norm. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype E]

theorem graphOccupation_norm_le (G : MetricGraph V E)
    (f : C(GraphRealization G, ℝ)) (T : ℝ≥0) (p : GraphContinuousPath G) :
    ‖graphOccupation G f T p‖ ≤ (T : ℝ) * ‖f‖ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (T : ℝ)) (fun s _ => f.norm_coe_le_norm (p s.toNNReal))
  simpa only [graphOccupation, sub_zero, abs_of_nonneg T.coe_nonneg, mul_comm] using h

theorem graphOccupationCompactPath_norm_le (G : MetricGraph V E)
    (f : C(GraphRealization G, ℝ)) (T : ℝ≥0) (p : GraphContinuousPath G) :
    ‖graphOccupationCompactPath G f T p‖ ≤ (T : ℝ) * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  exact (graphOccupation_norm_le G f t.val p).trans
    (mul_le_mul_of_nonneg_right (show (t.val : ℝ) ≤ (T : ℝ) from t.property.2) (norm_nonneg _))

omit [Fintype E] in
theorem graphOccupationCompactPath_sub_norm_eq (G : MetricGraph V E)
    (f g : C(GraphRealization G, ℝ)) (T : ℝ≥0) (p : GraphContinuousPath G) :
    ‖graphOccupationCompactPath G f T p - graphOccupationCompactPath G g T p‖ =
      ⨆ t : Icc (0 : ℝ≥0) T, |graphOccupation G f t.val p - graphOccupation G g t.val p| := by
  rw [ContinuousMap.norm_eq_iSup_norm]
  simp only [ContinuousMap.sub_apply, graphOccupationCompactPath_apply, Real.norm_eq_abs]

end TimeTraps.Analysis
