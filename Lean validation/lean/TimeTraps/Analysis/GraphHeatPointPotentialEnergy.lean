module

public import TimeTraps.Analysis.GraphShiftedContactHeatSobolev
public import TimeTraps.Analysis.GraphShiftedContactHeatContraction

@[expose] public section

/-! Energy smoothing for the actual original graph heat. The shifted
full form is evaluated through its constructed solution map; contraction
and the proved inverse-heat bound supply the short-time estimate. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.heatSobolevL_form
    (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t)
    (f : GraphL2Product P.geometry) (v : GraphSobolevSpace P.geometry) :
    P.operatorForm (P.heatSobolevL t ht f) v = Real.exp (t : ℝ) *
      inner ℝ (P.operatorCompactPositiveInverse.heatInverseL t ht f)
        (graphSobolevSpaceStateL P.geometry v) := by
  change P.operatorForm (Real.exp (t : ℝ) •
    P.operatorSolution (P.operatorCompactPositiveInverse.heatInverseL t ht f)) v = _
  rw [map_smul, smul_apply, smul_eq_mul, P.operatorSolution_spec]

theorem GraphShiftedContactOperatorProblem.heatSobolevL_form_bound
    (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t)
    (f : GraphL2Product P.geometry) :
    P.operatorForm (P.heatSobolevL t ht f) (P.heatSobolevL t ht f) ≤
      (Real.exp (t : ℝ) / (t : ℝ)) * ‖f‖ ^ 2 := by
  rw [P.heatSobolevL_form, P.heatSobolevL_state]
  have hi : ‖P.operatorCompactPositiveInverse.heatInverseL t ht f‖ ≤
      (1 / (t : ℝ)) * ‖f‖ :=
    (P.operatorCompactPositiveInverse.heatInverseL t ht).le_opNorm f |>.trans
      (mul_le_mul_of_nonneg_right
        (P.operatorCompactPositiveInverse.heatInverseL_norm_le t ht) (norm_nonneg _))
  calc
    _ ≤ Real.exp (t : ℝ) *
        (‖P.operatorCompactPositiveInverse.heatInverseL t ht f‖ * ‖P.heatSemigroup t f‖) :=
      mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) (Real.exp_pos _).le
    _ ≤ Real.exp (t : ℝ) * (((1 / (t : ℝ)) * ‖f‖) * ‖f‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hi (P.heatSemigroup_norm_le t f) (norm_nonneg _)
          (mul_nonneg (div_nonneg zero_le_one ht.le) (norm_nonneg _))) (Real.exp_pos _).le
    _ = _ := by ring

theorem GraphShiftedContactOperatorProblem.heatSobolevL_h1_bound
    (P : GraphShiftedContactOperatorProblem V E) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (ht : 0 < t) (f : GraphL2Product P.geometry),
      ‖P.heatSobolevL t ht f‖ ^ 2 ≤ C * (Real.exp (t : ℝ) / (t : ℝ)) * ‖f‖ ^ 2 := by
  obtain ⟨c,hc,hb⟩ := P.operatorForm_coercive
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  intro t ht f
  have h := hb (P.heatSobolevL t ht f)
  have hb' : c * ‖P.heatSobolevL t ht f‖ ^ 2 ≤
      P.operatorForm (P.heatSobolevL t ht f) (P.heatSobolevL t ht f) := by
    simpa only [pow_two, mul_assoc] using h
  have h' : c * ‖P.heatSobolevL t ht f‖ ^ 2 ≤
      (Real.exp (t : ℝ) / (t : ℝ)) * ‖f‖ ^ 2 :=
    hb'.trans (P.heatSobolevL_form_bound t ht f)
  calc
    _ ≤ ((Real.exp (t : ℝ) / (t : ℝ)) * ‖f‖ ^ 2) / c :=
      (le_div_iff₀ hc).mpr (by nlinarith)
    _ = _ := by ring

end TimeTraps.Analysis
