module

public import TimeTraps.Analysis.GraphShiftedContactHeatSemigroup

@[expose] public section

/-! Although removing the shift multiplies the shifted evolution by exp(t),
the resulting original evolution is a contraction. The actual inverse
eigenvalue bound, rather than an assumed spectral gap, proves this. -/

namespace TimeTraps.Analysis

open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.heatSemigroup_eq_contraction
    (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0) :
    P.heatSemigroup t = hilbertContraction P.operatorCompactPositiveInverse.eigenbasis
      (P.heatCoefficient t) (P.heatCoefficient_abs_le_one t) := by
  apply ContinuousLinearMap.ext
  intro x
  apply P.operatorCompactPositiveInverse.eigenbasis.repr.injective
  apply lp.ext
  funext i
  rw [HilbertBasis.repr_apply_apply, P.heatSemigroup_inner,
    hilbertContraction_repr, HilbertBasis.repr_apply_apply]

theorem GraphShiftedContactOperatorProblem.heatSemigroup_norm_le
    (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0) (x : GraphL2Product P.geometry) :
    ‖P.heatSemigroup t x‖ ≤ ‖x‖ := by
  rw [P.heatSemigroup_eq_contraction]
  exact hilbertContraction_norm_le P.operatorCompactPositiveInverse.eigenbasis
    (P.heatCoefficient t) (P.heatCoefficient_abs_le_one t) x

theorem GraphShiftedContactOperatorProblem.heatSemigroup_opNorm_le
    (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0) : ‖P.heatSemigroup t‖ ≤ 1 := by
  rw [P.heatSemigroup_eq_contraction]
  exact hilbertContraction_opNorm_le P.operatorCompactPositiveInverse.eigenbasis
    (P.heatCoefficient t) (P.heatCoefficient_abs_le_one t)

end TimeTraps.Analysis
