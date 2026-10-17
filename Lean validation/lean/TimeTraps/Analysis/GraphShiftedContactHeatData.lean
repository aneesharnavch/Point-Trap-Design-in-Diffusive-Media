module

public import TimeTraps.Analysis.GraphShiftedContactOperatorConstant
public import TimeTraps.Analysis.CompactSpectralSemigroupGeneratorCharacterization

@[expose] public section

/-! The mass-shifted inverse has eigenvalues at most one. This is derived
from the original nonnegative contact form. Consequently the unshifted
rates are nonnegative, including the zero rate of a conservative graph. -/

namespace TimeTraps.Analysis

open Set InnerProductSpace
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.eigenbasis_reciprocal_ge_one
    (P : GraphShiftedContactOperatorProblem V E) (i : CompactSpectralIndex P.operatorInverse) :
    1 ≤ i.1⁻¹ := by
  have hn := P.operator_nonneg
    ⟨P.operatorCompactPositiveInverse.eigenbasis i,
      P.operatorCompactPositiveInverse.eigenbasis_mem_inverse_domain i⟩
  rw [P.operator_apply] at hn
  change 0 ≤ inner ℝ (P.operatorCompactPositiveInverse.eigenbasis i)
    (inverseOperator P.operatorInverse P.operatorInverse_injective
      ⟨P.operatorCompactPositiveInverse.eigenbasis i,
        P.operatorCompactPositiveInverse.eigenbasis_mem_inverse_domain i⟩ -
          P.operatorCompactPositiveInverse.eigenbasis i) at hn
  rw [P.operatorCompactPositiveInverse.inverse_eigenbasis, inner_sub_right,
    inner_smul_right, real_inner_self_eq_norm_sq,
    P.operatorCompactPositiveInverse.eigenbasis.orthonormal.norm_eq_one,
    one_pow, mul_one] at hn
  linarith

theorem GraphShiftedContactOperatorProblem.eigenbasis_eigenvalue_le_one
    (P : GraphShiftedContactOperatorProblem V E) (i : CompactSpectralIndex P.operatorInverse) :
    i.1 ≤ 1 := by
  have hp := P.operatorCompactPositiveInverse.eigenbasis_positive i
  have hn := mul_le_mul_of_nonneg_right (P.eigenbasis_reciprocal_ge_one i) hp.le
  simpa only [one_mul, inv_mul_cancel₀ hp.ne'] using hn

noncomputable def GraphShiftedContactOperatorProblem.heatRate
    (P : GraphShiftedContactOperatorProblem V E) (i : CompactSpectralIndex P.operatorInverse) : ℝ :=
  i.1⁻¹ - 1

theorem GraphShiftedContactOperatorProblem.heatRate_nonneg
    (P : GraphShiftedContactOperatorProblem V E) (i : CompactSpectralIndex P.operatorInverse) :
    0 ≤ P.heatRate i := sub_nonneg.mpr (P.eigenbasis_reciprocal_ge_one i)

noncomputable def GraphShiftedContactOperatorProblem.heatCoefficient
    (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0)
    (i : CompactSpectralIndex P.operatorInverse) : ℝ := Real.exp (-(t : ℝ) * P.heatRate i)

theorem GraphShiftedContactOperatorProblem.heatCoefficient_shift
    (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0)
    (i : CompactSpectralIndex P.operatorInverse) :
    P.heatCoefficient t i = Real.exp (t : ℝ) * compactHeatCoefficient t i := by
  rw [heatCoefficient, compactHeatCoefficient, ← Real.exp_add]
  congr 1
  simp only [heatRate, div_eq_mul_inv]
  ring

theorem GraphShiftedContactOperatorProblem.heatCoefficient_abs_le_one
    (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0)
    (i : CompactSpectralIndex P.operatorInverse) : |P.heatCoefficient t i| ≤ 1 := by
  rw [heatCoefficient, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr t.property) (P.heatRate_nonneg i)

end TimeTraps.Analysis
