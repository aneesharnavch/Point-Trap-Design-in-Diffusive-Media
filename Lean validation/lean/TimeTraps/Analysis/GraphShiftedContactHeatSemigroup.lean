module

public import TimeTraps.Analysis.GraphShiftedContactHeatData
public import TimeTraps.Analysis.CompactHeatSymmetry

@[expose] public section

/-! Undo the mass shift on the actual compact spectral heat evolution.
The resulting family has rates of the original contact operator and
retains zero rates when the graph has no killing. -/

namespace TimeTraps.Analysis

open Set InnerProductSpace
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.heatSemigroup
    (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0) :
    GraphL2Product P.geometry →L[ℝ] GraphL2Product P.geometry :=
  Real.exp (t : ℝ) • P.operatorCompactPositiveInverse.heatSemigroup t

noncomputable def GraphShiftedContactOperatorProblem.heatCurve
    (P : GraphShiftedContactOperatorProblem V E) (x : GraphL2Product P.geometry)
    (t : ℝ) : GraphL2Product P.geometry :=
  Real.exp t • P.operatorCompactPositiveInverse.heatCurve x t

theorem GraphShiftedContactOperatorProblem.heatCurve_coe
    (P : GraphShiftedContactOperatorProblem V E) (x : GraphL2Product P.geometry) (t : ℝ≥0) :
    P.heatCurve x t = P.heatSemigroup t x := by
  simp only [heatCurve, heatSemigroup, CompactPositiveInverse.heatCurve,
    Real.toNNReal_coe, smul_apply]

theorem GraphShiftedContactOperatorProblem.heatSemigroup_zero
    (P : GraphShiftedContactOperatorProblem V E) :
    P.heatSemigroup 0 = ContinuousLinearMap.id ℝ (GraphL2Product P.geometry) := by
  simp only [heatSemigroup, NNReal.coe_zero, Real.exp_zero, one_smul,
    P.operatorCompactPositiveInverse.heatSemigroup_zero]

theorem GraphShiftedContactOperatorProblem.heatSemigroup_add
    (P : GraphShiftedContactOperatorProblem V E) (s t : ℝ≥0) :
    P.heatSemigroup (s + t) = (P.heatSemigroup s).comp (P.heatSemigroup t) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [heatSemigroup, NNReal.coe_add, Real.exp_add,
    P.operatorCompactPositiveInverse.heatSemigroup_add, smul_apply,
    ContinuousLinearMap.comp_apply, map_smul, smul_smul, mul_comm]

theorem GraphShiftedContactOperatorProblem.heatSemigroup_inner
    (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0) (x : GraphL2Product P.geometry)
    (i : CompactSpectralIndex P.operatorInverse) :
    inner ℝ (P.operatorCompactPositiveInverse.eigenbasis i) (P.heatSemigroup t x) =
      P.heatCoefficient t i * inner ℝ (P.operatorCompactPositiveInverse.eigenbasis i) x := by
  simp only [heatSemigroup, smul_apply, inner_smul_right,
    P.operatorCompactPositiveInverse.heatSemigroup_inner, P.heatCoefficient_shift, mul_assoc]

theorem GraphShiftedContactOperatorProblem.heatSemigroup_expansion
    (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0) (x : GraphL2Product P.geometry) :
    HasSum (fun i : CompactSpectralIndex P.operatorInverse =>
      (P.heatCoefficient t i * inner ℝ (P.operatorCompactPositiveInverse.eigenbasis i) x) •
        P.operatorCompactPositiveInverse.eigenbasis i) (P.heatSemigroup t x) := by
  simpa only [P.heatSemigroup_inner] using
    P.operatorCompactPositiveInverse.hasSum_eigenbasis (P.heatSemigroup t x)

theorem GraphShiftedContactOperatorProblem.heatSemigroup_symmetric
    (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0) :
    (P.heatSemigroup t).IsSymmetric := by
  intro x y
  change inner ℝ (Real.exp (t : ℝ) • P.operatorCompactPositiveInverse.heatSemigroup t x) y =
    inner ℝ x (Real.exp (t : ℝ) • P.operatorCompactPositiveInverse.heatSemigroup t y)
  simp only [real_inner_smul_left, inner_smul_right]
  have hs : inner ℝ (P.operatorCompactPositiveInverse.heatSemigroup t x) y =
      inner ℝ x (P.operatorCompactPositiveInverse.heatSemigroup t y) :=
    P.operatorCompactPositiveInverse.heatSemigroup_symmetric t x y
  rw [hs]

theorem GraphShiftedContactOperatorProblem.heatSemigroup_strong_continuous
    (P : GraphShiftedContactOperatorProblem V E) (x : GraphL2Product P.geometry) :
    Continuous (fun t : ℝ≥0 => P.heatSemigroup t x) :=
  (Real.continuous_exp.comp NNReal.continuous_coe).smul
    (P.operatorCompactPositiveInverse.heatSemigroup_strong_continuous x)

end TimeTraps.Analysis
