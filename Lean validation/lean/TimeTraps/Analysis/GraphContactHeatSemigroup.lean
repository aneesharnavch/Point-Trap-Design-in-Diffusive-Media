module

public import TimeTraps.Analysis.GraphContactOperatorInverse
public import TimeTraps.Analysis.CompactSpectralSemigroupGeneratorCharacterization
public import TimeTraps.Analysis.InverseOperator

@[expose] public section

/-! The actual contraction heat family on the original finite edge L2
Hilbert product, built from the complete eigenbasis of the variable-conductance inverse. These are
analytic operators; no stochastic or Markov interpretation is used. -/

namespace TimeTraps.Analysis

open Set TimeTraps.Analysis
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphContactOperatorProblem.operator (P : GraphContactOperatorProblem V E) :
    GraphL2Product P.geometry →ₗ.[ℝ] GraphL2Product P.geometry :=
  inverseOperator P.operatorInverse P.operatorInverse_injective

noncomputable def GraphContactOperatorProblem.heatSemigroup (P : GraphContactOperatorProblem V E) (t : ℝ≥0) :
    GraphL2Product P.geometry →L[ℝ] GraphL2Product P.geometry :=
  P.operatorCompactPositiveInverse.heatSemigroup t

noncomputable def GraphContactOperatorProblem.heatCurve (P : GraphContactOperatorProblem V E)
    (x : GraphL2Product P.geometry) (t : ℝ) : GraphL2Product P.geometry :=
  P.operatorCompactPositiveInverse.heatCurve x t

theorem GraphContactOperatorProblem.heatSemigroup_zero (P : GraphContactOperatorProblem V E) :
    P.heatSemigroup 0 = ContinuousLinearMap.id ℝ (GraphL2Product P.geometry) :=
  P.operatorCompactPositiveInverse.heatSemigroup_zero

theorem GraphContactOperatorProblem.heatSemigroup_add (P : GraphContactOperatorProblem V E) (s t : ℝ≥0) :
    P.heatSemigroup (s + t) = (P.heatSemigroup s).comp (P.heatSemigroup t) :=
  P.operatorCompactPositiveInverse.heatSemigroup_add s t

theorem GraphContactOperatorProblem.heatSemigroup_norm_le (P : GraphContactOperatorProblem V E)
    (t : ℝ≥0) (x : GraphL2Product P.geometry) : ‖P.heatSemigroup t x‖ ≤ ‖x‖ :=
  P.operatorCompactPositiveInverse.heatSemigroup_norm_le t x

theorem GraphContactOperatorProblem.heatSemigroup_opNorm_le (P : GraphContactOperatorProblem V E)
    (t : ℝ≥0) : ‖P.heatSemigroup t‖ ≤ 1 :=
  P.operatorCompactPositiveInverse.heatSemigroup_opNorm_le t

theorem GraphContactOperatorProblem.heatSemigroup_inner (P : GraphContactOperatorProblem V E)
    (t : ℝ≥0) (x : GraphL2Product P.geometry) (i : CompactSpectralIndex P.operatorInverse) :
    inner ℝ (P.operatorCompactPositiveInverse.eigenbasis i) (P.heatSemigroup t x) =
      Real.exp (-(t : ℝ) / i.1) * inner ℝ (P.operatorCompactPositiveInverse.eigenbasis i) x :=
  P.operatorCompactPositiveInverse.heatSemigroup_inner t x i

theorem GraphContactOperatorProblem.heatSemigroup_expansion (P : GraphContactOperatorProblem V E)
    (t : ℝ≥0) (x : GraphL2Product P.geometry) :
    HasSum (fun i : CompactSpectralIndex P.operatorInverse =>
      (Real.exp (-(t : ℝ) / i.1) * inner ℝ (P.operatorCompactPositiveInverse.eigenbasis i) x) • P.operatorCompactPositiveInverse.eigenbasis i)
        (P.heatSemigroup t x) :=
  P.operatorCompactPositiveInverse.hasSum_heatSemigroup t x

theorem GraphContactOperatorProblem.heat_initial (P : GraphContactOperatorProblem V E) (x : GraphL2Product P.geometry) :
    P.heatCurve x 0 = x := P.operatorCompactPositiveInverse.heatCurve_zero x

theorem GraphContactOperatorProblem.heat_strong_continuous (P : GraphContactOperatorProblem V E)
    (x : GraphL2Product P.geometry) : Continuous (fun t : ℝ≥0 => P.heatCurve x t) := by
  simpa only [GraphContactOperatorProblem.heatCurve, CompactPositiveInverse.heatCurve, Real.toNNReal_coe] using
    P.operatorCompactPositiveInverse.heatSemigroup_strong_continuous x

end TimeTraps.Analysis
