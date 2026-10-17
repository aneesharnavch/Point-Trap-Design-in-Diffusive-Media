module

public import TimeTraps.Analysis.GraphShiftedContactHeatGenerator
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-! Integrated evolution for the actual unshifted graph operator, on its
full original domain. The mass shift is removed algebraically from the
proved compact spectral derivative before integration in time. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph
open scoped NNReal ENNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.heatCurve_continuous
    (P : GraphShiftedContactOperatorProblem V E) (x : GraphL2Product P.geometry) :
    Continuous (P.heatCurve x) :=
  Real.continuous_exp.smul
    ((P.operatorCompactPositiveInverse.heatSemigroup_strong_continuous x).comp continuous_real_toNNReal)

theorem GraphShiftedContactOperatorProblem.heatCurve_derivative_of_graph
    (P : GraphShiftedContactOperatorProblem V E) {x y : GraphL2Product P.geometry}
    (hxy : (x, y) ∈ P.operator.graph) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt (P.heatCurve x) (-P.heatCurve y s) (Ici 0) s := by
  have he := (P.operator_graph_iff x y).mp hxy
  let u : (inverseOperator P.operatorInverse P.operatorInverse_injective).domain := ⟨x, ⟨y + x, he⟩⟩
  have hu : inverseOperator P.operatorInverse P.operatorInverse_injective u = y + x := by
    apply P.operatorInverse_injective
    exact (inverseOperator_right_inverse P.operatorInverse P.operatorInverse_injective u).trans he.symm
  have hd := P.operatorCompactPositiveInverse.heatCurve_hasDerivWithinAt u hs
  rw [hu] at hd
  have hp := (Real.hasDerivAt_exp s).hasDerivWithinAt.smul hd
  have hv : Real.exp s • (-P.operatorCompactPositiveInverse.heatCurve (y + x) s) +
      Real.exp s • P.operatorCompactPositiveInverse.heatCurve x s = -P.heatCurve y s := by
    simp only [heatCurve, CompactPositiveInverse.heatCurve, map_add, smul_neg, smul_add]
    abel
  change HasDerivWithinAt (P.heatCurve x)
    (Real.exp s • (-P.operatorCompactPositiveInverse.heatCurve (y + x) s) +
      Real.exp s • P.operatorCompactPositiveInverse.heatCurve x s) (Ici 0) s at hp
  rw [hv] at hp
  exact hp

theorem GraphShiftedContactOperatorProblem.heatSemigroup_variation
    (P : GraphShiftedContactOperatorProblem V E) {x y : GraphL2Product P.geometry}
    (hxy : (x, y) ∈ P.operator.graph) (T : ℝ≥0) :
    P.heatSemigroup T x - x = -∫ s in (0 : ℝ)..T.val, P.heatSemigroup s.toNNReal y := by
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le T.coe_nonneg
    (P.heatCurve_continuous x).continuousOn
    (fun s hs => (P.heatCurve_derivative_of_graph hxy hs.1.le).hasDerivAt (Ici_mem_nhds hs.1))
    ((P.heatCurve_continuous y).neg.intervalIntegrable 0 T.val)
  have hc : (∫ s in (0 : ℝ)..T.val, -P.heatCurve y s) =
      -∫ s in (0 : ℝ)..T.val, P.heatSemigroup s.toNNReal y := by
    rw [intervalIntegral.integral_neg]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hs0 : 0 ≤ s := (uIcc_of_le T.coe_nonneg ▸ hs).1
    calc
      P.heatCurve y s = P.heatCurve y s.toNNReal.val :=
        congrArg (P.heatCurve y) (Real.coe_toNNReal s hs0).symm
      _ = _ := P.heatCurve_coe y s.toNNReal
  calc
    _ = P.heatCurve x T.val - P.heatCurve x 0 :=
      congrArg₂ (fun u v : GraphL2Product P.geometry => u - v)
        (P.heatCurve_coe x T).symm (P.heatCurve_zero x).symm
    _ = ∫ s in (0 : ℝ)..T.val, -P.heatCurve y s := ht.symm
    _ = _ := hc

end TimeTraps.Analysis
