module

public import TimeTraps.Probability.GraphPointLocalTimeMartingale
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

@[expose] public section

/-! Actual first absolute moments of graph local time and its terminal
martingales. Conditional expectation contraction gives a uniform bound
without any assumed pathwise growth estimate. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.pointLocalTime_integral_norm
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (H : ℝ≥0) :
    (∫ p, ‖P.pointLocalTime a H p‖ ∂P.continuousPathLaw hκ x) = P.realizedHeatPointPotential x a H := by
  calc
    _ = ∫ p, P.pointLocalTime a H p ∂P.continuousPathLaw hκ x := by
      apply integral_congr_ae
      filter_upwards [P.pointLocalTime_eq_path_ae hκ x a] with p hp
      simp only [hp H, Real.norm_eq_abs, abs_of_nonneg (P.pointLocalTimePath_nonneg a p H)]
    _ = _ := P.pointLocalTime_mean hκ x a H

theorem GraphShiftedContactOperatorProblem.pointLocalTimeTerminalProcess_integral_norm_le
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (H t : ℝ≥0) :
    (∫ p, ‖P.pointLocalTimeTerminalProcess a H t p‖ ∂P.continuousPathLaw hκ x) ≤
      P.realizedHeatPointPotential x a H := by
  calc
    _ = ∫ p, ‖(P.continuousPathLaw hκ x)[P.pointLocalTime a H |
        graphContinuousNaturalFiltration P.geometry t] p‖ ∂P.continuousPathLaw hκ x :=
      integral_congr_ae ((P.pointLocalTimeTerminalProcess_condExp hκ x a H t).symm.fun_comp norm)
    _ ≤ ∫ p, ‖P.pointLocalTime a H p‖ ∂P.continuousPathLaw hκ x := integral_norm_condExp_le _
    _ = _ := P.pointLocalTime_integral_norm hκ x a H

end TimeTraps.Analysis
