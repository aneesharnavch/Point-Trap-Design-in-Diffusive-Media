module

public import TimeTraps.Analysis.GraphShiftedContactFellerOperator
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

/-! Exact semigroup composition for the continuous graph operators,
derived from the actual transition measures at every nonnegative time. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory TimeTraps.Graph
open scoped NNReal ENNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem GraphShiftedContactOperatorProblem.realizedFeller_integrable
    (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0)
    (f : C(GraphRealization P.geometry, ℝ)) (x : GraphRealization P.geometry) :
    Integrable f (P.realizedTransition t x) :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem GraphShiftedContactOperatorProblem.realizedFeller_add_apply
    (P : GraphShiftedContactOperatorProblem V E) (s t : ℝ≥0)
    (f : C(GraphRealization P.geometry, ℝ)) :
    P.realizedFeller (s + t) f = P.realizedFeller s (P.realizedFeller t f) := by
  ext x
  rw [P.realizedFeller_apply, P.realizedFeller_apply, P.realizedTransition_add]
  have hi : Integrable f ((P.realizedTransition t ∘ₖ P.realizedTransition s) x) := by
    rw [← P.realizedTransition_add]
    exact P.realizedFeller_integrable (s + t) f x
  rw [Kernel.integral_comp hi]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun y =>
    (P.realizedFeller_apply t f y).symm))

theorem GraphShiftedContactOperatorProblem.realizedFeller_add
    (P : GraphShiftedContactOperatorProblem V E) (s t : ℝ≥0) :
    P.realizedFeller (s + t) = (P.realizedFeller s).comp (P.realizedFeller t) := by
  ext f x
  exact congrArg (fun g : C(GraphRealization P.geometry, ℝ) => g x)
    (P.realizedFeller_add_apply s t f)

theorem GraphShiftedContactOperatorProblem.realizedFeller_contraction
    (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0)
    (f g : C(GraphRealization P.geometry, ℝ)) :
    ‖P.realizedFeller t f - P.realizedFeller t g‖ ≤ ‖f - g‖ := by
  rw [← map_sub]
  exact P.realizedFeller_norm_le t (f - g)

end TimeTraps.Analysis
