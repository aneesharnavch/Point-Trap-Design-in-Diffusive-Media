module

public import TimeTraps.Analysis.GraphShiftedContactFellerContinuous
public import TimeTraps.Analysis.GraphShiftedContactRealizedConservative

@[expose] public section

/-! The actual continuous graph transition preserves constants when all
vertex reactions vanish. This is the conservative Feller specialization
of the original unshifted graph heat evolution. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory TimeTraps.Graph
open scoped NNReal ENNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.realizedFeller_one
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0) (t : ℝ≥0) :
    P.realizedFeller t (ContinuousMap.const (GraphRealization P.geometry) (1 : ℝ)) =
      ContinuousMap.const (GraphRealization P.geometry) (1 : ℝ) := by
  ext x
  rw [P.realizedFeller_apply]
  change (∫ _y, (1 : ℝ) ∂P.realizedTransition t x) = 1
  simp only [integral_const, Measure.real, P.realizedTransition_mass_one hκ,
    ENNReal.toReal_one, one_smul]

end TimeTraps.Analysis
