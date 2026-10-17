module

public import TimeTraps.Analysis.GraphShiftedContactHeatOrderForm
public import TimeTraps.Analysis.GraphShiftedContactHeatSemigroup
public import TimeTraps.Spectral.CompactInverseResolventDomain

@[expose] public section

/-! The actual shifted spectral graph resolvent has an actual graph H1 representative.
Its full mass-plus-form weak equation is derived from the actual inverse
operator graph, not assumed as a characterization of the multiplier. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace TimeTraps.Analysis
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.shiftedHeatSemigroup
    (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0) :
    GraphL2Product P.geometry →L[ℝ] GraphL2Product P.geometry :=
  P.operatorCompactPositiveInverse.heatSemigroup t

noncomputable def GraphShiftedContactOperatorProblem.shiftedHeatResolvent (P : GraphShiftedContactOperatorProblem V E) (s : ℝ≥0) :
    GraphL2Product P.geometry →L[ℝ] GraphL2Product P.geometry :=
  P.operatorCompactPositiveInverse.resolvent s

theorem GraphShiftedContactOperatorProblem.shiftedHeatResolvent_zero (P : GraphShiftedContactOperatorProblem V E) :
    P.shiftedHeatResolvent 0 = ContinuousLinearMap.id ℝ (GraphL2Product P.geometry) :=
  P.operatorCompactPositiveInverse.resolvent_zero

theorem GraphShiftedContactOperatorProblem.shiftedHeatResolvent_mem_domain (P : GraphShiftedContactOperatorProblem V E)
    (s : ℝ≥0) (hs : 0 < s) (f : GraphL2Product P.geometry) :
    P.shiftedHeatResolvent s f ∈ P.shiftedOperator.domain :=
  P.operatorCompactPositiveInverse.resolvent_mem_inverse_domain s hs f

noncomputable def GraphShiftedContactOperatorProblem.shiftedHeatResolventState (P : GraphShiftedContactOperatorProblem V E)
    (s : ℝ≥0) (hs : 0 < s) (f : GraphL2Product P.geometry) : GraphSobolevSpace P.geometry :=
  P.operatorSolution (P.shiftedOperator ⟨P.shiftedHeatResolvent s f, P.shiftedHeatResolvent_mem_domain s hs f⟩)

theorem GraphShiftedContactOperatorProblem.shiftedHeatResolventState_state (P : GraphShiftedContactOperatorProblem V E)
    (s : ℝ≥0) (hs : 0 < s) (f : GraphL2Product P.geometry) :
    graphSobolevSpaceStateL P.geometry (P.shiftedHeatResolventState s hs f) = P.shiftedHeatResolvent s f :=
  inverseOperator_right_inverse P.operatorInverse P.operatorInverse_injective _

theorem GraphShiftedContactOperatorProblem.shiftedHeatResolvent_equation (P : GraphShiftedContactOperatorProblem V E)
    (s : ℝ≥0) (hs : 0 < s) (f : GraphL2Product P.geometry) :
    P.shiftedHeatResolvent s f + (s : ℝ) •
      P.shiftedOperator ⟨P.shiftedHeatResolvent s f, P.shiftedHeatResolvent_mem_domain s hs f⟩ = f :=
  P.operatorCompactPositiveInverse.resolvent_equation s hs f

theorem GraphShiftedContactOperatorProblem.shiftedHeatResolventState_spec (P : GraphShiftedContactOperatorProblem V E)
    (s : ℝ≥0) (hs : 0 < s) (f : GraphL2Product P.geometry) (v : GraphSobolevSpace P.geometry) :
    P.shiftedHeatResolventPairing s (P.shiftedHeatResolventState s hs f) v =
      inner ℝ f (graphSobolevSpaceStateL P.geometry v) := by
  unfold shiftedHeatResolventPairing
  rw [P.shiftedHeatResolventState_state]
  have he : P.operatorForm (P.shiftedHeatResolventState s hs f) v =
      inner ℝ (P.shiftedOperator ⟨P.shiftedHeatResolvent s f, P.shiftedHeatResolvent_mem_domain s hs f⟩)
        (graphSobolevSpaceStateL P.geometry v) :=
    P.operatorSolution_spec _ v
  rw [he, ← real_inner_smul_left, ← inner_add_left, P.shiftedHeatResolvent_equation s hs f]

end TimeTraps.Analysis
