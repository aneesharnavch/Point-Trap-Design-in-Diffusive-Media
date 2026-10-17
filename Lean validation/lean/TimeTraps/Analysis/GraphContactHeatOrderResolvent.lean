module

public import TimeTraps.Analysis.GraphContactHeatOrderForm
public import TimeTraps.Analysis.GraphContactHeatSemigroup
public import TimeTraps.Spectral.CompactInverseResolventDomain

@[expose] public section

/-! The spectral network resolvent has an actual graph H1 representative.
Its full mass-plus-form weak equation is derived from the actual inverse
operator graph, not assumed as a characterization of the multiplier. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace TimeTraps.Analysis
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphContactOperatorProblem.heatResolvent (P : GraphContactOperatorProblem V E) (s : ℝ≥0) :
    GraphL2Product P.geometry →L[ℝ] GraphL2Product P.geometry :=
  P.operatorCompactPositiveInverse.resolvent s

theorem GraphContactOperatorProblem.heatResolvent_zero (P : GraphContactOperatorProblem V E) :
    P.heatResolvent 0 = ContinuousLinearMap.id ℝ (GraphL2Product P.geometry) :=
  P.operatorCompactPositiveInverse.resolvent_zero

theorem GraphContactOperatorProblem.heatResolvent_mem_domain (P : GraphContactOperatorProblem V E)
    (s : ℝ≥0) (hs : 0 < s) (f : GraphL2Product P.geometry) :
    P.heatResolvent s f ∈ P.operator.domain :=
  P.operatorCompactPositiveInverse.resolvent_mem_inverse_domain s hs f

noncomputable def GraphContactOperatorProblem.heatResolventState (P : GraphContactOperatorProblem V E)
    (s : ℝ≥0) (hs : 0 < s) (f : GraphL2Product P.geometry) : GraphSobolevSpace P.geometry :=
  P.operatorSolution (P.operator ⟨P.heatResolvent s f, P.heatResolvent_mem_domain s hs f⟩)

theorem GraphContactOperatorProblem.heatResolventState_state (P : GraphContactOperatorProblem V E)
    (s : ℝ≥0) (hs : 0 < s) (f : GraphL2Product P.geometry) :
    graphSobolevSpaceStateL P.geometry (P.heatResolventState s hs f) = P.heatResolvent s f :=
  inverseOperator_right_inverse P.operatorInverse P.operatorInverse_injective _

theorem GraphContactOperatorProblem.heatResolvent_equation (P : GraphContactOperatorProblem V E)
    (s : ℝ≥0) (hs : 0 < s) (f : GraphL2Product P.geometry) :
    P.heatResolvent s f + (s : ℝ) •
      P.operator ⟨P.heatResolvent s f, P.heatResolvent_mem_domain s hs f⟩ = f :=
  P.operatorCompactPositiveInverse.resolvent_equation s hs f

theorem GraphContactOperatorProblem.heatResolventState_spec (P : GraphContactOperatorProblem V E)
    (s : ℝ≥0) (hs : 0 < s) (f : GraphL2Product P.geometry) (v : GraphSobolevSpace P.geometry) :
    P.heatResolventPairing s (P.heatResolventState s hs f) v =
      inner ℝ f (graphSobolevSpaceStateL P.geometry v) := by
  unfold heatResolventPairing
  rw [P.heatResolventState_state]
  have he : P.operatorForm (P.heatResolventState s hs f) v =
      inner ℝ (P.operator ⟨P.heatResolvent s f, P.heatResolvent_mem_domain s hs f⟩)
        (graphSobolevSpaceStateL P.geometry v) :=
    P.operatorSolution_spec _ v
  rw [he, ← real_inner_smul_left, ← inner_add_left, P.heatResolvent_equation s hs f]

end TimeTraps.Analysis
