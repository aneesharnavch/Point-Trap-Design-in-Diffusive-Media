module

public import TimeTraps.Analysis.GraphShiftedContactOperatorInverse
public import TimeTraps.Analysis.InverseOperator

@[expose] public section

/-! Removing the ordinary mass shift yields an actual densely defined
closed graph contact operator. Its graph is characterized through the
proved shifted inverse, and its quadratic form is nonnegative even when
every contact vanishes. -/

namespace TimeTraps.Analysis

open Set InnerProductSpace

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.shiftedOperator
    (P : GraphShiftedContactOperatorProblem V E) :
    GraphL2Product P.geometry →ₗ.[ℝ] GraphL2Product P.geometry :=
  inverseOperator P.operatorInverse P.operatorInverse_injective

noncomputable def GraphShiftedContactOperatorProblem.operator
    (P : GraphShiftedContactOperatorProblem V E) :
    GraphL2Product P.geometry →ₗ.[ℝ] GraphL2Product P.geometry where
  domain := P.shiftedOperator.domain
  toFun := P.shiftedOperator.toFun - P.shiftedOperator.domain.subtype

theorem GraphShiftedContactOperatorProblem.operator_domain
    (P : GraphShiftedContactOperatorProblem V E) : P.operator.domain = P.operatorInverse.range := rfl

theorem GraphShiftedContactOperatorProblem.operator_apply
    (P : GraphShiftedContactOperatorProblem V E) (u : P.operator.domain) :
    P.operator u = P.shiftedOperator u - (u : GraphL2Product P.geometry) := rfl

theorem GraphShiftedContactOperatorProblem.operator_graph_iff
    (P : GraphShiftedContactOperatorProblem V E) (x y : GraphL2Product P.geometry) :
    (x, y) ∈ P.operator.graph ↔ P.operatorInverse (y + x) = x := by
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨z, hz, hzy⟩
    change (z : GraphL2Product P.geometry) = x at hz
    change P.shiftedOperator z - (z : GraphL2Product P.geometry) = y at hzy
    rw [hz] at hzy
    have hs := sub_eq_iff_eq_add.mp hzy
    rw [← hs]
    exact (inverseOperator_right_inverse P.operatorInverse P.operatorInverse_injective z).trans hz
  · intro he
    let z : P.operator.domain := ⟨x, ⟨y + x, he⟩⟩
    refine ⟨z, rfl, ?_⟩
    have hs : P.shiftedOperator z = y + x := by
      apply P.operatorInverse_injective
      exact (inverseOperator_right_inverse P.operatorInverse P.operatorInverse_injective z).trans he.symm
    rw [P.operator_apply, hs]
    change y + x - x = y
    exact add_sub_cancel_right y x

theorem GraphShiftedContactOperatorProblem.operator_isClosed
    (P : GraphShiftedContactOperatorProblem V E) : P.operator.IsClosed := by
  have he : (P.operator.graph : Set (GraphL2Product P.geometry × GraphL2Product P.geometry)) =
      {p | P.operatorInverse (p.2 + p.1) = p.1} := by
    ext p
    exact P.operator_graph_iff p.1 p.2
  change IsClosed (P.operator.graph : Set (GraphL2Product P.geometry × GraphL2Product P.geometry))
  rw [he]
  exact isClosed_eq (P.operatorInverse.continuous.comp (continuous_snd.add continuous_fst)) continuous_fst

theorem GraphShiftedContactOperatorProblem.operator_dense_domain
    (P : GraphShiftedContactOperatorProblem V E) :
    Dense (P.operator.domain : Set (GraphL2Product P.geometry)) :=
  inverseOperator_dense_domain P.operatorInverse P.operatorInverse_injective P.operatorInverse_symmetric

theorem GraphShiftedContactOperatorProblem.operator_nonneg
    (P : GraphShiftedContactOperatorProblem V E) (u : P.operator.domain) :
    0 ≤ inner ℝ (u : GraphL2Product P.geometry) (P.operator u) := by
  let f := P.shiftedOperator u
  have hs : graphSobolevSpaceStateL P.geometry (P.operatorSolution f) =
      (u : GraphL2Product P.geometry) :=
    inverseOperator_right_inverse P.operatorInverse P.operatorInverse_injective u
  have hw := P.operatorSolution_spec f (P.operatorSolution f)
  rw [P.operatorForm_eq, hs] at hw
  have hc : inner ℝ f (u : GraphL2Product P.geometry) =
      inner ℝ (u : GraphL2Product P.geometry) f := real_inner_comm _ _
  rw [hc] at hw
  rw [P.operator_apply, inner_sub_right]
  change 0 ≤ inner ℝ (u : GraphL2Product P.geometry) f - inner ℝ (u : GraphL2Product P.geometry) u
  linarith [P.contactForm_nonneg (P.operatorSolution f)]

end TimeTraps.Analysis
