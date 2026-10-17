module

public import TimeTraps.Analysis.RegularSturmInverse
public import TimeTraps.Analysis.ShiftedInverseOperatorAdjoint

@[expose] public section

/-! The original regular Sturm operator in the speed-weighted representation is the translated inverse
of the actual shifted solution. Its dense closed self-adjoint graph is
exactly the unshifted form on the full selected-endpoint H1 space with variable conductance, speed and potential. -/

namespace TimeTraps.Analysis

open Set InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable def RegularSturmProblem.operator (P : RegularSturmProblem ι l r) :
    IntervalSobolevL2 l r →ₗ.[ℝ] IntervalSobolevL2 l r :=
  translatedInverseOperator P.shiftedInverse P.shiftedInverse_injective P.massShift

theorem RegularSturmProblem.shiftedForm_eq (P : RegularSturmProblem ι l r)
    (u v : IntervalSeparatedSpace P.boundary) :
    P.shiftedForm u v = P.form u v + P.massShift *
      inner ℝ (P.stateL u) (P.stateL v) := rfl

theorem RegularSturmProblem.operator_domain (P : RegularSturmProblem ι l r) :
    P.operator.domain = P.shiftedInverse.range := rfl

theorem RegularSturmProblem.operator_dense_domain (P : RegularSturmProblem ι l r) :
    Dense (P.operator.domain : Set (IntervalSobolevL2 l r)) :=
  translatedInverseOperator_dense_domain P.shiftedInverse P.shiftedInverse_injective
    P.shiftedInverse_symmetric P.massShift

theorem RegularSturmProblem.operator_closed (P : RegularSturmProblem ι l r) :
    P.operator.IsClosed :=
  translatedInverseOperator_isClosed P.shiftedInverse P.shiftedInverse_injective P.massShift

theorem RegularSturmProblem.operator_selfAdjoint (P : RegularSturmProblem ι l r) :
    IsSelfAdjoint P.operator :=
  translatedInverseOperator_isSelfAdjoint P.shiftedInverse P.shiftedInverse_injective
    P.shiftedInverse_symmetric P.massShift

theorem RegularSturmProblem.operator_graph_iff (P : RegularSturmProblem ι l r)
    (u f : IntervalSobolevL2 l r) :
    (u, f) ∈ P.operator.graph ↔ P.shiftedInverse (f + P.massShift • u) = u :=
  translatedInverseOperator_graph_iff P.shiftedInverse P.shiftedInverse_injective P.massShift u f

theorem RegularSturmProblem.operator_graph_iff_hilbert
    (P : RegularSturmProblem ι l r) (u f : IntervalSobolevL2 l r) :
    (u, f) ∈ P.operator.graph ↔ ∃ v : IntervalSeparatedSpace P.boundary,
      P.stateL v = u ∧ ∀ w : IntervalSeparatedSpace P.boundary,
        P.form v w = inner ℝ f (P.stateL w) := by
  rw [P.operator_graph_iff]
  constructor
  · intro h
    refine ⟨P.shiftedSolution (f + P.massShift • u), h, fun w => ?_⟩
    have he := P.shiftedSolution_spec (f + P.massShift • u) w
    rw [P.shiftedForm_eq, inner_add_left, real_inner_smul_left] at he
    change P.stateL (P.shiftedSolution (f + P.massShift • u)) = u at h
    rw [h] at he
    exact add_right_cancel he
  · rintro ⟨v, hv, he⟩
    have hs : v = P.shiftedSolution (f + P.massShift • u) := by
      apply (P.shiftedSolution_eq_iff _ v).mpr
      intro w
      rw [P.shiftedForm_eq, inner_add_left, real_inner_smul_left, hv, he w]
    rw [hs] at hv
    exact hv

theorem RegularSturmProblem.operator_graph_iff_state
    (P : RegularSturmProblem ι l r) (u : IntervalSeparatedSpace P.boundary)
    (f : IntervalSobolevL2 l r) :
    (P.stateL u, f) ∈ P.operator.graph ↔
      ∀ v : IntervalSeparatedSpace P.boundary, P.form u v = inner ℝ f (P.stateL v) := by
  rw [P.operator_graph_iff_hilbert]
  constructor
  · rintro ⟨v, hv, he⟩
    have h : v = u := P.stateL_injective hv
    rwa [h] at he
  · intro h
    exact ⟨u, rfl, h⟩

theorem RegularSturmProblem.form_semibounded (P : RegularSturmProblem ι l r)
    (u : IntervalSeparatedSpace P.boundary) :
    -(P.massShift * ‖P.stateL u‖ ^ 2) ≤ P.form u u := by
  obtain ⟨c, hc, hb⟩ := P.shiftedForm_coercive
  have h := hb u
  rw [P.shiftedForm_eq, real_inner_self_eq_norm_sq] at h
  have hp := mul_nonneg (mul_nonneg hc.le (norm_nonneg u)) (norm_nonneg u)
  linarith

theorem RegularSturmProblem.operator_semibounded (P : RegularSturmProblem ι l r)
    (u : P.operator.domain) :
    -(P.massShift * ‖(u : IntervalSobolevL2 l r)‖ ^ 2) ≤
      inner ℝ (u : IntervalSobolevL2 l r) (P.operator u) := by
  obtain ⟨v, hv, he⟩ := (P.operator_graph_iff_hilbert _ _).mp (P.operator.mem_graph u)
  have h := P.form_semibounded v
  rw [he v, hv] at h
  simpa only [real_inner_comm (u : IntervalSobolevL2 l r) (P.operator u)] using h

end TimeTraps.Analysis
