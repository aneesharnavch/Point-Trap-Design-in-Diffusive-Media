module

public import TimeTraps.Analysis.SignedIntervalPointOperator
public import TimeTraps.Analysis.ShiftedInverseOperatorAdjoint

@[expose] public section

/-! The original signed point-interaction operator, after removing the
auxiliary coercive mass shift. Its actual graph and full H1 form are
identified exactly; zero and negative eigenvalues are not excluded. -/

namespace TimeTraps.Analysis

open Set IntervalSobolevSpace
open scoped InnerProductSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable def SignedIntervalPointProblem.form (P : SignedIntervalPointProblem ι l r) :
    IntervalSobolevSpace l r →L[ℝ] IntervalSobolevSpace l r →L[ℝ] ℝ :=
  intervalSobolevPointForm P.interval_pos P.diffusivity P.strength P.site P.site_mem

noncomputable def SignedIntervalPointProblem.operator (P : SignedIntervalPointProblem ι l r) :
    IntervalSobolevL2 l r →ₗ.[ℝ] IntervalSobolevL2 l r :=
  translatedInverseOperator P.shiftedInverse P.shiftedInverse_injective P.massShift

theorem SignedIntervalPointProblem.shiftedForm_eq (P : SignedIntervalPointProblem ι l r)
    (u v : IntervalSobolevSpace l r) :
    P.shiftedForm u v = P.form u v + P.massShift * ⟪u.state, v.state⟫_ℝ := rfl

theorem SignedIntervalPointProblem.operator_domain (P : SignedIntervalPointProblem ι l r) :
    P.operator.domain = P.shiftedInverse.range := rfl

theorem SignedIntervalPointProblem.operator_dense_domain (P : SignedIntervalPointProblem ι l r) :
    Dense (P.operator.domain : Set (IntervalSobolevL2 l r)) :=
  translatedInverseOperator_dense_domain P.shiftedInverse P.shiftedInverse_injective
    P.shiftedInverse_symmetric P.massShift

theorem SignedIntervalPointProblem.operator_closed (P : SignedIntervalPointProblem ι l r) :
    P.operator.IsClosed :=
  translatedInverseOperator_isClosed P.shiftedInverse P.shiftedInverse_injective P.massShift

theorem SignedIntervalPointProblem.operator_selfAdjoint (P : SignedIntervalPointProblem ι l r) :
    IsSelfAdjoint P.operator :=
  translatedInverseOperator_isSelfAdjoint P.shiftedInverse P.shiftedInverse_injective
    P.shiftedInverse_symmetric P.massShift

theorem SignedIntervalPointProblem.operator_graph_iff (P : SignedIntervalPointProblem ι l r)
    (u f : IntervalSobolevL2 l r) :
    (u, f) ∈ P.operator.graph ↔ P.shiftedInverse (f + P.massShift • u) = u :=
  translatedInverseOperator_graph_iff P.shiftedInverse P.shiftedInverse_injective P.massShift u f

theorem SignedIntervalPointProblem.operator_graph_iff_shifted (P : SignedIntervalPointProblem ι l r)
    (u f : IntervalSobolevL2 l r) :
    (u, f) ∈ P.operator.graph ↔ (u, f + P.massShift • u) ∈ P.shiftedOperator.graph := by
  rw [P.operator_graph_iff, P.shiftedOperator_graph_iff]

theorem SignedIntervalPointProblem.operator_graph_iff_hilbert (P : SignedIntervalPointProblem ι l r)
    (u f : IntervalSobolevL2 l r) :
    (u, f) ∈ P.operator.graph ↔ ∃ v : IntervalSobolevSpace l r, v.state = u ∧
      ∀ w : IntervalSobolevSpace l r, P.form v w = ⟪f, w.state⟫_ℝ := by
  rw [P.operator_graph_iff_shifted, P.shiftedOperator_graph_iff_hilbert]
  constructor
  · rintro ⟨v, hv, he⟩
    refine ⟨v, hv, fun w => ?_⟩
    have h := he w
    rw [P.shiftedForm_eq, inner_add_left, real_inner_smul_left, hv] at h
    exact add_right_cancel h
  · rintro ⟨v, hv, he⟩
    refine ⟨v, hv, fun w => ?_⟩
    rw [P.shiftedForm_eq, inner_add_left, real_inner_smul_left, hv, he w]

theorem SignedIntervalPointProblem.operator_graph_iff_state (P : SignedIntervalPointProblem ι l r)
    (u : IntervalSobolevSpace l r) (f : IntervalSobolevL2 l r) :
    (u.state, f) ∈ P.operator.graph ↔
      ∀ v : IntervalSobolevSpace l r, P.form u v = ⟪f, v.state⟫_ℝ := by
  rw [P.operator_graph_iff_hilbert]
  constructor
  · rintro ⟨v, hv, he⟩
    have h : v = u := ext_state hv
    rwa [h] at he
  · intro h
    exact ⟨u, rfl, h⟩

theorem SignedIntervalPointProblem.form_semibounded (P : SignedIntervalPointProblem ι l r)
    (u : IntervalSobolevSpace l r) :
    -(intervalPointNegativeBound P.diffusivity P.strength l r * ‖u.state‖ ^ 2) ≤ P.form u u :=
  intervalSobolevPointForm_semibounded P.interval_pos P.diffusivity_pos P.strength P.site P.site_mem u

theorem SignedIntervalPointProblem.operator_semibounded (P : SignedIntervalPointProblem ι l r)
    (u : P.operator.domain) :
    -(intervalPointNegativeBound P.diffusivity P.strength l r * ‖(u : IntervalSobolevL2 l r)‖ ^ 2) ≤
      ⟪(u : IntervalSobolevL2 l r), P.operator u⟫_ℝ := by
  obtain ⟨v, hv, he⟩ := (P.operator_graph_iff_hilbert _ _).mp (P.operator.mem_graph u)
  have h := P.form_semibounded v
  rw [he v, hv] at h
  simpa only [real_inner_comm (u : IntervalSobolevL2 l r) (P.operator u)] using h

end TimeTraps.Analysis
