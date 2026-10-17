module

public import TimeTraps.Analysis.SignedPeriodicPointInverse
public import TimeTraps.Analysis.ShiftedInverseOperatorAdjoint

@[expose] public section

/-! The original signed periodic operator is the translated inverse
of the actual shifted solution. Its dense closed self-adjoint graph is
exactly the unshifted form on the full endpoint-matched periodic H1 space. -/

namespace TimeTraps.Analysis

open Set InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable def SignedPeriodicPointProblem.operator (P : SignedPeriodicPointProblem ι l r) :
    IntervalSobolevL2 l r →ₗ.[ℝ] IntervalSobolevL2 l r :=
  translatedInverseOperator P.shiftedInverse P.shiftedInverse_injective P.massShift

theorem SignedPeriodicPointProblem.shiftedForm_eq (P : SignedPeriodicPointProblem ι l r)
    (u v : IntervalPeriodicSpace P.boundary) :
    P.shiftedForm u v = P.form u v + P.massShift *
      inner ℝ (P.boundary.stateL u) (P.boundary.stateL v) := rfl

theorem SignedPeriodicPointProblem.operator_domain (P : SignedPeriodicPointProblem ι l r) :
    P.operator.domain = P.shiftedInverse.range := rfl

theorem SignedPeriodicPointProblem.operator_dense_domain (P : SignedPeriodicPointProblem ι l r) :
    Dense (P.operator.domain : Set (IntervalSobolevL2 l r)) :=
  translatedInverseOperator_dense_domain P.shiftedInverse P.shiftedInverse_injective
    P.shiftedInverse_symmetric P.massShift

theorem SignedPeriodicPointProblem.operator_closed (P : SignedPeriodicPointProblem ι l r) :
    P.operator.IsClosed :=
  translatedInverseOperator_isClosed P.shiftedInverse P.shiftedInverse_injective P.massShift

theorem SignedPeriodicPointProblem.operator_selfAdjoint (P : SignedPeriodicPointProblem ι l r) :
    IsSelfAdjoint P.operator :=
  translatedInverseOperator_isSelfAdjoint P.shiftedInverse P.shiftedInverse_injective
    P.shiftedInverse_symmetric P.massShift

theorem SignedPeriodicPointProblem.operator_graph_iff (P : SignedPeriodicPointProblem ι l r)
    (u f : IntervalSobolevL2 l r) :
    (u, f) ∈ P.operator.graph ↔ P.shiftedInverse (f + P.massShift • u) = u :=
  translatedInverseOperator_graph_iff P.shiftedInverse P.shiftedInverse_injective P.massShift u f

theorem SignedPeriodicPointProblem.operator_graph_iff_hilbert
    (P : SignedPeriodicPointProblem ι l r) (u f : IntervalSobolevL2 l r) :
    (u, f) ∈ P.operator.graph ↔ ∃ v : IntervalPeriodicSpace P.boundary,
      P.boundary.stateL v = u ∧ ∀ w : IntervalPeriodicSpace P.boundary,
        P.form v w = inner ℝ f (P.boundary.stateL w) := by
  rw [P.operator_graph_iff]
  constructor
  · intro h
    refine ⟨P.shiftedSolution (f + P.massShift • u), h, fun w => ?_⟩
    have he := P.shiftedSolution_spec (f + P.massShift • u) w
    rw [P.shiftedForm_eq, inner_add_left, real_inner_smul_left] at he
    change P.boundary.stateL (P.shiftedSolution (f + P.massShift • u)) = u at h
    rw [h] at he
    exact add_right_cancel he
  · rintro ⟨v, hv, he⟩
    have hs : v = P.shiftedSolution (f + P.massShift • u) := by
      apply (P.shiftedSolution_eq_iff _ v).mpr
      intro w
      rw [P.shiftedForm_eq, inner_add_left, real_inner_smul_left, hv, he w]
    rw [hs] at hv
    exact hv

theorem SignedPeriodicPointProblem.operator_graph_iff_state
    (P : SignedPeriodicPointProblem ι l r) (u : IntervalPeriodicSpace P.boundary)
    (f : IntervalSobolevL2 l r) :
    (P.boundary.stateL u, f) ∈ P.operator.graph ↔
      ∀ v : IntervalPeriodicSpace P.boundary, P.form u v = inner ℝ f (P.boundary.stateL v) := by
  rw [P.operator_graph_iff_hilbert]
  constructor
  · rintro ⟨v, hv, he⟩
    have h : v = u := P.boundary.stateL_injective hv
    rwa [h] at he
  · intro h
    exact ⟨u, rfl, h⟩

theorem SignedPeriodicPointProblem.form_semibounded (P : SignedPeriodicPointProblem ι l r)
    (u : IntervalPeriodicSpace P.boundary) :
    -(intervalPointNegativeBound P.diffusivity P.strength l r * ‖P.boundary.stateL u‖ ^ 2) ≤
      P.form u u :=
  intervalPeriodicPointForm_semibounded P.boundary P.diffusivity_pos P.strength P.site P.site_mem u

theorem SignedPeriodicPointProblem.operator_semibounded (P : SignedPeriodicPointProblem ι l r)
    (u : P.operator.domain) :
    -(intervalPointNegativeBound P.diffusivity P.strength l r * ‖(u : IntervalSobolevL2 l r)‖ ^ 2) ≤
      inner ℝ (u : IntervalSobolevL2 l r) (P.operator u) := by
  obtain ⟨v, hv, he⟩ := (P.operator_graph_iff_hilbert _ _).mp (P.operator.mem_graph u)
  have h := P.form_semibounded v
  rw [he v, hv] at h
  simpa only [real_inner_comm (u : IntervalSobolevL2 l r) (P.operator u)] using h

end TimeTraps.Analysis
