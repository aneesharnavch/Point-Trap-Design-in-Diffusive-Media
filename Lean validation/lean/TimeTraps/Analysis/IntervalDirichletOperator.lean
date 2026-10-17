module

public import TimeTraps.Analysis.IntervalDirichletPositive
public import TimeTraps.Analysis.InverseOperatorAdjoint

@[expose] public section

/-! The densely defined closed self-adjoint inverse of the actual compact
Dirichlet solution operator. Its graph is characterized by the full
zero-boundary Hilbert variational equation with arbitrary L2 forcing. -/

namespace TimeTraps.Analysis

open Set IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable def DirichletPointProblem.operator (P : DirichletPointProblem ι l r) :
    IntervalSobolevL2 l r →ₗ.[ℝ] IntervalSobolevL2 l r :=
  inverseOperator P.inverse P.inverse_injective

theorem DirichletPointProblem.operator_domain (P : DirichletPointProblem ι l r) :
    P.operator.domain = P.inverse.range := rfl

theorem DirichletPointProblem.operator_dense_domain (P : DirichletPointProblem ι l r) :
    Dense (P.operator.domain : Set (IntervalSobolevL2 l r)) :=
  inverseOperator_dense_domain P.inverse P.inverse_injective P.inverse_symmetric

theorem DirichletPointProblem.operator_closed (P : DirichletPointProblem ι l r) :
    P.operator.IsClosed := inverseOperator_isClosed P.inverse P.inverse_injective

theorem DirichletPointProblem.operator_selfAdjoint (P : DirichletPointProblem ι l r) :
    IsSelfAdjoint P.operator :=
  inverseOperator_isSelfAdjoint P.inverse P.inverse_injective P.inverse_symmetric

theorem DirichletPointProblem.operator_graph_iff (P : DirichletPointProblem ι l r)
    (u f : IntervalSobolevL2 l r) : (u, f) ∈ P.operator.graph ↔ P.inverse f = u :=
  inverseOperator_graph_iff P.inverse P.inverse_injective u f

theorem DirichletPointProblem.operator_graph_iff_hilbert (P : DirichletPointProblem ι l r)
    (u f : IntervalSobolevL2 l r) :
    (u, f) ∈ P.operator.graph ↔ ∃ v : IntervalDirichletSpace P.boundary,
      P.boundary.stateL v = u ∧ ∀ w : IntervalDirichletSpace P.boundary,
        P.form v w = inner ℝ f (P.boundary.stateL w) := by
  rw [P.operator_graph_iff]
  constructor
  · intro h
    exact ⟨P.solution f, h, P.solution_spec f⟩
  · rintro ⟨v, hv, he⟩
    rw [(P.solution_eq_iff f v).mpr he] at hv
    exact hv

theorem DirichletPointProblem.operator_positive (P : DirichletPointProblem ι l r)
    (u : P.operator.domain) (hu : (u : IntervalSobolevL2 l r) ≠ 0) :
    0 < inner ℝ (u : IntervalSobolevL2 l r) (P.operator u) := by
  have hi : P.inverse (P.operator u) = u :=
    inverseOperator_right_inverse P.inverse P.inverse_injective u
  have hf : P.operator u ≠ 0 := by
    intro h
    rw [h, map_zero] at hi
    exact hu hi.symm
  have hp := P.inverse_positive hf
  rw [hi] at hp
  exact hp.trans_eq (real_inner_comm _ _)

end TimeTraps.Analysis
