module

public import TimeTraps.Analysis.IntervalPeriodicPositive
public import TimeTraps.Analysis.InverseOperatorAdjoint

@[expose] public section

/-! The densely defined closed self-adjoint inverse of the actual compact
periodic solution operator. Its graph is characterized by the full
periodic Hilbert variational equation with arbitrary L2 forcing. -/

namespace TimeTraps.Analysis

open Set IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable def PeriodicPointProblem.operator (P : PeriodicPointProblem ι l r) :
    IntervalSobolevL2 l r →ₗ.[ℝ] IntervalSobolevL2 l r :=
  inverseOperator P.inverse P.inverse_injective

theorem PeriodicPointProblem.operator_domain (P : PeriodicPointProblem ι l r) :
    P.operator.domain = P.inverse.range := rfl

theorem PeriodicPointProblem.operator_dense_domain (P : PeriodicPointProblem ι l r) :
    Dense (P.operator.domain : Set (IntervalSobolevL2 l r)) :=
  inverseOperator_dense_domain P.inverse P.inverse_injective P.inverse_symmetric

theorem PeriodicPointProblem.operator_closed (P : PeriodicPointProblem ι l r) :
    P.operator.IsClosed := inverseOperator_isClosed P.inverse P.inverse_injective

theorem PeriodicPointProblem.operator_selfAdjoint (P : PeriodicPointProblem ι l r) :
    IsSelfAdjoint P.operator :=
  inverseOperator_isSelfAdjoint P.inverse P.inverse_injective P.inverse_symmetric

theorem PeriodicPointProblem.operator_graph_iff (P : PeriodicPointProblem ι l r)
    (u f : IntervalSobolevL2 l r) : (u, f) ∈ P.operator.graph ↔ P.inverse f = u :=
  inverseOperator_graph_iff P.inverse P.inverse_injective u f

theorem PeriodicPointProblem.operator_graph_iff_hilbert (P : PeriodicPointProblem ι l r)
    (u f : IntervalSobolevL2 l r) :
    (u, f) ∈ P.operator.graph ↔ ∃ v : IntervalPeriodicSpace P.boundary,
      P.boundary.stateL v = u ∧ ∀ w : IntervalPeriodicSpace P.boundary,
        P.form v w = inner ℝ f (P.boundary.stateL w) := by
  rw [P.operator_graph_iff]
  constructor
  · intro h
    exact ⟨P.solution f, h, P.solution_spec f⟩
  · rintro ⟨v, hv, he⟩
    rw [(P.solution_eq_iff f v).mpr he] at hv
    exact hv

theorem PeriodicPointProblem.operator_positive (P : PeriodicPointProblem ι l r)
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
