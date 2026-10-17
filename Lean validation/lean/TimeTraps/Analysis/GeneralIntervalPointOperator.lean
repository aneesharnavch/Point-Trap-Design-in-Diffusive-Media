module

public import TimeTraps.Analysis.GeneralIntervalPointWeak
public import TimeTraps.Analysis.InverseOperatorAdjoint

@[expose] public section

/-! The densely defined self-adjoint operator of the actual interval form.
Its domain is characterized by the full physical weak equation with an L2
right-hand side; no closed-range or boundedness of this operator is claimed. -/

namespace TimeTraps.Analysis

open Set IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable def IntervalPointProblem.operator (P : IntervalPointProblem ι l r) :
    IntervalSobolevL2 l r →ₗ.[ℝ] IntervalSobolevL2 l r := inverseOperator P.inverse P.inverse_injective

theorem IntervalPointProblem.operator_domain (P : IntervalPointProblem ι l r) :
    P.operator.domain = P.inverse.range := rfl

theorem IntervalPointProblem.operator_dense_domain (P : IntervalPointProblem ι l r) :
    Dense (P.operator.domain : Set (IntervalSobolevL2 l r)) :=
  inverseOperator_dense_domain P.inverse P.inverse_injective P.inverse_symmetric

theorem IntervalPointProblem.operator_closed (P : IntervalPointProblem ι l r) : P.operator.IsClosed :=
  inverseOperator_isClosed P.inverse P.inverse_injective

theorem IntervalPointProblem.operator_selfAdjoint (P : IntervalPointProblem ι l r) :
    IsSelfAdjoint P.operator :=
  inverseOperator_isSelfAdjoint P.inverse P.inverse_injective P.inverse_symmetric

theorem IntervalPointProblem.operator_graph_iff (P : IntervalPointProblem ι l r)
    (u f : IntervalSobolevL2 l r) : (u, f) ∈ P.operator.graph ↔ P.inverse f = u :=
  inverseOperator_graph_iff P.inverse P.inverse_injective u f

theorem IntervalPointProblem.operator_graph_iff_hilbert (P : IntervalPointProblem ι l r)
    (u f : IntervalSobolevL2 l r) :
    (u, f) ∈ P.operator.graph ↔ ∃ v : IntervalSobolevSpace l r, v.state = u ∧
      ∀ w : IntervalSobolevSpace l r, P.form v w = inner ℝ f w.state := by
  rw [P.operator_graph_iff]
  constructor
  · intro h
    exact ⟨P.solution f, h, P.solution_spec f⟩
  · rintro ⟨v, hv, he⟩
    rw [(P.solution_eq_iff f v).mpr he] at hv
    exact hv

theorem IntervalPointProblem.operator_graph_iff_physical (P : IntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r) :
    ((ofEnergy hu P.interval_pos).state, f) ∈ P.operator.graph ↔
      ∀ v : ℝ → ℝ, IntervalEnergy v l r →
        intervalPointForm P.diffusivity P.strength P.site l r u v = ∫ x in l..r, f x * v x := by
  rw [P.operator_graph_iff, P.inverse_eq_iff_weak f hu]

theorem IntervalPointProblem.operator_positive (P : IntervalPointProblem ι l r)
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
