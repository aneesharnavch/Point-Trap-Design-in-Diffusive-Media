module

public import TimeTraps.Analysis.IntervalSobolevOperatorWeak
public import TimeTraps.Analysis.InverseOperatorAdjoint

@[expose] public section

/-! The densely defined self-adjoint operator of the actual interval form.
Its domain is characterized by the full physical weak equation with an L2
right-hand side; no closed-range or boundedness of this operator is claimed. -/

namespace TimeTraps.Analysis

open Set IntervalSobolevSpace

variable {ι : Type*} [Fintype ι]

noncomputable def UnitPointProblem.operator (P : UnitPointProblem ι) :
    UnitIntervalL2 →ₗ.[ℝ] UnitIntervalL2 := inverseOperator P.inverse P.inverse_injective

theorem UnitPointProblem.operator_domain (P : UnitPointProblem ι) :
    P.operator.domain = P.inverse.range := rfl

theorem UnitPointProblem.operator_dense_domain (P : UnitPointProblem ι) :
    Dense (P.operator.domain : Set UnitIntervalL2) :=
  inverseOperator_dense_domain P.inverse P.inverse_injective P.inverse_symmetric

theorem UnitPointProblem.operator_closed (P : UnitPointProblem ι) : P.operator.IsClosed :=
  inverseOperator_isClosed P.inverse P.inverse_injective

theorem UnitPointProblem.operator_selfAdjoint (P : UnitPointProblem ι) :
    IsSelfAdjoint P.operator :=
  inverseOperator_isSelfAdjoint P.inverse P.inverse_injective P.inverse_symmetric

theorem UnitPointProblem.operator_graph_iff (P : UnitPointProblem ι)
    (u f : UnitIntervalL2) : (u, f) ∈ P.operator.graph ↔ P.inverse f = u :=
  inverseOperator_graph_iff P.inverse P.inverse_injective u f

theorem UnitPointProblem.operator_graph_iff_hilbert (P : UnitPointProblem ι)
    (u f : UnitIntervalL2) :
    (u, f) ∈ P.operator.graph ↔ ∃ v : UnitIntervalSobolev, v.state = u ∧
      ∀ w : UnitIntervalSobolev, P.form v w = inner ℝ f w.state := by
  rw [P.operator_graph_iff]
  constructor
  · intro h
    exact ⟨P.solution f, h, P.solution_spec f⟩
  · rintro ⟨v, hv, he⟩
    rw [(P.solution_eq_iff f v).mpr he] at hv
    exact hv

theorem UnitPointProblem.operator_graph_iff_physical (P : UnitPointProblem ι)
    (f : UnitIntervalL2) {u : ℝ → ℝ} (hu : IntervalEnergy u 0 1) :
    ((ofEnergy hu zero_lt_one).state, f) ∈ P.operator.graph ↔
      ∀ v : ℝ → ℝ, IntervalEnergy v 0 1 →
        unitPointForm P.diffusivity P.strength P.site u v = ∫ x in (0 : ℝ)..1, f x * v x := by
  rw [P.operator_graph_iff, P.inverse_eq_iff_weak f hu]

theorem UnitPointProblem.operator_positive (P : UnitPointProblem ι)
    (u : P.operator.domain) (hu : (u : UnitIntervalL2) ≠ 0) :
    0 < inner ℝ (u : UnitIntervalL2) (P.operator u) := by
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
