module

public import TimeTraps.Analysis.SignedIntervalPointWeak
public import TimeTraps.Analysis.InverseOperatorAdjoint

@[expose] public section

/-! The actual densely defined, closed self-adjoint shifted operator.
It is the inverse of the compact mass-shifted solution map; its physical
graph includes the mass shift explicitly. No unshifted operator is defined. -/

namespace TimeTraps.Analysis

open Set IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable def SignedIntervalPointProblem.shiftedOperator (P : SignedIntervalPointProblem ι l r) :
    IntervalSobolevL2 l r →ₗ.[ℝ] IntervalSobolevL2 l r :=
  inverseOperator P.shiftedInverse P.shiftedInverse_injective

theorem SignedIntervalPointProblem.shiftedOperator_domain (P : SignedIntervalPointProblem ι l r) :
    P.shiftedOperator.domain = P.shiftedInverse.range := rfl

theorem SignedIntervalPointProblem.shiftedOperator_dense_domain (P : SignedIntervalPointProblem ι l r) :
    Dense (P.shiftedOperator.domain : Set (IntervalSobolevL2 l r)) :=
  inverseOperator_dense_domain P.shiftedInverse P.shiftedInverse_injective P.shiftedInverse_symmetric

theorem SignedIntervalPointProblem.shiftedOperator_closed (P : SignedIntervalPointProblem ι l r) :
    P.shiftedOperator.IsClosed :=
  inverseOperator_isClosed P.shiftedInverse P.shiftedInverse_injective

theorem SignedIntervalPointProblem.shiftedOperator_selfAdjoint (P : SignedIntervalPointProblem ι l r) :
    IsSelfAdjoint P.shiftedOperator :=
  inverseOperator_isSelfAdjoint P.shiftedInverse P.shiftedInverse_injective P.shiftedInverse_symmetric

theorem SignedIntervalPointProblem.shiftedOperator_graph_iff (P : SignedIntervalPointProblem ι l r)
    (u f : IntervalSobolevL2 l r) : (u, f) ∈ P.shiftedOperator.graph ↔ P.shiftedInverse f = u :=
  inverseOperator_graph_iff P.shiftedInverse P.shiftedInverse_injective u f

theorem SignedIntervalPointProblem.shiftedOperator_graph_iff_hilbert (P : SignedIntervalPointProblem ι l r)
    (u f : IntervalSobolevL2 l r) :
    (u, f) ∈ P.shiftedOperator.graph ↔ ∃ v : IntervalSobolevSpace l r, v.state = u ∧
      ∀ w : IntervalSobolevSpace l r, P.shiftedForm v w = inner ℝ f w.state := by
  rw [P.shiftedOperator_graph_iff]
  constructor
  · intro h
    exact ⟨P.shiftedSolution f, h, P.shiftedSolution_spec f⟩
  · rintro ⟨v, hv, he⟩
    rw [(P.shiftedSolution_eq_iff f v).mpr he] at hv
    exact hv

theorem SignedIntervalPointProblem.shiftedOperator_graph_iff_physical (P : SignedIntervalPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r) :
    ((ofEnergy hu P.interval_pos).state, f) ∈ P.shiftedOperator.graph ↔
      ∀ v : ℝ → ℝ, IntervalEnergy v l r →
        intervalPointForm P.diffusivity P.strength P.site l r u v +
          P.massShift * (∫ x in l..r, u x * v x) = ∫ x in l..r, f x * v x := by
  rw [P.shiftedOperator_graph_iff, P.shiftedInverse_eq_iff_weak f hu]

theorem SignedIntervalPointProblem.shiftedOperator_positive (P : SignedIntervalPointProblem ι l r)
    (u : P.shiftedOperator.domain) (hu : (u : IntervalSobolevL2 l r) ≠ 0) :
    0 < inner ℝ (u : IntervalSobolevL2 l r) (P.shiftedOperator u) := by
  have hi : P.shiftedInverse (P.shiftedOperator u) = u :=
    inverseOperator_right_inverse P.shiftedInverse P.shiftedInverse_injective u
  have hf : P.shiftedOperator u ≠ 0 := by
    intro h
    rw [h, map_zero] at hi
    exact hu hi.symm
  have hp := P.shiftedInverse_positive hf
  rw [hi] at hp
  exact hp.trans_eq (real_inner_comm _ _)

end TimeTraps.Analysis
