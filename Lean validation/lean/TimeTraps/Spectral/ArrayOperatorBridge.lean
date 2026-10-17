module

public import TimeTraps.Spectral.ArrayOperatorData
public import TimeTraps.Analysis.IntervalPeriodicSpectrum
public import TimeTraps.Analysis.CompactInverseEigenvalue

@[expose] public section

/-! The original arbitrary-array weak eigenvalue equation is precisely the
actual periodic operator equation. Every operator eigenvalue belongs to the
independent physical Rayleigh class. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis IntervalSobolevSpace

variable {n : ℕ}

theorem PeriodicArray.operator_weak_iff (P : PeriodicArray n)
    (u : IntervalPeriodicSpace P.operatorBoundary) (ev : ℝ) :
    (P.operatorBoundary.stateL u, ev • P.operatorBoundary.stateL u) ∈
      P.periodicPointProblem.operator.graph ↔
        ArrayWeakEigenEquation P ev (u.val.representative P.length_pos) := by
  change (P.periodicPointProblem.boundary.stateL u,
    ev • P.periodicPointProblem.boundary.stateL u) ∈ P.periodicPointProblem.operator.graph ↔ _
  rw [P.periodicPointProblem.operator_eigen_iff_physical]
  constructor
  · intro h
    refine ⟨P.operator_energy u, ?_⟩
    intro v hv
    exact h v hv.1 hv.2
  · intro h v hv hp
    exact h.weak_form v ⟨hv, hp⟩

theorem PeriodicArray.operator_eigenbasis_weak (P : PeriodicArray n)
    (i : CompactSpectralIndex P.periodicPointProblem.inverse) :
    ArrayWeakEigenEquation P i.1⁻¹
      ((P.periodicPointProblem.eigenstate i).val.representative P.length_pos) := by
  apply (P.operator_weak_iff _ _).mp
  change (P.periodicPointProblem.boundary.stateL (P.periodicPointProblem.eigenstate i),
    i.1⁻¹ • P.periodicPointProblem.boundary.stateL (P.periodicPointProblem.eigenstate i)) ∈ _
  rw [P.periodicPointProblem.eigenstate_state]
  exact P.periodicPointProblem.eigenbasis_operator_graph i

theorem PeriodicArray.operator_eigenvalue_rayleigh (P : PeriodicArray n)
    (i : CompactSpectralIndex P.periodicPointProblem.inverse) : i.1⁻¹ ∈ P.rayleighValues := by
  let u := P.periodicPointProblem.eigenstate i
  have he := P.operator_eigenbasis_weak i
  have hm : 0 < P.squareMass (u.val.representative P.length_pos) := by
    rw [P.operator_squareMass u]
    change 0 < ‖P.periodicPointProblem.boundary.stateL
      (P.periodicPointProblem.eigenstate i)‖ ^ 2
    rw [P.periodicPointProblem.eigenstate_state]
    exact sq_pos_of_pos (norm_pos_iff.mpr
      (P.periodicPointProblem.eigenbasis.orthonormal.ne_zero i))
  refine ⟨u.val.representative P.length_pos, he.energy, hm, ?_⟩
  rw [he.self_quadraticForm, mul_div_cancel_right₀ _ hm.ne']

theorem PeriodicArray.principal_le_operator_eigenvalue (P : PeriodicArray n)
    (i : CompactSpectralIndex P.periodicPointProblem.inverse) : P.principalValue ≤ i.1⁻¹ :=
  P.rayleigh_minimum.2 (P.operator_eigenvalue_rayleigh i)

end TimeTraps.Spectral
