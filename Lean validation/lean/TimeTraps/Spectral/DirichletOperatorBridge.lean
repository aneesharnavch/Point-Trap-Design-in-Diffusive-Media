module

public import TimeTraps.Spectral.DirichletOperatorData
public import TimeTraps.Analysis.IntervalDirichletSpectrum
public import TimeTraps.Analysis.CompactInverseEigenvalue

@[expose] public section

/-! Exact weak correspondence for the original full admissible H1 class,
and inclusion of every constructed operator eigenvalue in its independent
Rayleigh value set. No spectral or minimization premise is supplied. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis IntervalSobolevSpace

theorem DirichletInterval.operator_weak_iff (P : DirichletInterval)
    (u : IntervalDirichletSpace P.operatorBoundary) (ev : ℝ) :
    (P.operatorBoundary.stateL u, ev • P.operatorBoundary.stateL u) ∈
      P.dirichletPointProblem.operator.graph ↔
        DirichletWeakEigenEquation P ev (u.val.representative P.length_pos) := by
  change (P.dirichletPointProblem.boundary.stateL u,
    ev • P.dirichletPointProblem.boundary.stateL u) ∈
      P.dirichletPointProblem.operator.graph ↔ _
  rw [P.dirichletPointProblem.operator_eigen_iff_physical u ev]
  constructor
  · intro h
    refine ⟨P.operator_admissible u, ?_⟩
    intro v hv
    have he := h v hv.1 ((P.operator_zeroTraces_iff v).mpr hv.2)
    rwa [P.operator_form_empty] at he
  · intro h v hv hvz
    rw [P.operator_form_empty]
    exact h.weak_form v ⟨hv, (P.operator_zeroTraces_iff v).mp hvz⟩

theorem DirichletInterval.operator_eigenbasis_weak (P : DirichletInterval)
    (i : CompactSpectralIndex P.dirichletPointProblem.inverse) :
    DirichletWeakEigenEquation P i.1⁻¹
      ((P.dirichletPointProblem.eigenstate i).val.representative P.length_pos) := by
  apply (P.operator_weak_iff _ _).mp
  change (P.dirichletPointProblem.boundary.stateL (P.dirichletPointProblem.eigenstate i),
    i.1⁻¹ • P.dirichletPointProblem.boundary.stateL (P.dirichletPointProblem.eigenstate i)) ∈ _
  rw [P.dirichletPointProblem.eigenstate_state]
  exact P.dirichletPointProblem.eigenbasis_operator_graph i

theorem DirichletInterval.operator_eigenvalue_rayleigh (P : DirichletInterval)
    (i : CompactSpectralIndex P.dirichletPointProblem.inverse) : i.1⁻¹ ∈ P.rayleighValues := by
  let u := P.dirichletPointProblem.eigenstate i
  have he := P.operator_eigenbasis_weak i
  have hm : 0 < P.squareMass (u.val.representative P.length_pos) := by
    rw [P.operator_squareMass u]
    change 0 < ‖P.dirichletPointProblem.boundary.stateL
      (P.dirichletPointProblem.eigenstate i)‖ ^ 2
    rw [P.dirichletPointProblem.eigenstate_state]
    exact sq_pos_of_pos (norm_pos_iff.mpr
      (P.dirichletPointProblem.eigenbasis.orthonormal.ne_zero i))
  refine ⟨u.val.representative P.length_pos, he.admissible, hm, ?_⟩
  rw [he.self_quadraticForm, mul_div_cancel_right₀ _ hm.ne']

theorem DirichletInterval.principal_le_operator_eigenvalue (P : DirichletInterval)
    (i : CompactSpectralIndex P.dirichletPointProblem.inverse) : P.principalValue ≤ i.1⁻¹ :=
  csInf_le P.rayleighValues_bddBelow (P.operator_eigenvalue_rayleigh i)

end TimeTraps.Spectral
