module

public import TimeTraps.Analysis.GeneralIntervalPointEigenEquivalence
public import TimeTraps.Analysis.CompactInverseEigenvalue
public import TimeTraps.Spectral.GroundStateUniqueness

@[expose] public section

/-! The original physical spectral problem, at its arbitrary positive
length, as the constructed self-adjoint L2 operator. All H1 competitors and
the independent Rayleigh objective are retained without rescaling. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis IntervalSobolevSpace

variable {n : ℕ}

def SpectralProblem.intervalPointProblem (P : SpectralProblem n) :
    IntervalPointProblem (Fin n) 0 P.length where
  interval_pos := P.length_pos
  diffusivity := P.diffusivity
  diffusivity_pos := P.diffusivity_pos
  strength := P.strength
  strength_nonneg := fun i => (P.strength_pos i).le
  site := P.site
  site_mem := fun i => Ioo_subset_Icc_self (P.site_interior i)
  positive_contact := ⟨⟨0, P.count_pos⟩, P.strength_pos _⟩

theorem SpectralProblem.interval_operator_weak_iff (P : SpectralProblem n)
    (u : IntervalSobolevSpace 0 P.length) (ev : ℝ) :
    (u.state, ev • u.state) ∈ P.intervalPointProblem.operator.graph ↔
      WeakEigenEquation P ev (u.representative P.length_pos) := by
  rw [P.intervalPointProblem.operator_eigen_iff_physical]
  constructor
  · intro h
    refine ⟨(u.representative_spec P.length_pos).1, ?_⟩
    intro v hv
    exact h v hv
  · intro h v hv
    exact h.weak_form v hv

theorem SpectralProblem.interval_squareMass (P : SpectralProblem n)
    (u : IntervalSobolevSpace 0 P.length) :
    P.squareMass (u.representative P.length_pos) = ‖u.state‖ ^ 2 := by
  rw [SpectralProblem.squareMass, ← real_inner_self_eq_norm_sq, state_inner _ _ P.length_pos]
  simp only [pow_two]

theorem SpectralProblem.interval_eigenbasis_weak (P : SpectralProblem n)
    (i : CompactSpectralIndex P.intervalPointProblem.inverse) :
    WeakEigenEquation P i.1⁻¹
      ((P.intervalPointProblem.eigenstate i).representative P.length_pos) := by
  apply (P.interval_operator_weak_iff _ _).mp
  rw [P.intervalPointProblem.eigenstate_state]
  exact P.intervalPointProblem.eigenbasis_operator_graph i

theorem SpectralProblem.interval_eigenvalue_rayleigh (P : SpectralProblem n)
    (i : CompactSpectralIndex P.intervalPointProblem.inverse) : i.1⁻¹ ∈ P.rayleighValues := by
  let u := P.intervalPointProblem.eigenstate i
  have he := P.interval_eigenbasis_weak i
  have hm : 0 < P.squareMass (u.representative P.length_pos) := by
    rw [P.interval_squareMass, P.intervalPointProblem.eigenstate_state]
    exact sq_pos_of_pos (norm_pos_iff.mpr (P.intervalPointProblem.eigenbasis.orthonormal.ne_zero i))
  refine ⟨u.representative P.length_pos, he.energy, hm, ?_⟩
  rw [he.self_quadraticForm, mul_div_cancel_right₀ _ hm.ne']

theorem SpectralProblem.principal_le_interval_eigenvalue (P : SpectralProblem n)
    (i : CompactSpectralIndex P.intervalPointProblem.inverse) : P.principalValue ≤ i.1⁻¹ :=
  P.rayleigh_minimum.2 (P.interval_eigenvalue_rayleigh i)

end TimeTraps.Spectral
