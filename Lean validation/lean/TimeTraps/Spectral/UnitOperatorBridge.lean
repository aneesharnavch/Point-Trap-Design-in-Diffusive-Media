module

public import TimeTraps.Analysis.IntervalPointEigenEquivalence
public import TimeTraps.Analysis.CompactInverseEigenvalue
public import TimeTraps.Spectral.GroundStateUniqueness

@[expose] public section

/-! For physical spectral data of length one, identify the independently
defined Rayleigh minimum with the least eigenvalue of the constructed
self-adjoint L2 operator. No optimizer or eigenvalue is redefined. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis IntervalSobolevSpace

variable {n : ℕ}

def SpectralProblem.unitPointProblem (P : SpectralProblem n) (hL : P.length = 1) :
    UnitPointProblem (Fin n) where
  diffusivity := P.diffusivity
  diffusivity_pos := P.diffusivity_pos
  strength := P.strength
  strength_nonneg := fun i => (P.strength_pos i).le
  site := P.site
  site_mem := fun i => by simpa only [hL] using Ioo_subset_Icc_self (P.site_interior i)
  positive_contact := ⟨⟨0, P.count_pos⟩, P.strength_pos _⟩

theorem SpectralProblem.unit_operator_weak_iff (P : SpectralProblem n)
    (hL : P.length = 1) (u : UnitIntervalSobolev) (ev : ℝ) :
    (u.state, ev • u.state) ∈ (P.unitPointProblem hL).operator.graph ↔
      WeakEigenEquation P ev (u.representative zero_lt_one) := by
  rw [(P.unitPointProblem hL).operator_eigen_iff_physical]
  constructor
  · intro h
    refine ⟨by simpa only [hL] using (u.representative_spec zero_lt_one).1, ?_⟩
    intro v hv
    have he := h v (by simpa only [hL] using hv)
    simpa only [unitPointForm, unitPointProblem, hL] using he
  · intro h v hv
    have he := h.weak_form v (by simpa only [hL] using hv)
    simpa only [unitPointForm, unitPointProblem, hL] using he

theorem SpectralProblem.unit_squareMass (P : SpectralProblem n)
    (hL : P.length = 1) (u : UnitIntervalSobolev) :
    P.squareMass (u.representative zero_lt_one) = ‖u.state‖ ^ 2 := by
  rw [SpectralProblem.squareMass, hL, ← real_inner_self_eq_norm_sq,
    state_inner _ _ zero_lt_one]
  simp only [pow_two]

theorem SpectralProblem.unit_eigenbasis_weak (P : SpectralProblem n)
    (hL : P.length = 1) (i : CompactSpectralIndex (P.unitPointProblem hL).inverse) :
    WeakEigenEquation P i.1⁻¹
      (((P.unitPointProblem hL).eigenstate i).representative zero_lt_one) := by
  apply (P.unit_operator_weak_iff hL _ _).mp
  rw [(P.unitPointProblem hL).eigenstate_state]
  exact (P.unitPointProblem hL).eigenbasis_operator_graph i

theorem SpectralProblem.unit_eigenvalue_rayleigh (P : SpectralProblem n)
    (hL : P.length = 1) (i : CompactSpectralIndex (P.unitPointProblem hL).inverse) :
    i.1⁻¹ ∈ P.rayleighValues := by
  let u := (P.unitPointProblem hL).eigenstate i
  have he := P.unit_eigenbasis_weak hL i
  have hm : 0 < P.squareMass (u.representative zero_lt_one) := by
    rw [P.unit_squareMass hL, (P.unitPointProblem hL).eigenstate_state]
    exact sq_pos_of_pos (norm_pos_iff.mpr ((P.unitPointProblem hL).eigenbasis.orthonormal.ne_zero i))
  refine ⟨u.representative zero_lt_one, he.energy, hm, ?_⟩
  rw [he.self_quadraticForm, mul_div_cancel_right₀ _ hm.ne']

theorem SpectralProblem.principal_le_unit_eigenvalue (P : SpectralProblem n)
    (hL : P.length = 1) (i : CompactSpectralIndex (P.unitPointProblem hL).inverse) :
    P.principalValue ≤ i.1⁻¹ :=
  P.rayleigh_minimum.2 (P.unit_eigenvalue_rayleigh hL i)

end TimeTraps.Spectral
