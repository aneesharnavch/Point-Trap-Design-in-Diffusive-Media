module

public import TimeTraps.Spectral.UnitOperatorGround
public import TimeTraps.Analysis.CompactSpectralEnumerationInterval

@[expose] public section

/-! The first term of the actual sorted operator spectrum is the original
Rayleigh principal value. Natural indexing starts at zero. -/

namespace TimeTraps.Spectral

open TimeTraps.Analysis IntervalSobolevSpace

variable {n : ℕ}

theorem SpectralProblem.unit_first_eigenvalue (P : SpectralProblem n) (hL : P.length = 1) :
    ((P.unitPointProblem hL).spectralEnumeration 0).1⁻¹ = P.principalValue := by
  apply le_antisymm _ (P.principal_le_unit_eigenvalue hL _)
  obtain ⟨i, hi⟩ := P.unit_principal_spectral_index hL
  have hm := (P.unitPointProblem hL).spectralEnumeration_monotone
    (Nat.zero_le ((P.unitPointProblem hL).spectralEnumeration.symm i))
  simpa only [Equiv.apply_symm_apply, hi] using hm

theorem SpectralProblem.unit_first_eigenstate_weak (P : SpectralProblem n)
    (hL : P.length = 1) : WeakEigenEquation P P.principalValue
      (((P.unitPointProblem hL).eigenstate
        ((P.unitPointProblem hL).spectralEnumeration 0)).representative zero_lt_one) := by
  have he := P.unit_eigenbasis_weak hL ((P.unitPointProblem hL).spectralEnumeration 0)
  rwa [P.unit_first_eigenvalue hL] at he

end TimeTraps.Spectral
