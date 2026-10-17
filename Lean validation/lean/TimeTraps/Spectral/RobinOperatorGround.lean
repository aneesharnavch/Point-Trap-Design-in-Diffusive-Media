module

public import TimeTraps.Spectral.RobinOperatorBridge
public import TimeTraps.Analysis.GeneralIntervalPointEnumeration

@[expose] public section

/-! The independent full-H1 Robin Rayleigh minimum is the first eigenvalue
of the actual interval operator, with both finite nonnegative endpoint
coefficients retained. Its positive physical ground state gives attainment. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis IntervalSobolevSpace

variable {n : ℕ}

theorem RobinProblem.interval_principal_operator_exists (P : RobinProblem n) :
    ∃ u : IntervalSobolevSpace 0 P.length, u.state ≠ 0 ∧
      (u.state, P.principalValue • u.state) ∈ P.intervalPointProblem.operator.graph ∧
      ∀ x ∈ Icc (0 : ℝ) P.length, 0 < u.representative P.length_pos x := by
  obtain ⟨E, _⟩ := P.principal_eigenstate_exists
  let u := ofEnergy E.energy P.length_pos
  have hp : EqOn (u.representative P.length_pos) E.state (Icc (0 : ℝ) P.length) :=
    representative_ofEnergy E.energy P.length_pos
  have hm : 0 < P.squareMass (u.representative P.length_pos) := by
    have he := E.squareMass_of_eq_scalar (c := 1) (by simpa only [one_mul] using hp)
    rw [he, one_pow, one_mul]
    exact E.squareMass_pos
  refine ⟨u, ?_, (P.interval_operator_ofEnergy_iff E.energy _).mpr E.to_weak, ?_⟩
  · intro hz
    rw [P.interval_squareMass, hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hm
    exact (lt_irrefl 0) hm
  · intro x hx
    rw [hp hx]
    exact E.positive x hx

theorem RobinProblem.interval_principal_spectral_index (P : RobinProblem n) :
    ∃ i : CompactSpectralIndex P.intervalPointProblem.inverse, i.1⁻¹ = P.principalValue := by
  obtain ⟨u, hu, he, _⟩ := P.interval_principal_operator_exists
  exact P.intervalPointProblem.compactPositiveInverse.inverse_eigenvalue_index hu he

theorem RobinProblem.interval_principal_least_spectral (P : RobinProblem n) :
    IsLeast (Set.range (fun i : CompactSpectralIndex P.intervalPointProblem.inverse => i.1⁻¹))
      P.principalValue := by
  refine ⟨P.interval_principal_spectral_index, ?_⟩
  rintro ev ⟨i, rfl⟩
  exact P.principal_le_interval_eigenvalue i

theorem RobinProblem.interval_first_eigenvalue (P : RobinProblem n) :
    (P.intervalPointProblem.spectralEnumeration 0).1⁻¹ = P.principalValue := by
  apply le_antisymm _ (P.principal_le_interval_eigenvalue _)
  obtain ⟨i, hi⟩ := P.interval_principal_spectral_index
  have hm := P.intervalPointProblem.spectralEnumeration_monotone
    (Nat.zero_le (P.intervalPointProblem.spectralEnumeration.symm i))
  simpa only [Equiv.apply_symm_apply, hi] using hm

theorem RobinProblem.interval_first_eigenstate_weak (P : RobinProblem n) :
    RobinWeakEigenEquation P P.principalValue
      ((P.intervalPointProblem.eigenstate (P.intervalPointProblem.spectralEnumeration 0)).representative
        P.length_pos) := by
  have he := P.interval_eigenbasis_weak (P.intervalPointProblem.spectralEnumeration 0)
  rwa [P.interval_first_eigenvalue] at he

end TimeTraps.Spectral
