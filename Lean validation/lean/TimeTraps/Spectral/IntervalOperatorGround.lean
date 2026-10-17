module

public import TimeTraps.Spectral.IntervalOperatorBridge
public import TimeTraps.Analysis.GeneralIntervalPointEnumeration

@[expose] public section

/-! The independent principal Rayleigh value is the first eigenvalue of the
actual L2 operator at the original arbitrary length. The positive physical
ground state supplies attainment and the full spectrum supplies ordering. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis IntervalSobolevSpace

variable {n : ℕ}

theorem SpectralProblem.interval_principal_operator_exists (P : SpectralProblem n) :
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
  refine ⟨u, ?_, ?_, ?_⟩
  · intro hz
    rw [P.interval_squareMass, hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hm
    exact (lt_irrefl 0) hm
  · apply (P.intervalPointProblem.operator_eigen_iff_hilbert u P.principalValue).mpr
    intro v
    rw [IntervalPointProblem.form, intervalSobolevPointForm_apply, state_inner _ _ P.length_pos]
    change intervalPointForm P.diffusivity P.strength P.site 0 P.length
      (u.representative P.length_pos) (v.representative P.length_pos) = _
    have hz : ∀ i, P.site i ∈ Icc (0 : ℝ) P.length :=
      fun i => Ioo_subset_Icc_self (P.site_interior i)
    rw [intervalPointForm_congr P.diffusivity P.strength P.site P.length_pos.le hz
      hp (fun _ _ => rfl)]
    have he := E.to_weak.weak_form (v.representative P.length_pos)
      (v.representative_spec P.length_pos).1
    calc
      _ = P.principalValue * ∫ x in (0 : ℝ)..P.length,
          E.state x * v.representative P.length_pos x := he
      _ = _ := by
        congr 1
        apply intervalIntegral.integral_congr_Ioo_of_le P.length_pos.le
        intro x hx
        change E.state x * v.representative P.length_pos x =
          u.representative P.length_pos x * v.representative P.length_pos x
        rw [hp (Ioo_subset_Icc_self hx)]
  · intro x hx
    rw [hp hx]
    exact E.positive x hx

theorem SpectralProblem.interval_principal_spectral_index (P : SpectralProblem n) :
    ∃ i : CompactSpectralIndex P.intervalPointProblem.inverse, i.1⁻¹ = P.principalValue := by
  obtain ⟨u, hu, he, _⟩ := P.interval_principal_operator_exists
  exact P.intervalPointProblem.compactPositiveInverse.inverse_eigenvalue_index hu he

theorem SpectralProblem.interval_principal_least_spectral (P : SpectralProblem n) :
    IsLeast (Set.range (fun i : CompactSpectralIndex P.intervalPointProblem.inverse => i.1⁻¹))
      P.principalValue := by
  refine ⟨P.interval_principal_spectral_index, ?_⟩
  rintro ev ⟨i, rfl⟩
  exact P.principal_le_interval_eigenvalue i

theorem SpectralProblem.interval_first_eigenvalue (P : SpectralProblem n) :
    (P.intervalPointProblem.spectralEnumeration 0).1⁻¹ = P.principalValue := by
  apply le_antisymm _ (P.principal_le_interval_eigenvalue _)
  obtain ⟨i, hi⟩ := P.interval_principal_spectral_index
  have hm := P.intervalPointProblem.spectralEnumeration_monotone
    (Nat.zero_le (P.intervalPointProblem.spectralEnumeration.symm i))
  simpa only [Equiv.apply_symm_apply, hi] using hm

theorem SpectralProblem.interval_first_eigenstate_weak (P : SpectralProblem n) :
    WeakEigenEquation P P.principalValue
      ((P.intervalPointProblem.eigenstate (P.intervalPointProblem.spectralEnumeration 0)).representative
        P.length_pos) := by
  have he := P.interval_eigenbasis_weak (P.intervalPointProblem.spectralEnumeration 0)
  rwa [P.interval_first_eigenvalue] at he

end TimeTraps.Spectral
