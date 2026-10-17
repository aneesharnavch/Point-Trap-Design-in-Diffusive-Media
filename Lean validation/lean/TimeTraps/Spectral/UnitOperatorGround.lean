module

public import TimeTraps.Spectral.UnitOperatorBridge

@[expose] public section

/-! The independently attained positive Rayleigh ground state gives an
actual eigenvector of the L2 operator. Completeness places its eigenvalue
in the constructed spectral index, and the Rayleigh bound makes it least. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis IntervalSobolevSpace

variable {n : ℕ}

theorem SpectralProblem.unit_principal_operator_exists (P : SpectralProblem n)
    (hL : P.length = 1) : ∃ u : UnitIntervalSobolev, u.state ≠ 0 ∧
      (u.state, P.principalValue • u.state) ∈ (P.unitPointProblem hL).operator.graph ∧
      ∀ x ∈ Icc (0 : ℝ) 1, 0 < u.representative zero_lt_one x := by
  obtain ⟨E, _⟩ := P.principal_eigenstate_exists
  have hu : IntervalEnergy E.state 0 1 := by simpa only [hL] using E.energy
  let u := ofEnergy hu zero_lt_one
  have hp : EqOn (u.representative zero_lt_one) E.state (Icc (0 : ℝ) P.length) := by
    simpa only [hL] using representative_ofEnergy hu zero_lt_one
  have hm : 0 < P.squareMass (u.representative zero_lt_one) := by
    have he := E.squareMass_of_eq_scalar (c := 1) (by simpa only [one_mul] using hp)
    rw [he, one_pow, one_mul]
    exact E.squareMass_pos
  refine ⟨u, ?_, ?_, ?_⟩
  · intro hz
    rw [P.unit_squareMass hL, hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hm
    exact (lt_irrefl 0) hm
  · apply ((P.unitPointProblem hL).operator_eigen_iff_hilbert u P.principalValue).mpr
    intro v
    rw [UnitPointProblem.form, unitSobolevForm_apply, state_inner _ _ zero_lt_one]
    change unitPointForm P.diffusivity P.strength P.site
      (u.representative zero_lt_one) (v.representative zero_lt_one) = _
    have hp1 : EqOn (u.representative zero_lt_one) E.state (Icc (0 : ℝ) 1) := by
      simpa only [hL] using hp
    have hz : ∀ i, P.site i ∈ Icc (0 : ℝ) 1 := by
      intro i
      simpa only [hL] using Ioo_subset_Icc_self (P.site_interior i)
    rw [unitPointForm_congr P.diffusivity P.strength P.site hz
      hp1 (fun _ _ => rfl)]
    have he := E.to_weak.weak_form (v.representative zero_lt_one)
      (by simpa only [hL] using (v.representative_spec zero_lt_one).1)
    change unitPointForm P.diffusivity P.strength P.site E.state
      (v.representative zero_lt_one) = _
    calc
      _ = P.principalValue * ∫ x in (0 : ℝ)..1,
          E.state x * v.representative zero_lt_one x := by
        simpa only [hL, unitPointForm] using he
      _ = _ := by
        congr 1
        apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
        intro x hx
        change E.state x * v.representative zero_lt_one x =
          u.representative zero_lt_one x * v.representative zero_lt_one x
        rw [hp1 (Ioo_subset_Icc_self hx)]
  · intro x hx
    have hx' : x ∈ Icc (0 : ℝ) P.length := by simpa only [hL] using hx
    rw [hp hx']
    exact E.positive x hx'

theorem SpectralProblem.unit_principal_spectral_index (P : SpectralProblem n)
    (hL : P.length = 1) :
    ∃ i : CompactSpectralIndex (P.unitPointProblem hL).inverse, i.1⁻¹ = P.principalValue := by
  obtain ⟨u, hu, he, _⟩ := P.unit_principal_operator_exists hL
  exact (P.unitPointProblem hL).compactPositiveInverse.inverse_eigenvalue_index hu he

theorem SpectralProblem.unit_principal_least_spectral (P : SpectralProblem n)
    (hL : P.length = 1) :
    IsLeast (Set.range (fun i : CompactSpectralIndex (P.unitPointProblem hL).inverse => i.1⁻¹))
      P.principalValue := by
  refine ⟨P.unit_principal_spectral_index hL, ?_⟩
  rintro ev ⟨i, rfl⟩
  exact P.principal_le_unit_eigenvalue hL i

end TimeTraps.Spectral
