module

public import TimeTraps.Spectral.ArrayOperatorBridge
public import TimeTraps.Analysis.IntervalPeriodicEnumeration

@[expose] public section

/-! The physical circle-array Rayleigh minimum is attained by a positive
actual operator eigenstate and equals the first sorted operator eigenvalue. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis IntervalSobolevSpace

variable {n : ℕ}

theorem PeriodicArray.principal_operator_exists (P : PeriodicArray n) :
    ∃ u : IntervalPeriodicSpace P.operatorBoundary, P.operatorBoundary.stateL u ≠ 0 ∧
      (P.operatorBoundary.stateL u, P.principalValue • P.operatorBoundary.stateL u) ∈
        P.periodicPointProblem.operator.graph ∧
      ∀ x ∈ Icc 0 P.length, 0 < u.val.representative P.length_pos x := by
  obtain ⟨U, hU, hpos, hmass, _⟩ := P.positive_ground_state
  let u := P.operatorOfEnergy hU.energy
  have hp := P.operatorOfEnergy_representative hU.energy
  have hm : 0 < P.squareMass (u.val.representative P.length_pos) := by
    have he : P.squareMass (u.val.representative P.length_pos) = P.squareMass U := by
      unfold squareMass
      apply intervalIntegral.integral_congr_Ioo_of_le P.length_pos.le
      intro x hx
      change u.val.representative P.length_pos x ^ 2 = U x ^ 2
      rw [hp (Ioo_subset_Icc_self hx)]
    rwa [he]
  refine ⟨u, ?_, ?_, ?_⟩
  · intro hz
    rw [P.operator_squareMass u, hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hm
    exact (lt_irrefl 0) hm
  · exact (P.operator_weak_iff u P.principalValue).mpr (hU.congr hp.symm)
  · intro x hx
    rw [hp hx]
    exact hpos x hx

theorem PeriodicArray.principal_operator_spectral_index (P : PeriodicArray n) :
    ∃ i : CompactSpectralIndex P.periodicPointProblem.inverse, i.1⁻¹ = P.principalValue := by
  obtain ⟨u, hu, he, _⟩ := P.principal_operator_exists
  exact P.periodicPointProblem.compactPositiveInverse.inverse_eigenvalue_index hu he

theorem PeriodicArray.principal_operator_least_spectral (P : PeriodicArray n) :
    IsLeast (Set.range (fun i : CompactSpectralIndex P.periodicPointProblem.inverse => i.1⁻¹))
      P.principalValue := by
  refine ⟨P.principal_operator_spectral_index, ?_⟩
  rintro ev ⟨i, rfl⟩
  exact P.principal_le_operator_eigenvalue i

theorem PeriodicArray.operator_first_eigenvalue (P : PeriodicArray n) :
    (P.periodicPointProblem.spectralEnumeration 0).1⁻¹ = P.principalValue := by
  apply le_antisymm _ (P.principal_le_operator_eigenvalue _)
  obtain ⟨i, hi⟩ := P.principal_operator_spectral_index
  have hm := P.periodicPointProblem.spectralEnumeration_monotone
    (Nat.zero_le (P.periodicPointProblem.spectralEnumeration.symm i))
  simpa only [Equiv.apply_symm_apply, hi] using hm

theorem PeriodicArray.operator_first_eigenstate_weak (P : PeriodicArray n) :
    ArrayWeakEigenEquation P P.principalValue
      ((P.periodicPointProblem.eigenstate
        (P.periodicPointProblem.spectralEnumeration 0)).val.representative P.length_pos) := by
  have he := P.operator_eigenbasis_weak (P.periodicPointProblem.spectralEnumeration 0)
  rwa [P.operator_first_eigenvalue] at he

end TimeTraps.Spectral
