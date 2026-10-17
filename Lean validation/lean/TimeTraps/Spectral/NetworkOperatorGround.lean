module

public import TimeTraps.Spectral.NetworkOperatorSpectrumPhysical
public import TimeTraps.Spectral.NetworkOperatorSpectrumEnumeration
public import TimeTraps.Spectral.NetworkOperatorSpectrumExpansion
public import TimeTraps.Analysis.CompactInverseEigenvalue

@[expose] public section

/-! The first eigenvalue of the actual network operator equals the old
independent full-GraphEnergy Rayleigh minimum. The old positive physical
ground state supplies an operator eigenvector; the original Rayleigh
lower bound orders every member of the new complete spectrum. -/

namespace TimeTraps.Spectral

open Set TimeTraps.Analysis

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem SpectralNetwork.operator_eigenvalue_rayleigh (P : SpectralNetwork V E)
    (i : CompactSpectralIndex P.operatorInverse) : i.1⁻¹ ∈ P.rayleighValues := by
  have he := P.eigenstate_physical_weak i
  have hm : 0 < P.squareMass (P.operatorRep (P.eigenstate i)) := by
    rw [P.operator_squareMass, P.eigenstate_state]
    exact sq_pos_of_pos (norm_pos_iff.mpr (P.eigenbasis.orthonormal.ne_zero i))
  refine ⟨P.operatorNodes (P.eigenstate i), P.operatorRep (P.eigenstate i),
    he.energy, hm, ?_⟩
  rw [he.self_quadraticForm, mul_div_cancel_right₀ _ hm.ne']

theorem SpectralNetwork.principal_le_operator_eigenvalue (P : SpectralNetwork V E)
    (i : CompactSpectralIndex P.operatorInverse) : P.principalValue ≤ i.1⁻¹ := by
  let : Nonempty V := ⟨P.tail (Classical.choice inferInstance)⟩
  exact P.rayleigh_minimum.2 (P.operator_eigenvalue_rayleigh i)

theorem SpectralNetwork.principal_operator_exists (P : SpectralNetwork V E) :
    ∃ u : GraphSobolevSpace P.geometry,
      graphSobolevSpaceStateL P.geometry u ≠ 0 ∧
      (graphSobolevSpaceStateL P.geometry u,
        P.principalValue • graphSobolevSpaceStateL P.geometry u) ∈ P.operator.graph ∧
      ∀ e x, x ∈ Icc 0 (P.length e) → 0 < P.operatorRep u e x := by
  let : Nonempty V := ⟨P.tail (Classical.choice inferInstance)⟩
  obtain ⟨F⟩ := P.principal_eigenstate_exists
  refine ⟨graphSobolevSpaceOfEnergy P.geometry F.energy, ?_, ?_, ?_⟩
  · intro hz
    have hm := F.squareMass_pos
    rw [← P.operatorState_norm_ofEnergy F.energy, hz, norm_zero,
      zero_pow (by norm_num : 2 ≠ 0)] at hm
    exact (lt_irrefl 0) hm
  · exact (P.operator_eigen_iff_physical F.energy P.principalValue).mpr F.to_weak
  · intro e x hx
    rw [P.operatorRep_ofEnergy F.energy e hx]
    exact F.positive e x hx

theorem SpectralNetwork.principal_operator_spectral_index (P : SpectralNetwork V E) :
    ∃ i : CompactSpectralIndex P.operatorInverse, i.1⁻¹ = P.principalValue := by
  obtain ⟨u, hu, he, _⟩ := P.principal_operator_exists
  exact P.operatorCompactPositiveInverse.inverse_eigenvalue_index hu he

theorem SpectralNetwork.principal_least_operator_spectral (P : SpectralNetwork V E) :
    IsLeast (Set.range (fun i : CompactSpectralIndex P.operatorInverse => i.1⁻¹))
      P.principalValue := by
  refine ⟨P.principal_operator_spectral_index, ?_⟩
  rintro ev ⟨i, rfl⟩
  exact P.principal_le_operator_eigenvalue i

theorem SpectralNetwork.first_operator_eigenvalue (P : SpectralNetwork V E) :
    (P.spectralEnumeration 0).1⁻¹ = P.principalValue := by
  apply le_antisymm _ (P.principal_le_operator_eigenvalue _)
  obtain ⟨i, hi⟩ := P.principal_operator_spectral_index
  have hm := P.spectralEnumeration_monotone (Nat.zero_le (P.spectralEnumeration.symm i))
  simpa only [Equiv.apply_symm_apply, hi] using hm

theorem SpectralNetwork.first_operator_eigenstate_weak (P : SpectralNetwork V E) :
    NetworkWeakEigenEquation P P.principalValue
      (P.operatorNodes (P.eigenstate (P.spectralEnumeration 0)))
      (P.operatorRep (P.eigenstate (P.spectralEnumeration 0))) := by
  have he := P.eigenstate_physical_weak (P.spectralEnumeration 0)
  rwa [P.first_operator_eigenvalue] at he

end TimeTraps.Spectral
