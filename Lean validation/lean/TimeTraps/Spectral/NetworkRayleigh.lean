module

public import TimeTraps.Spectral.NetworkGroundState

@[expose] public section

/-! Positive physical network eigenstates attain the independently defined
Rayleigh minimum. Existence is supplied by the checked compact nodal construction. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] {P : SpectralNetwork V E} {ev : ℝ}

omit [Fintype V] in
theorem PositiveNetworkEigenstate.squareMass_pos [Nonempty E]
    (F : PositiveNetworkEigenstate P ev) : 0 < P.squareMass F.state := by
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro e _
  apply intervalIntegral.integral_pos (P.length_pos e) ((F.edge_continuous e).pow 2)
  · intro x _
    exact sq_nonneg _
  · exact ⟨0, ⟨le_rfl, (P.length_pos e).le⟩,
      sq_pos_of_pos (F.positive e 0 ⟨le_rfl, (P.length_pos e).le⟩)⟩

theorem PositiveNetworkEigenstate.rayleigh_member [Nonempty E]
    (F : PositiveNetworkEigenstate P ev) : ev ∈ P.rayleighValues := by
  refine ⟨F.nodal, F.state, F.energy, F.squareMass_pos, ?_⟩
  rw [F.to_weak.self_quadraticForm, mul_div_cancel_right₀ _ (ne_of_gt F.squareMass_pos)]

theorem PositiveNetworkEigenstate.rayleigh_lower (F : PositiveNetworkEigenstate P ev)
    {r : ℝ} (hr : r ∈ P.rayleighValues) : ev ≤ r := by
  obtain ⟨W, w, hw, hm, rfl⟩ := hr
  exact (le_div_iff₀ hm).mpr (F.quadraticForm_lower hw)

theorem PositiveNetworkEigenstate.principalValue_eq [Nonempty E]
    (F : PositiveNetworkEigenstate P ev) : P.principalValue = ev :=
  le_antisymm (csInf_le P.rayleighValues_bddBelow F.rayleigh_member)
    (le_csInf P.rayleighValues_nonempty fun _ hr => F.rayleigh_lower hr)

theorem PositiveNetworkEigenstate.eigenvalue_unique [Nonempty E]
    (F : PositiveNetworkEigenstate P ev) {r : ℝ} (H : PositiveNetworkEigenstate P r) : ev = r :=
  F.principalValue_eq.symm.trans H.principalValue_eq

theorem SpectralNetwork.principalValue_pos [Nonempty V] [Nonempty E]
    (P : SpectralNetwork V E) : 0 < P.principalValue := by
  obtain ⟨ev, hev, ⟨F⟩⟩ := P.positive_eigenstate_exists
  rw [F.principalValue_eq]
  exact hev

theorem SpectralNetwork.principal_eigenstate_exists [Nonempty V] [Nonempty E]
    (P : SpectralNetwork V E) : Nonempty (PositiveNetworkEigenstate P P.principalValue) := by
  obtain ⟨ev, _, ⟨F⟩⟩ := P.positive_eigenstate_exists
  rw [F.principalValue_eq]
  exact ⟨F⟩

theorem SpectralNetwork.rayleigh_minimum [Nonempty V] [Nonempty E]
    (P : SpectralNetwork V E) : IsLeast P.rayleighValues P.principalValue := by
  obtain ⟨F⟩ := P.principal_eigenstate_exists
  exact ⟨F.rayleigh_member, fun _ hr => F.rayleigh_lower hr⟩

omit [Fintype V] [Fintype E] in
theorem CircleProblem.principal_ground_state {n : ℕ} (C : CircleProblem n) :
    0 < C.network.principalValue ∧ IsLeast C.network.rayleighValues C.network.principalValue ∧
      ∃ F : PositiveNetworkEigenstate C.network C.network.principalValue,
        NetworkWeakEigenEquation C.network C.network.principalValue F.nodal F.state := by
  let : Nonempty (Fin n) := ⟨⟨0, C.count_pos⟩⟩
  obtain ⟨F⟩ := C.network.principal_eigenstate_exists
  exact ⟨C.network.principalValue_pos, C.network.rayleigh_minimum, F, F.to_weak⟩

end TimeTraps.Spectral
