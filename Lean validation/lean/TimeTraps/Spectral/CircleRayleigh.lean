module

public import TimeTraps.Spectral.CircleAssembly
public import TimeTraps.Spectral.NetworkRayleigh

@[expose] public section

/-! Equality of the independently defined physical periodic and matching-arc
Rayleigh classes, with no restriction to smooth tests or eigenfunctions. -/

namespace TimeTraps.Spectral

open Set TimeTraps.Analysis TimeTraps.Graph

variable {n : ℕ}

theorem CircleProblem.periodicRayleighValues_eq (C : CircleProblem n) :
    C.periodicRayleighValues = C.network.rayleighValues := by
  ext r
  constructor
  · rintro ⟨w, hw, hm, hr⟩
    refine ⟨(fun i => w (C.site i)), C.restriction w, C.restrict_periodic_energy hw, ?_, ?_⟩
    · rw [C.restrict_mass hw.1]
      exact hm
    · rw [C.restrict_quadraticForm hw.1, C.restrict_mass hw.1]
      exact hr
  · rintro ⟨U, u, hu, hm, hr⟩
    obtain ⟨w, hw, _, _, hmass, hform⟩ := C.periodic_representative hu
    refine ⟨w, hw, ?_, ?_⟩
    · rwa [hmass]
    · rwa [hform, hmass]

theorem CircleProblem.periodicPrincipalValue_eq (C : CircleProblem n) :
    C.periodicPrincipalValue = C.network.principalValue := by
  unfold periodicPrincipalValue SpectralNetwork.principalValue
  rw [C.periodicRayleighValues_eq]

theorem CircleProblem.periodicPrincipalValue_pos (C : CircleProblem n) :
    0 < C.periodicPrincipalValue := by
  rw [C.periodicPrincipalValue_eq]
  exact C.principal_ground_state.1

theorem CircleProblem.periodic_rayleigh_minimum (C : CircleProblem n) :
    IsLeast C.periodicRayleighValues C.periodicPrincipalValue := by
  rw [C.periodicPrincipalValue_eq, C.periodicRayleighValues_eq]
  exact C.principal_ground_state.2.1

theorem CircleProblem.periodic_rayleigh_attained (C : CircleProblem n) :
    ∃ w : ℝ → ℝ, C.PeriodicEnergy w ∧ 0 < C.periodicMass w ∧
      C.periodicQuadraticForm w / C.periodicMass w = C.periodicPrincipalValue := by
  obtain ⟨w, hw, hm, he⟩ := C.periodic_rayleigh_minimum.1
  exact ⟨w, hw, hm, he.symm⟩

theorem CircleProblem.periodic_rayleigh_lower (C : CircleProblem n) {w : ℝ → ℝ}
    (hw : C.PeriodicEnergy w) (hm : 0 < C.periodicMass w) :
    C.periodicPrincipalValue ≤ C.periodicQuadraticForm w / C.periodicMass w :=
  C.periodic_rayleigh_minimum.2 ⟨w, hw, hm, rfl⟩

end TimeTraps.Spectral
