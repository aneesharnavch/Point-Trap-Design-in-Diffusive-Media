module

public import TimeTraps.Spectral.PeriodicArray
public import TimeTraps.Analysis.PeriodicShiftIntegral

@[expose] public section

/-! Moving the cut to the first trap preserves the entire independently
specified periodic Rayleigh class of an arbitrary physical array. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {n : ℕ}

noncomputable def PeriodicArray.normalizeFunction (P : PeriodicArray n) (u : ℝ → ℝ) : ℝ → ℝ :=
  periodicShift P.length P.offset u

noncomputable def PeriodicArray.restoreFunction (P : PeriodicArray n) (u : ℝ → ℝ) : ℝ → ℝ :=
  periodicShift P.length (P.length - P.offset) u

theorem PeriodicArray.normalize_energy (P : PeriodicArray n) {u : ℝ → ℝ} (hu : P.Energy u) :
    P.normalized.PeriodicEnergy (P.normalizeFunction u) :=
  ⟨periodicShift_energy hu.1 hu.2 ⟨P.offset_mem.1, P.offset_mem.2.le⟩,
    periodicShift_trace hu.2 ⟨P.offset_mem.1, P.offset_mem.2.le⟩⟩

theorem PeriodicArray.restore_energy (P : PeriodicArray n) {u : ℝ → ℝ}
    (hu : P.normalized.PeriodicEnergy u) : P.Energy (P.restoreFunction u) :=
  ⟨periodicShift_energy hu.1 hu.2 ⟨sub_nonneg.mpr P.offset_mem.2.le, sub_le_self _ P.offset_mem.1⟩,
    periodicShift_trace hu.2 ⟨sub_nonneg.mpr P.offset_mem.2.le, sub_le_self _ P.offset_mem.1⟩⟩

theorem PeriodicArray.normalize_site_value (P : PeriodicArray n) (u : ℝ → ℝ) (i : Fin n) :
    P.normalizeFunction u (P.normalized.site i) = u (P.site i) := by
  rw [normalizeFunction, periodicShift_left P.length P.offset u (P.normalized_site_mem i).2.le,
    P.normalized_site, add_sub_cancel]

theorem PeriodicArray.restore_site_value (P : PeriodicArray n) {u : ℝ → ℝ}
    (hu : u 0 = u P.length) (i : Fin n) :
    P.restoreFunction u (P.site i) = u (P.normalized.site i) := by
  rw [restoreFunction, periodicShift_right hu (show P.length - (P.length - P.offset) ≤ P.site i by
    linarith [P.offset_le_site i]), P.normalized_site]
  congr 1
  ring

theorem PeriodicArray.normalize_mass (P : PeriodicArray n) {u : ℝ → ℝ} (hu : P.Energy u) :
    P.normalized.periodicMass (P.normalizeFunction u) = P.squareMass u :=
  periodicShift_square_integral hu.1 hu.2 ⟨P.offset_mem.1, P.offset_mem.2.le⟩

theorem PeriodicArray.restore_mass (P : PeriodicArray n) {u : ℝ → ℝ}
    (hu : P.normalized.PeriodicEnergy u) : P.squareMass (P.restoreFunction u) = P.normalized.periodicMass u :=
  periodicShift_square_integral hu.1 hu.2
    ⟨sub_nonneg.mpr P.offset_mem.2.le, sub_le_self _ P.offset_mem.1⟩

theorem PeriodicArray.normalize_quadraticForm (P : PeriodicArray n) {u : ℝ → ℝ} (hu : P.Energy u) :
    P.normalized.periodicQuadraticForm (P.normalizeFunction u) = P.quadraticForm u := by
  unfold CircleProblem.periodicQuadraticForm
  simp_rw [P.normalize_site_value]
  have h := periodicShift_derivative_integral hu.1 hu.2 ⟨P.offset_mem.1, P.offset_mem.2.le⟩
  change (∫ x in (0 : ℝ)..P.length, deriv (P.normalizeFunction u) x ^ 2) = _ at h
  change P.diffusivity * (∫ x in (0 : ℝ)..P.length, deriv (P.normalizeFunction u) x ^ 2) +
    (∑ i, P.strength i * u (P.site i) ^ 2) = _
  rw [h]
  rfl

theorem PeriodicArray.restore_quadraticForm (P : PeriodicArray n) {u : ℝ → ℝ}
    (hu : P.normalized.PeriodicEnergy u) : P.quadraticForm (P.restoreFunction u) = P.normalized.periodicQuadraticForm u := by
  unfold quadraticForm
  simp_rw [P.restore_site_value hu.2]
  have h := periodicShift_derivative_integral hu.1 hu.2
    ⟨sub_nonneg.mpr P.offset_mem.2.le, sub_le_self _ P.offset_mem.1⟩
  change (∫ x in (0 : ℝ)..P.length, deriv (P.restoreFunction u) x ^ 2) = _ at h
  rw [h]
  rfl

theorem PeriodicArray.rayleighValues_eq_normalized (P : PeriodicArray n) :
    P.rayleighValues = P.normalized.periodicRayleighValues := by
  ext r
  constructor
  · rintro ⟨u, hu, hm, hr⟩
    refine ⟨P.normalizeFunction u, P.normalize_energy hu, ?_, ?_⟩
    · rwa [P.normalize_mass hu]
    · rwa [P.normalize_quadraticForm hu, P.normalize_mass hu]
  · rintro ⟨u, hu, hm, hr⟩
    refine ⟨P.restoreFunction u, P.restore_energy hu, ?_, ?_⟩
    · rwa [P.restore_mass hu]
    · rwa [P.restore_quadraticForm hu, P.restore_mass hu]

theorem PeriodicArray.principalValue_eq_normalized (P : PeriodicArray n) :
    P.principalValue = P.normalized.periodicPrincipalValue := by
  unfold principalValue CircleProblem.periodicPrincipalValue
  rw [P.rayleighValues_eq_normalized]

theorem PeriodicArray.principalValue_pos (P : PeriodicArray n) : 0 < P.principalValue := by
  rw [P.principalValue_eq_normalized]
  exact P.normalized.periodicPrincipalValue_pos

theorem PeriodicArray.rayleigh_minimum (P : PeriodicArray n) : IsLeast P.rayleighValues P.principalValue := by
  rw [P.principalValue_eq_normalized, P.rayleighValues_eq_normalized]
  exact P.normalized.periodic_rayleigh_minimum

end TimeTraps.Spectral
