module

public import TimeTraps.Spectral.ArrayNormalization
public import TimeTraps.Analysis.PeriodicShiftPairing

@[expose] public section

/-! Rotation transport for both arguments of the physical weak equation,
with exact reconstruction and preservation of positivity. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {n : ℕ}

theorem PeriodicArray.restore_normalize (P : PeriodicArray n) {u : ℝ → ℝ}
    (hu : u 0 = u P.length) :
    EqOn (P.restoreFunction (P.normalizeFunction u)) u (Icc 0 P.length) := by
  intro x hx
  exact periodicShift_inverse hu ⟨P.offset_mem.1, P.offset_mem.2.le⟩ hx

theorem PeriodicArray.normalize_restore (P : PeriodicArray n) {u : ℝ → ℝ}
    (hu : u 0 = u P.length) :
    EqOn (P.normalizeFunction (P.restoreFunction u)) u (Icc 0 P.length) := by
  intro x hx
  have hr : P.length - P.offset ∈ Icc 0 P.length :=
    ⟨sub_nonneg.mpr P.offset_mem.2.le, sub_le_self _ P.offset_mem.1⟩
  have hc : P.length - (P.length - P.offset) = P.offset := by ring
  change periodicShift P.length P.offset (periodicShift P.length (P.length - P.offset) u) x = u x
  simpa only [hc] using periodicShift_inverse hu hr hx

theorem PeriodicArray.normalize_zero (P : PeriodicArray n) (u : ℝ → ℝ) :
    P.normalizeFunction u 0 = u P.offset := by
  rw [normalizeFunction, periodicShift_left P.length P.offset u
    (sub_nonneg.mpr P.offset_mem.2.le), add_zero]

theorem PeriodicArray.normalize_mass_pairing (P : PeriodicArray n) {u v : ℝ → ℝ}
    (hu : P.Energy u) (hv : P.Energy v) :
    (∫ x in (0 : ℝ)..P.length, P.normalizeFunction u x * P.normalizeFunction v x) =
      ∫ x in (0 : ℝ)..P.length, u x * v x :=
  periodicShift_pairing hu.1 hu.2 hv.1 hv.2 ⟨P.offset_mem.1, P.offset_mem.2.le⟩

theorem PeriodicArray.restore_mass_pairing (P : PeriodicArray n) {u v : ℝ → ℝ}
    (hu : P.normalized.PeriodicEnergy u) (hv : P.normalized.PeriodicEnergy v) :
    (∫ x in (0 : ℝ)..P.length, P.restoreFunction u x * P.restoreFunction v x) =
      ∫ x in (0 : ℝ)..P.length, u x * v x :=
  periodicShift_pairing hu.1 hu.2 hv.1 hv.2
    ⟨sub_nonneg.mpr P.offset_mem.2.le, sub_le_self _ P.offset_mem.1⟩

theorem PeriodicArray.normalize_bilinear (P : PeriodicArray n) {u v : ℝ → ℝ}
    (hu : P.Energy u) (hv : P.Energy v) :
    P.diffusivity * (∫ x in (0 : ℝ)..P.length,
        deriv (P.normalizeFunction u) x * deriv (P.normalizeFunction v) x) +
      (∑ i, P.strength i * P.normalizeFunction u (P.normalized.site i) *
        P.normalizeFunction v (P.normalized.site i)) =
    P.diffusivity * (∫ x in (0 : ℝ)..P.length, deriv u x * deriv v x) +
      (∑ i, P.strength i * u (P.site i) * v (P.site i)) := by
  simp_rw [P.normalize_site_value]
  have h := periodicShift_derivative_pairing hu.1 hu.2 hv.1 hv.2
    ⟨P.offset_mem.1, P.offset_mem.2.le⟩
  change (∫ x in (0 : ℝ)..P.length,
    deriv (P.normalizeFunction u) x * deriv (P.normalizeFunction v) x) = _ at h
  rw [h]

theorem PeriodicArray.restore_bilinear (P : PeriodicArray n) {u v : ℝ → ℝ}
    (hu : P.normalized.PeriodicEnergy u) (hv : P.normalized.PeriodicEnergy v) :
    P.diffusivity * (∫ x in (0 : ℝ)..P.length,
        deriv (P.restoreFunction u) x * deriv (P.restoreFunction v) x) +
      (∑ i, P.strength i * P.restoreFunction u (P.site i) * P.restoreFunction v (P.site i)) =
    P.diffusivity * (∫ x in (0 : ℝ)..P.length, deriv u x * deriv v x) +
      (∑ i, P.strength i * u (P.normalized.site i) * v (P.normalized.site i)) := by
  simp_rw [P.restore_site_value hu.2, P.restore_site_value hv.2]
  have h := periodicShift_derivative_pairing hu.1 hu.2 hv.1 hv.2
    ⟨sub_nonneg.mpr P.offset_mem.2.le, sub_le_self _ P.offset_mem.1⟩
  change (∫ x in (0 : ℝ)..P.length,
    deriv (P.restoreFunction u) x * deriv (P.restoreFunction v) x) =
      ∫ x in (0 : ℝ)..P.length, deriv u x * deriv v x at h
  rw [h]

theorem PeriodicArray.normalize_pos (P : PeriodicArray n) {u : ℝ → ℝ}
    (hu : ∀ x ∈ Icc 0 P.length, 0 < u x) :
    ∀ x ∈ Icc 0 P.length, 0 < P.normalizeFunction u x :=
  periodicShift_pos ⟨P.offset_mem.1, P.offset_mem.2.le⟩ hu

theorem PeriodicArray.restore_pos (P : PeriodicArray n) {u : ℝ → ℝ}
    (hu : ∀ x ∈ Icc 0 P.length, 0 < u x) :
    ∀ x ∈ Icc 0 P.length, 0 < P.restoreFunction u x :=
  periodicShift_pos ⟨sub_nonneg.mpr P.offset_mem.2.le, sub_le_self _ P.offset_mem.1⟩ hu

theorem PeriodicArray.eqOn_scalar_of_normalized (P : PeriodicArray n) {u v : ℝ → ℝ} {c : ℝ}
    (hu : u 0 = u P.length) (hv : v 0 = v P.length)
    (h : EqOn (P.normalizeFunction v) (fun x => c * P.normalizeFunction u x) (Icc 0 P.length)) :
    EqOn v (fun x => c * u x) (Icc 0 P.length) := by
  have ht := periodicShift_congr
    (show P.length - P.offset ∈ Icc 0 P.length from
      ⟨sub_nonneg.mpr P.offset_mem.2.le, sub_le_self _ P.offset_mem.1⟩) h
  rw [periodicShift_const_mul] at ht
  intro x hx
  have he := ht hx
  change P.restoreFunction (P.normalizeFunction v) x =
    c * P.restoreFunction (P.normalizeFunction u) x at he
  rw [P.restore_normalize hv hx, P.restore_normalize hu hx] at he
  exact he

end TimeTraps.Spectral
