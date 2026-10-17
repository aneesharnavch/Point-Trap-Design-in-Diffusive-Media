module

public import TimeTraps.Spectral.ArrayPairing

@[expose] public section

/-! The independently stated weak eigenvalue equation for arbitrary physical
arrays. Both rotation directions use the full periodic H1 test space. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {n : ℕ} {P : PeriodicArray n} {ev : ℝ}

structure ArrayWeakEigenEquation (P : PeriodicArray n) (ev : ℝ) (u : ℝ → ℝ) : Prop where
  energy : P.Energy u
  weak_form : ∀ v : ℝ → ℝ, P.Energy v →
    P.diffusivity * (∫ x in (0 : ℝ)..P.length, deriv u x * deriv v x) +
      (∑ i, P.strength i * u (P.site i) * v (P.site i)) =
        ev * (∫ x in (0 : ℝ)..P.length, u x * v x)

theorem ArrayWeakEigenEquation.normalized {u : ℝ → ℝ}
    (h : ArrayWeakEigenEquation P ev u) :
    PeriodicWeakEigenEquation P.normalized ev (P.normalizeFunction u) := by
  refine ⟨P.normalize_energy h.energy, ?_⟩
  intro v hv
  have hrv := P.restore_energy hv
  have he := h.weak_form (P.restoreFunction v) hrv
  rw [← P.normalize_bilinear h.energy hrv, ← P.normalize_mass_pairing h.energy hrv] at he
  have hc := P.normalize_restore hv.2
  have hd := integral_derivative_pairing_congr_right
    (u := P.normalizeFunction u) P.length_pos.le hc
  have hm := integral_pairing_congr_right (u := P.normalizeFunction u) P.length_pos.le hc
  have hs (i : Fin n) : P.normalizeFunction (P.restoreFunction v) (P.normalized.site i) =
      v (P.normalized.site i) := hc ⟨(P.normalized.site_mem i).1, (P.normalized.site_mem i).2.le⟩
  rw [hd, hm] at he
  simp_rw [hs] at he
  exact he

theorem PeriodicArray.restored_weak (P : PeriodicArray n) {u : ℝ → ℝ}
    (h : PeriodicWeakEigenEquation P.normalized ev u) :
    ArrayWeakEigenEquation P ev (P.restoreFunction u) := by
  refine ⟨P.restore_energy h.energy, ?_⟩
  intro v hv
  have hnv := P.normalize_energy hv
  have he := h.weak_form (P.normalizeFunction v) hnv
  change P.diffusivity * (∫ x in (0 : ℝ)..P.length, deriv u x * deriv (P.normalizeFunction v) x) +
    (∑ i, P.strength i * u (P.normalized.site i) * P.normalizeFunction v (P.normalized.site i)) =
      ev * (∫ x in (0 : ℝ)..P.length, u x * P.normalizeFunction v x) at he
  rw [← P.restore_bilinear h.energy hnv, ← P.restore_mass_pairing h.energy hnv] at he
  have hc := P.restore_normalize hv.2
  have hd := integral_derivative_pairing_congr_right
    (u := P.restoreFunction u) P.length_pos.le hc
  have hm := integral_pairing_congr_right (u := P.restoreFunction u) P.length_pos.le hc
  have hs (i : Fin n) : P.restoreFunction (P.normalizeFunction v) (P.site i) = v (P.site i) :=
    hc ⟨(P.site_mem i).1, (P.site_mem i).2.le⟩
  rw [hd, hm] at he
  simp_rw [hs] at he
  exact he

theorem ArrayWeakEigenEquation.congr {u w : ℝ → ℝ}
    (h : ArrayWeakEigenEquation P ev u) (huw : EqOn u w (Icc 0 P.length)) :
    ArrayWeakEigenEquation P ev w := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply h.energy.1.congr
    simpa only [uIcc_of_le P.length_pos.le] using huw
  · rw [← huw ⟨le_rfl, P.length_pos.le⟩, ← huw ⟨P.length_pos.le, le_rfl⟩]
    exact h.energy.2
  · intro v hv
    have hd : (∫ x in (0 : ℝ)..P.length, deriv w x * deriv v x) =
        ∫ x in (0 : ℝ)..P.length, deriv u x * deriv v x := by
      simpa only [mul_comm] using integral_derivative_pairing_congr_right
        (u := v) P.length_pos.le huw.symm
    have hm : (∫ x in (0 : ℝ)..P.length, w x * v x) =
        ∫ x in (0 : ℝ)..P.length, u x * v x := by
      simpa only [mul_comm] using integral_pairing_congr_right (u := v) P.length_pos.le huw.symm
    have hs (i : Fin n) : w (P.site i) = u (P.site i) :=
      (huw ⟨(P.site_mem i).1, (P.site_mem i).2.le⟩).symm
    rw [hd, hm]
    simp_rw [hs]
    exact h.weak_form v hv

theorem PeriodicArray.weak_iff_normalized (P : PeriodicArray n) {u : ℝ → ℝ}
    (hu : P.Energy u) :
    ArrayWeakEigenEquation P ev u ↔
      PeriodicWeakEigenEquation P.normalized ev (P.normalizeFunction u) := by
  constructor
  · exact ArrayWeakEigenEquation.normalized
  · intro h
    exact (P.restored_weak h).congr (P.restore_normalize hu.2)

theorem ArrayWeakEigenEquation.self_quadraticForm {u : ℝ → ℝ}
    (h : ArrayWeakEigenEquation P ev u) : P.quadraticForm u = ev * P.squareMass u := by
  simpa only [PeriodicArray.quadraticForm, PeriodicArray.squareMass, pow_two, mul_assoc] using
    h.weak_form u h.energy

theorem PeriodicArray.positive_ground_state (P : PeriodicArray n) :
    ∃ u : ℝ → ℝ, ArrayWeakEigenEquation P P.principalValue u ∧
      (∀ x ∈ Icc 0 P.length, 0 < u x) ∧ 0 < P.squareMass u ∧
      P.quadraticForm u / P.squareMass u = P.principalValue := by
  obtain ⟨u, hu, hp, hm, he⟩ := P.normalized.periodic_positive_ground_state
  refine ⟨P.restoreFunction u, ?_, P.restore_pos hp, ?_, ?_⟩
  · rw [P.principalValue_eq_normalized]
    exact P.restored_weak hu
  · rwa [P.restore_mass hu.energy]
  · rw [P.restore_quadraticForm hu.energy, P.restore_mass hu.energy,
      P.principalValue_eq_normalized]
    exact he

end TimeTraps.Spectral
