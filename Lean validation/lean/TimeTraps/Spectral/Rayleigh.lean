module

public import TimeTraps.Spectral.GroundStateIdentity

@[expose] public section

/-!
The positive eigenvalue equals the independently defined physical Rayleigh
infimum. The infimum is attained over the full H1 space. Positive eigenstate
existence is supplied by the checked analytical shooting construction.
-/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Interval
open scoped BigOperators

variable {n : ℕ} {P : SpectralProblem n} {ev : ℝ}

theorem PositiveEigenstate.self_remainder_zero (E : PositiveEigenstate P ev) (e : Fin (n + 1)) :
    E.gapRemainder E.state e = 0 := by
  unfold gapRemainder
  calc
    _ = ∫ _x in (0 : ℝ)..P.shooting.gap e, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (P.shooting.gap_pos e).le
      intro x hx
      change (deriv (E.gapValue e) x - E.slope e x / E.gapValue e x * E.gapValue e x) ^ 2 = 0
      have hd : HasDerivAt (E.gapValue e) (E.slope e x) x := E.state_derivative e x hx
      rw [hd.deriv, div_mul_cancel₀ _ (ne_of_gt (E.gap_positive e (Ioo_subset_Icc_self hx))), sub_self, zero_pow (by norm_num : 2 ≠ 0)]
    _ = 0 := intervalIntegral.integral_zero

theorem PositiveEigenstate.self_quadraticForm (E : PositiveEigenstate P ev) :
    P.quadraticForm E.state = ev * P.squareMass E.state := by
  have h := E.ground_state_identity E.energy
  simp_rw [E.self_remainder_zero] at h
  simpa only [Finset.sum_const_zero, mul_zero, sub_eq_zero] using h

theorem PositiveEigenstate.squareMass_pos (E : PositiveEigenstate P ev) : 0 < P.squareMass E.state := by
  have hc := E.energy.continuousOn.pow 2
  change ContinuousOn (fun x => E.state x ^ 2) (uIcc (0 : ℝ) P.length) at hc
  apply intervalIntegral.integral_pos P.length_pos
    (show ContinuousOn (fun x => E.state x ^ 2) (Icc (0 : ℝ) P.length) from by
      simpa only [uIcc_of_le P.length_pos.le] using hc)
  · intro x _
    exact sq_nonneg _
  · exact ⟨0, ⟨le_rfl, P.length_pos.le⟩, sq_pos_of_pos (E.positive 0 ⟨le_rfl, P.length_pos.le⟩)⟩

theorem PositiveEigenstate.rayleigh_member (E : PositiveEigenstate P ev) : ev ∈ P.rayleighValues := by
  refine ⟨E.state, E.energy, E.squareMass_pos, ?_⟩
  rw [E.self_quadraticForm, mul_div_cancel_right₀ _ (ne_of_gt E.squareMass_pos)]

theorem PositiveEigenstate.rayleigh_lower (E : PositiveEigenstate P ev) {r : ℝ}
    (hr : r ∈ P.rayleighValues) : ev ≤ r := by
  obtain ⟨v, hv, hm, rfl⟩ := hr
  exact (le_div_iff₀ hm).mpr (E.quadraticForm_lower hv)

theorem PositiveEigenstate.principalValue_eq (E : PositiveEigenstate P ev) : P.principalValue = ev :=
  le_antisymm (csInf_le P.rayleighValues_bddBelow E.rayleigh_member)
    (le_csInf P.rayleighValues_nonempty (fun _ hr => E.rayleigh_lower hr))

theorem PositiveEigenstate.eigenvalue_unique (E : PositiveEigenstate P ev) {r : ℝ}
    (F : PositiveEigenstate P r) : ev = r :=
  E.principalValue_eq.symm.trans F.principalValue_eq

theorem SpectralProblem.principalValue_pos (P : SpectralProblem n) : 0 < P.principalValue := by
  obtain ⟨ev, hev, E, _⟩ := P.positive_eigenstate_exists
  rw [E.principalValue_eq]
  exact hev

theorem SpectralProblem.principal_eigenstate_exists (P : SpectralProblem n) :
    ∃ E : PositiveEigenstate P P.principalValue, E.state 0 = 1 := by
  obtain ⟨ev, _, E, hE⟩ := P.positive_eigenstate_exists
  rw [E.principalValue_eq]
  exact ⟨E, hE⟩

theorem SpectralProblem.rayleigh_minimum (P : SpectralProblem n) : IsLeast P.rayleighValues P.principalValue := by
  obtain ⟨E, _⟩ := P.principal_eigenstate_exists
  exact ⟨E.rayleigh_member, fun _ hr => E.rayleigh_lower hr⟩

end TimeTraps.Spectral
