module

public import TimeTraps.Spectral.PhaseEvolution
public import TimeTraps.Spectral.CapacityRoot
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
The phase comparison applies to the principal value independently defined by
the full physical Rayleigh class. The scalar root only bounds that value;
it is not used to define the eigenvalue.
-/

namespace TimeTraps.Spectral

open Set
open scoped BigOperators

variable {n : ℕ}

noncomputable def SpectralProblem.principalWavenumber (P : SpectralProblem n) : ℝ :=
  Real.sqrt (P.principalValue / P.diffusivity)

theorem SpectralProblem.principalWavenumber_pos (P : SpectralProblem n) : 0 < P.principalWavenumber :=
  Real.sqrt_pos.2 (div_pos P.principalValue_pos P.diffusivity_pos)

theorem SpectralProblem.principalWavenumber_sq (P : SpectralProblem n) :
    P.principalWavenumber ^ 2 = P.principalValue / P.diffusivity :=
  Real.sq_sqrt (div_pos P.principalValue_pos P.diffusivity_pos).le

theorem SpectralProblem.principalValue_formula (P : SpectralProblem n) :
    P.principalValue = P.diffusivity * P.principalWavenumber ^ 2 := by
  rw [P.principalWavenumber_sq, mul_div_cancel₀ _ (ne_of_gt P.diffusivity_pos)]

theorem SpectralProblem.principal_phase_bound (P : SpectralProblem n) :
    P.length * P.principalWavenumber ≤
      2 * ∑ i, Real.arctan (P.strength i / (2 * P.diffusivity * P.principalWavenumber)) := by
  obtain ⟨E, _⟩ := P.principal_eigenstate_exists
  exact E.phase_global_bound P.principalWavenumber_pos P.principalWavenumber_sq

theorem SpectralProblem.principalWavenumber_le_root (P : SpectralProblem n) {r : ℝ}
    (hr : 0 < r)
    (hroot : P.length * r = 2 * ∑ i, Real.arctan (P.strength i / (2 * P.diffusivity * r))) :
    P.principalWavenumber ≤ r := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, P.count_pos⟩, Finset.mem_univ _⟩
  have hc (k : ℝ) : phaseCapacity Finset.univ (fun i => P.strength i / (2 * P.diffusivity)) k =
      2 * ∑ i, Real.arctan (P.strength i / (2 * P.diffusivity * k)) := by
    simp only [phaseCapacity, div_div, Finset.mul_sum]
  exact le_capacity_root Finset.univ hne (fun i => P.strength i / (2 * P.diffusivity))
    (fun i _ => div_pos (P.strength_pos i) (mul_pos (by norm_num) P.diffusivity_pos))
    P.length_pos P.principalWavenumber_pos hr (by rwa [hc]) (by rw [hc]; exact P.principal_phase_bound)

theorem SpectralProblem.principalValue_le_root (P : SpectralProblem n) {r : ℝ}
    (hr : 0 < r)
    (hroot : P.length * r = 2 * ∑ i, Real.arctan (P.strength i / (2 * P.diffusivity * r))) :
    P.principalValue ≤ P.diffusivity * r ^ 2 := by
  rw [P.principalValue_formula]
  have h := P.principalWavenumber_le_root hr hroot
  have hs : P.principalWavenumber ^ 2 ≤ r ^ 2 := by nlinarith [P.principalWavenumber_pos]
  exact mul_le_mul_of_nonneg_left hs P.diffusivity_pos.le

theorem SpectralProblem.principalWavenumber_eq_of_value (P : SpectralProblem n) {r : ℝ}
    (hr : 0 < r) (he : P.principalValue = P.diffusivity * r ^ 2) :
    P.principalWavenumber = r := by
  have hsq := P.principalWavenumber_sq
  rw [he, mul_div_cancel_left₀ _ (ne_of_gt P.diffusivity_pos)] at hsq
  nlinarith [P.principalWavenumber_pos]

end TimeTraps.Spectral
