module

public import TimeTraps.Spectral.RobinPhaseEvolution
public import TimeTraps.Spectral.RobinRayleigh
public import TimeTraps.Spectral.RobinCapacity
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

noncomputable def RobinProblem.principalWavenumber (P : RobinProblem n) : ℝ :=
  Real.sqrt (P.principalValue / P.diffusivity)

theorem RobinProblem.principalWavenumber_pos (P : RobinProblem n) : 0 < P.principalWavenumber :=
  Real.sqrt_pos.2 (div_pos P.principalValue_pos P.diffusivity_pos)

theorem RobinProblem.principalWavenumber_sq (P : RobinProblem n) :
    P.principalWavenumber ^ 2 = P.principalValue / P.diffusivity :=
  Real.sq_sqrt (div_pos P.principalValue_pos P.diffusivity_pos).le

theorem RobinProblem.principalValue_formula (P : RobinProblem n) :
    P.principalValue = P.diffusivity * P.principalWavenumber ^ 2 := by
  rw [P.principalWavenumber_sq, mul_div_cancel₀ _ (ne_of_gt P.diffusivity_pos)]

theorem RobinProblem.principal_phase_bound (P : RobinProblem n) :
    P.length * P.principalWavenumber ≤
      Real.arctan (P.betaLeft / (P.diffusivity * P.principalWavenumber)) +
      Real.arctan (P.betaRight / (P.diffusivity * P.principalWavenumber)) +
        2 * ∑ i, Real.arctan (P.strength i / (2 * P.diffusivity * P.principalWavenumber)) := by
  obtain ⟨E, _⟩ := P.principal_eigenstate_exists
  exact E.phase_global_bound P.principalWavenumber_pos P.principalWavenumber_sq

theorem RobinProblem.principalWavenumber_le_root (P : RobinProblem n) {r : ℝ}
    (hr : 0 < r)
    (hroot : P.length * r = Real.arctan (P.betaLeft / (P.diffusivity * r)) +
      Real.arctan (P.betaRight / (P.diffusivity * r)) +
        2 * ∑ i, Real.arctan (P.strength i / (2 * P.diffusivity * r))) :
    P.principalWavenumber ≤ r := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, P.count_pos⟩, Finset.mem_univ _⟩
  have hc (k : ℝ) : robinPhaseCapacity Finset.univ
      (fun i => P.strength i / (2 * P.diffusivity))
      (P.betaLeft / P.diffusivity) (P.betaRight / P.diffusivity) k =
      Real.arctan (P.betaLeft / (P.diffusivity * k)) +
      Real.arctan (P.betaRight / (P.diffusivity * k)) + 2 * ∑ i, Real.arctan (P.strength i / (2 * P.diffusivity * k)) := by
    simp only [robinPhaseCapacity, phaseCapacity, div_div, Finset.mul_sum]
  exact le_robin_capacity_root Finset.univ hne (fun i => P.strength i / (2 * P.diffusivity))
    (fun i _ => div_pos (P.strength_pos i) (mul_pos (by norm_num) P.diffusivity_pos))
    (div_nonneg P.betaLeft_nonneg P.diffusivity_pos.le)
    (div_nonneg P.betaRight_nonneg P.diffusivity_pos.le)
    P.length_pos P.principalWavenumber_pos hr (by rwa [hc]) (by rw [hc]; exact P.principal_phase_bound)

theorem RobinProblem.principalValue_le_root (P : RobinProblem n) {r : ℝ}
    (hr : 0 < r)
    (hroot : P.length * r = Real.arctan (P.betaLeft / (P.diffusivity * r)) +
      Real.arctan (P.betaRight / (P.diffusivity * r)) +
        2 * ∑ i, Real.arctan (P.strength i / (2 * P.diffusivity * r))) :
    P.principalValue ≤ P.diffusivity * r ^ 2 := by
  rw [P.principalValue_formula]
  have h := P.principalWavenumber_le_root hr hroot
  have hs : P.principalWavenumber ^ 2 ≤ r ^ 2 := by nlinarith [P.principalWavenumber_pos]
  exact mul_le_mul_of_nonneg_left hs P.diffusivity_pos.le

theorem RobinProblem.principalWavenumber_eq_of_value (P : RobinProblem n) {r : ℝ}
    (hr : 0 < r) (he : P.principalValue = P.diffusivity * r ^ 2) :
    P.principalWavenumber = r := by
  have hsq := P.principalWavenumber_sq
  rw [he, mul_div_cancel_left₀ _ (ne_of_gt P.diffusivity_pos)] at hsq
  nlinarith [P.principalWavenumber_pos]

/-- A coefficient-independent bound, with the two endpoint phase capacities included. -/
theorem RobinProblem.principalWavenumber_lt_absorbing_bound (P : RobinProblem n) :
    P.principalWavenumber < (((n : ℝ) + 1) * Real.pi) / P.length := by
  have hc := robinPhaseCapacity_lt_bound Finset.univ
    (fun i : Fin n => P.strength i / (2 * P.diffusivity))
    (P.betaLeft / P.diffusivity) (P.betaRight / P.diffusivity) P.principalWavenumber
  simp only [robinPhaseCapacity, phaseCapacity, div_div,
    Finset.card_univ, Fintype.card_fin] at hc
  have hp := P.principal_phase_bound
  rw [Finset.mul_sum] at hp
  have h := lt_of_le_of_lt hp hc
  apply (lt_div_iff₀ P.length_pos).mpr
  simpa only [mul_comm] using h

theorem RobinProblem.principalValue_lt_absorbing_bound (P : RobinProblem n) :
    P.principalValue < P.diffusivity * ((((n : ℝ) + 1) * Real.pi) / P.length) ^ 2 := by
  have hk := P.principalWavenumber_lt_absorbing_bound
  have hcap : 0 < (((n : ℝ) + 1) * Real.pi) / P.length :=
    P.principalWavenumber_pos.trans hk
  have hs : P.principalWavenumber ^ 2 < ((((n : ℝ) + 1) * Real.pi) / P.length) ^ 2 := by
    have hm := mul_pos (sub_pos.mpr hk) (add_pos hcap P.principalWavenumber_pos)
    nlinarith
  rw [P.principalValue_formula]
  exact mul_lt_mul_of_pos_left hs P.diffusivity_pos

end TimeTraps.Spectral
