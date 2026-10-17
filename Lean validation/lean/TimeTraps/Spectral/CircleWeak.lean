module

public import TimeTraps.Spectral.CircleRayleigh
public import TimeTraps.Spectral.NetworkWeakCongruence

@[expose] public section

/-! The original single-interval weak equation against all periodic H1
functions, obtained without restricting the test class to smooth functions. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Interval TimeTraps.Graph
open scoped BigOperators

variable {n : ℕ} {ev : ℝ}

structure PeriodicWeakEigenEquation (C : CircleProblem n) (ev : ℝ) (u : ℝ → ℝ) : Prop where
  energy : C.PeriodicEnergy u
  weak_form : ∀ v : ℝ → ℝ, C.PeriodicEnergy v →
    C.diffusivity * (∫ x in (0 : ℝ)..C.length, deriv u x * deriv v x) +
      (∑ i, C.strength i * u (C.site i) * v (C.site i)) =
        ev * (∫ x in (0 : ℝ)..C.length, u x * v x)

theorem CircleProblem.restrict_bilinear (C : CircleProblem n) {u v : ℝ → ℝ}
    (hu : IntervalEnergy u 0 C.length) (hv : IntervalEnergy v 0 C.length) :
    (∑ i, ∫ x in (0 : ℝ)..C.gap i,
      C.diffusivity * deriv (C.restriction u i) x * deriv (C.restriction v i) x) =
      C.diffusivity * (∫ x in (0 : ℝ)..C.length, deriv u x * deriv v x) := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ C.count_pos)
  | succ n =>
    simp_rw [C.restriction_deriv]
    have h := C.cut.integral_gap_sum (hu.bilinear_integrable hv
      (show ContinuousOn (fun _ : ℝ => C.diffusivity) (uIcc 0 C.length) from continuousOn_const))
    simp_rw [C.cut_gapLength] at h
    calc
      _ = ∫ x in (0 : ℝ)..C.length, C.diffusivity * deriv u x * deriv v x := h
      _ = _ := by simp only [mul_assoc, intervalIntegral.integral_const_mul]

theorem CircleProblem.restrict_mass_pairing (C : CircleProblem n) {u v : ℝ → ℝ}
    (hu : IntervalEnergy u 0 C.length) (hv : IntervalEnergy v 0 C.length) :
    (∑ i, ∫ x in (0 : ℝ)..C.gap i, C.restriction u i x * C.restriction v i x) =
      ∫ x in (0 : ℝ)..C.length, u x * v x := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ C.count_pos)
  | succ n =>
    have h := C.cut.integral_gap_sum (hu.continuousOn.mul hv.continuousOn).intervalIntegrable
    simp_rw [C.cut_gapLength] at h
    exact h

theorem CircleProblem.periodic_weak_of_restriction (C : CircleProblem n) {u : ℝ → ℝ}
    (hu : C.PeriodicEnergy u)
    (h : NetworkWeakEigenEquation C.network ev (fun i => u (C.site i)) (C.restriction u)) :
    PeriodicWeakEigenEquation C ev u := by
  refine ⟨hu, ?_⟩
  intro v hv
  have he := h.weak_form (fun i => v (C.site i)) (C.restriction v) (C.restrict_periodic_energy hv)
  change (∑ i, ∫ x in (0 : ℝ)..C.gap i,
    C.diffusivity * deriv (C.restriction u i) x * deriv (C.restriction v i) x) +
    (∑ i, C.strength i * u (C.site i) * v (C.site i)) =
    ev * (∑ i, ∫ x in (0 : ℝ)..C.gap i, C.restriction u i x * C.restriction v i x) at he
  rw [C.restrict_bilinear hu.1 hv.1, C.restrict_mass_pairing hu.1 hv.1] at he
  exact he

theorem CircleProblem.assembled_weak (C : CircleProblem (n + 1))
    {U : Fin (n + 1) → ℝ} {u : Fin (n + 1) → ℝ → ℝ}
    (h : NetworkWeakEigenEquation C.network ev U u) :
    PeriodicWeakEigenEquation C ev (C.assembled U u) := by
  apply C.periodic_weak_of_restriction ⟨C.assembled_energy h.energy, C.assembled_periodic h.energy⟩
  have ht : NetworkWeakEigenEquation C.network ev U (C.restriction (C.assembled U u)) := by
    apply h.congr
    intro e x hx
    exact (C.assembled_gap h.energy e hx).symm
  simpa only [C.assembled_site h.energy] using ht

theorem CircleProblem.restricted_weak (C : CircleProblem n) {u : ℝ → ℝ}
    (h : PeriodicWeakEigenEquation C ev u) :
    NetworkWeakEigenEquation C.network ev (fun i => u (C.site i)) (C.restriction u) := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ C.count_pos)
  | succ n =>
    refine ⟨C.restrict_periodic_energy h.energy, ?_⟩
    intro W w hw
    have hv : C.PeriodicEnergy (C.assembled W w) :=
      ⟨C.assembled_energy hw, C.assembled_periodic hw⟩
    have he := h.weak_form (C.assembled W w) hv
    rw [← C.restrict_bilinear h.energy.1 hv.1, ← C.restrict_mass_pairing h.energy.1 hv.1] at he
    simp_rw [C.assembled_site hw] at he
    have hd : (∑ e, ∫ x in (0 : ℝ)..C.gap e,
        C.diffusivity * deriv (C.restriction u e) x * deriv (C.restriction (C.assembled W w) e) x) =
        ∑ e, ∫ x in (0 : ℝ)..C.gap e,
          C.diffusivity * deriv (C.restriction u e) x * deriv (w e) x := by
      apply Finset.sum_congr rfl
      intro e _
      apply intervalIntegral.integral_congr_uIoo
      intro x hx
      have hx' : x ∈ Ioo 0 (C.gap e) := by simpa only [uIoo_of_le (C.gap_pos e).le] using hx
      dsimp only
      rw [C.restriction_deriv (C.assembled W w), C.assembled_gap_deriv hw e hx']
    have hm : (∑ e, ∫ x in (0 : ℝ)..C.gap e,
        C.restriction u e x * C.restriction (C.assembled W w) e x) =
        ∑ e, ∫ x in (0 : ℝ)..C.gap e, C.restriction u e x * w e x := by
      apply Finset.sum_congr rfl
      intro e _
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc 0 (C.gap e) := by simpa only [uIcc_of_le (C.gap_pos e).le] using hx
      change C.restriction u e x * C.assembled W w (C.site e + x) = C.restriction u e x * w e x
      rw [C.assembled_gap hw e hx']
    rw [hd, hm] at he
    exact he

theorem CircleProblem.periodic_weak_iff (C : CircleProblem n) {u : ℝ → ℝ}
    (hu : C.PeriodicEnergy u) :
    PeriodicWeakEigenEquation C ev u ↔
      NetworkWeakEigenEquation C.network ev (fun i => u (C.site i)) (C.restriction u) :=
  ⟨C.restricted_weak, C.periodic_weak_of_restriction hu⟩

theorem CircleProblem.periodic_positive_ground_state (C : CircleProblem n) :
    ∃ w : ℝ → ℝ, PeriodicWeakEigenEquation C C.periodicPrincipalValue w ∧
      (∀ x ∈ Icc 0 C.length, 0 < w x) ∧ 0 < C.periodicMass w ∧
      C.periodicQuadraticForm w / C.periodicMass w = C.periodicPrincipalValue := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ C.count_pos)
  | succ n =>
    let : Nonempty (Fin (n + 1)) := ⟨0⟩
    obtain ⟨F⟩ := C.network.principal_eigenstate_exists
    refine ⟨C.assembled F.nodal F.state, ?_, ?_, ?_, ?_⟩
    · rw [C.periodicPrincipalValue_eq]
      exact C.assembled_weak F.to_weak
    · intro x hx
      obtain ⟨e, he⟩ := C.cut.gap_cover hx
      have ht : x - C.site e ∈ Icc 0 (C.gap e) := by
        rw [← C.cut_gapLength]
        exact ⟨sub_nonneg.mpr he.1, sub_le_sub_right he.2 _⟩
      have ha := C.assembled_gap F.energy e ht
      rw [add_sub_cancel] at ha
      rw [ha]
      exact F.positive e _ ht
    · rw [C.assembled_mass F.energy]
      exact F.squareMass_pos
    · rw [C.assembled_quadraticForm F.energy, C.assembled_mass F.energy,
        F.to_weak.self_quadraticForm, mul_div_cancel_right₀ _ (ne_of_gt F.squareMass_pos),
        C.periodicPrincipalValue_eq]

end TimeTraps.Spectral
