module

public import TimeTraps.Analysis.SignedPeriodicPointPositiveGround

@[expose] public section

/-! Closed-interval positivity for the full physical periodic weak
eigenproblem, including both identified endpoint values. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedPeriodicPointProblem.physical_eigen_hilbert
    (P : SignedPeriodicPointProblem ι l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (huz : u l = u r) (ev : ℝ)
    (he : ∀ v : ℝ → ℝ, IntervalEnergy v l r →
      (v l = v r) →
      intervalPointForm P.diffusivity P.strength P.site l r u v =
        ev * ∫ x in l..r, u x * v x) :
    ∀ v : IntervalPeriodicSpace P.boundary,
      P.form (P.boundary.ofEnergy hu huz.symm) v = ev *
        inner ℝ (P.boundary.stateL (P.boundary.ofEnergy hu huz.symm)) (P.boundary.stateL v) := by
  apply (P.hilbert_eigen_iff_physical (P.boundary.ofEnergy hu huz.symm) ev).mpr
  intro v hv hvz
  rw [intervalPointForm_congr P.diffusivity P.strength P.site P.boundary.interval_pos.le P.site_mem
    (P.boundary.ofEnergy_representative hu huz.symm) (fun _ _ => rfl), he v hv hvz]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le P.boundary.interval_pos.le
  intro x hx
  change u x * v x = (P.boundary.ofEnergy hu huz.symm).val.representative P.boundary.interval_pos x * v x
  rw [P.boundary.ofEnergy_representative hu huz.symm (Ioo_subset_Icc_self hx)]

theorem SignedPeriodicPointProblem.nonnegative_physical_eigenstate_pos
    (P : SignedPeriodicPointProblem ι l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (huz : u l = u r) (ev : ℝ)
    (hne : ∃ x ∈ Icc l r, u x ≠ 0) (hnonneg : ∀ x ∈ Icc l r, 0 ≤ u x)
    (he : ∀ v : ℝ → ℝ, IntervalEnergy v l r →
      (v l = v r) →
      intervalPointForm P.diffusivity P.strength P.site l r u v =
        ev * ∫ x in l..r, u x * v x) : ∀ x ∈ Icc l r, 0 < u x := by
  have hU : P.boundary.ofEnergy hu huz.symm ≠ 0 := by
    intro hz
    obtain ⟨x, hx, hnx⟩ := hne
    have heval := congrArg (fun w : IntervalPeriodicSpace P.boundary =>
      evalL P.boundary.interval_pos x hx w.val) hz
    change evalL P.boundary.interval_pos x hx (P.boundary.ofEnergy hu huz.symm).val =
      evalL P.boundary.interval_pos x hx 0 at heval
    rw [map_zero] at heval
    change (P.boundary.ofEnergy hu huz.symm).val.representative P.boundary.interval_pos x = 0 at heval
    rw [P.boundary.ofEnergy_representative hu huz.symm hx] at heval
    exact hnx heval
  have hN : ∀ x ∈ Icc l r,
      0 ≤ (P.boundary.ofEnergy hu huz.symm).val.representative P.boundary.interval_pos x := by
    intro x hx
    rw [P.boundary.ofEnergy_representative hu huz.symm hx]
    exact hnonneg x hx
  intro x hx
  have hp := P.nonnegative_eigenstate_pos (P.boundary.ofEnergy hu huz.symm) ev hU hN
    (P.physical_eigen_hilbert hu huz ev he) x hx
  rwa [P.boundary.ofEnergy_representative hu huz.symm hx] at hp

end TimeTraps.Analysis
