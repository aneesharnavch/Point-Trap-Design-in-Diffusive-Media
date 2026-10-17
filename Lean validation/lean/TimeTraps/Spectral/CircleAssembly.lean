module

public import TimeTraps.Spectral.CirclePhysicalProblem

@[expose] public section

/-! Exact preservation of mass and derivative/reaction energy when arbitrary
matching circle H1 functions are assembled on the physical periodic interval. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Interval TimeTraps.Graph
open scoped BigOperators

variable {n : ℕ}

theorem CircleProblem.assembled_mass (C : CircleProblem (n + 1))
    {U : Fin (n + 1) → ℝ} {u : Fin (n + 1) → ℝ → ℝ}
    (hu : GraphEnergy C.network.geometry U u) :
    C.periodicMass (C.assembled U u) = C.network.squareMass u := by
  rw [← C.restrict_mass (C.assembled_energy hu)]
  unfold SpectralNetwork.squareMass
  apply Finset.sum_congr rfl
  intro e _
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc 0 (C.gap e) := by
    simpa only [CircleProblem.network, uIcc_of_le (C.gap_pos e).le] using hx
  change C.assembled U u (C.site e + x) ^ 2 = u e x ^ 2
  rw [C.assembled_gap hu e hx']

theorem CircleProblem.assembled_derivative_energy (C : CircleProblem (n + 1))
    {U : Fin (n + 1) → ℝ} {u : Fin (n + 1) → ℝ → ℝ}
    (hu : GraphEnergy C.network.geometry U u) :
    (∫ x in (0 : ℝ)..C.length, deriv (C.assembled U u) x ^ 2) =
      ∑ i, ∫ x in (0 : ℝ)..C.gap i, deriv (u i) x ^ 2 := by
  rw [← C.restrict_derivative_energy (C.assembled_energy hu)]
  apply Finset.sum_congr rfl
  intro e _
  apply intervalIntegral.integral_congr_uIoo
  intro x hx
  have hx' : x ∈ Ioo 0 (C.gap e) := by
    simpa only [uIoo_of_le (C.gap_pos e).le] using hx
  dsimp only
  rw [C.restriction_deriv, C.assembled_gap_deriv hu e hx']

theorem CircleProblem.assembled_quadraticForm (C : CircleProblem (n + 1))
    {U : Fin (n + 1) → ℝ} {u : Fin (n + 1) → ℝ → ℝ}
    (hu : GraphEnergy C.network.geometry U u) :
    C.periodicQuadraticForm (C.assembled U u) = C.network.quadraticForm U u := by
  unfold periodicQuadraticForm
  rw [C.assembled_derivative_energy hu]
  simp_rw [C.assembled_site hu]
  rfl

theorem CircleProblem.periodic_representative (C : CircleProblem n)
    {U : Fin n → ℝ} {u : Fin n → ℝ → ℝ} (hu : GraphEnergy C.network.geometry U u) :
    ∃ w : ℝ → ℝ, C.PeriodicEnergy w ∧
      (∀ i, w (C.site i) = U i) ∧
      (∀ i x, x ∈ Icc 0 (C.gap i) → w (C.site i + x) = u i x) ∧
      C.periodicMass w = C.network.squareMass u ∧
      C.periodicQuadraticForm w = C.network.quadraticForm U u := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ C.count_pos)
  | succ n =>
    exact ⟨C.assembled U u, ⟨C.assembled_energy hu, C.assembled_periodic hu⟩,
      C.assembled_site hu, fun i _ hx => C.assembled_gap hu i hx,
      C.assembled_mass hu, C.assembled_quadraticForm hu⟩

theorem CircleProblem.assembled_restriction (C : CircleProblem (n + 1)) {w : ℝ → ℝ}
    (hw : C.PeriodicEnergy w) :
    EqOn (C.assembled (fun i => w (C.site i)) (C.restriction w)) w (Icc 0 C.length) := by
  intro x hx
  obtain ⟨e, he⟩ := C.cut.gap_cover hx
  have ht : x - C.site e ∈ Icc 0 (C.gap e) := by
    rw [← C.cut_gapLength]
    exact ⟨sub_nonneg.mpr he.1, sub_le_sub_right he.2 _⟩
  have h := C.assembled_gap (C.restrict_periodic_energy hw) e ht
  change C.assembled (fun i => w (C.site i)) (C.restriction w)
    (C.site e + (x - C.site e)) = w (C.site e + (x - C.site e)) at h
  simpa only [add_sub_cancel] using h

end TimeTraps.Spectral
