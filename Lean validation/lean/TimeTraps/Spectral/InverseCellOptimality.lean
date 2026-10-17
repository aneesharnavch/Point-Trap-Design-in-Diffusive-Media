module

public import TimeTraps.Spectral.InverseCellBijection
public import TimeTraps.Analysis.FinitePrefix

@[expose] public section

/-! Inverse cells reconstruct the actual unique optimizing physical sites,
and attain the prescribed principal value D k². -/

namespace TimeTraps.Spectral

open Set TimeTraps.Analysis

variable {n : ℕ}

theorem InverseCellProblem.constructed_cellLength (P : InverseCellProblem n)
    {ℓ : Fin n → ℝ} (hℓ : P.Cells ℓ) :
    (P.placement (P.cellStrength ℓ) (P.cellStrength_pos hℓ)).cellLength = ℓ := by
  funext i
  change 2 * Real.arctan (P.cellStrength ℓ i /
    (2 * P.diffusivity * (P.placement (P.cellStrength ℓ) (P.cellStrength_pos hℓ)).root)) /
      (P.placement (P.cellStrength ℓ) (P.cellStrength_pos hℓ)).root = ℓ i
  rw [P.cellStrength_root hℓ]
  exact congrFun (P.strengthCell_cellStrength hℓ) i

theorem InverseCellProblem.constructed_site (P : InverseCellProblem n)
    {ℓ : Fin n → ℝ} (hℓ : P.Cells ℓ) (i : Fin n) :
    (P.placement (P.cellStrength ℓ) (P.cellStrength_pos hℓ)).optimalSite i =
      vectorPrefix ℓ i.val + ℓ i / 2 := by
  simp only [PlacementProblem.optimalSite, PlacementProblem.boundary, P.constructed_cellLength hℓ]
  rfl

theorem InverseCellProblem.constructed_value (P : InverseCellProblem n)
    {ℓ : Fin n → ℝ} (hℓ : P.Cells ℓ) :
    (P.placement (P.cellStrength ℓ) (P.cellStrength_pos hℓ)).optimalPhysical.principalValue =
      P.diffusivity * P.wavenumber ^ 2 := by
  rw [(P.placement (P.cellStrength ℓ) (P.cellStrength_pos hℓ)).optimal_principalValue,
    P.cellStrength_root hℓ]
  rfl

theorem InverseCellProblem.constructed_maximum (P : InverseCellProblem n)
    {ℓ : Fin n → ℝ} (hℓ : P.Cells ℓ) :
    IsGreatest (P.placement (P.cellStrength ℓ) (P.cellStrength_pos hℓ)).principalValues
      (P.diffusivity * P.wavenumber ^ 2) := by
  have h := (P.placement (P.cellStrength ℓ) (P.cellStrength_pos hℓ)).placement_maximum
  rw [P.cellStrength_root hℓ] at h
  exact h

theorem InverseCellProblem.constructed_value_eq_iff_sites (P : InverseCellProblem n)
    {ℓ : Fin n → ℝ} (hℓ : P.Cells ℓ) (x : Fin n → ℝ)
    (hx : (P.placement (P.cellStrength ℓ) (P.cellStrength_pos hℓ)).Admissible x) :
    ((P.placement (P.cellStrength ℓ) (P.cellStrength_pos hℓ)).physical x hx).principalValue =
      P.diffusivity * P.wavenumber ^ 2 ↔ ∀ i, x i = vectorPrefix ℓ i.val + ℓ i / 2 := by
  have h := (P.placement (P.cellStrength ℓ) (P.cellStrength_pos hℓ)).value_eq_iff_sites x hx
  rw [P.cellStrength_root hℓ] at h
  change ((P.placement (P.cellStrength ℓ) (P.cellStrength_pos hℓ)).physical x hx).principalValue =
    P.diffusivity * P.wavenumber ^ 2 ↔
      x = (P.placement (P.cellStrength ℓ) (P.cellStrength_pos hℓ)).optimalSite at h
  rw [h, funext_iff]
  simp only [P.constructed_site hℓ]

theorem InverseCellProblem.reconstructed_sites_admissible (P : InverseCellProblem n)
    {ℓ : Fin n → ℝ} (hℓ : P.Cells ℓ) :
    (P.placement (P.cellStrength ℓ) (P.cellStrength_pos hℓ)).Admissible
      (fun i => vectorPrefix ℓ i.val + ℓ i / 2) := by
  have he := funext (P.constructed_site hℓ)
  rw [← he]
  exact (P.placement (P.cellStrength ℓ) (P.cellStrength_pos hℓ)).optimalSite_admissible

theorem InverseCellProblem.reconstructed_value (P : InverseCellProblem n)
    {ℓ : Fin n → ℝ} (hℓ : P.Cells ℓ) :
    ((P.placement (P.cellStrength ℓ) (P.cellStrength_pos hℓ)).physical
      (fun i => vectorPrefix ℓ i.val + ℓ i / 2) (P.reconstructed_sites_admissible hℓ)).principalValue =
        P.diffusivity * P.wavenumber ^ 2 :=
  (P.constructed_value_eq_iff_sites hℓ _ (P.reconstructed_sites_admissible hℓ)).mpr (fun _ => rfl)

end TimeTraps.Spectral
