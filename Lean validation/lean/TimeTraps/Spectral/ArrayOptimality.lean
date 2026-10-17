module

public import TimeTraps.Spectral.ArrayGeometry

@[expose] public section

/-! Prescribed-strength optimization over all sorted physical arrays. The
complete equality class is the normalized optimizer plus a common offset. -/

namespace TimeTraps.Spectral

open Set

variable {n : ℕ}

theorem PlacementProblem.arbitrary_array_upper_bound (C : PlacementProblem n)
    (x : Fin n → ℝ) (hx : C.AdmissibleArray x) :
    (C.array x hx).principalValue ≤ C.diffusivity * C.root ^ 2 := by
  rw [(C.array x hx).principalValue_eq_normalized]
  exact (C.array x hx).normalized.periodic_principal_bound

theorem PlacementProblem.array_value_eq_iff_gaps (C : PlacementProblem n)
    (x : Fin n → ℝ) (hx : C.AdmissibleArray x) :
    (C.array x hx).principalValue = C.diffusivity * C.root ^ 2 ↔
      (C.array x hx).gap = C.optimalCircleGap := by
  rw [(C.array x hx).principalValue_eq_normalized, C.array_normalized x hx]
  exact C.periodic_value_eq_iff_gaps _ _

theorem PlacementProblem.array_value_eq_iff_sites (C : PlacementProblem n)
    (x : Fin n → ℝ) (hx : C.AdmissibleArray x) :
    (C.array x hx).principalValue = C.diffusivity * C.root ^ 2 ↔
      ∀ i, x i = (C.array x hx).offset + C.optimalCircle.site i := by
  rw [C.array_value_eq_iff_gaps x hx, C.array_optimal_gap_iff x hx]

theorem PlacementProblem.optimal_array_value (C : PlacementProblem n) :
    (C.array C.optimalCircle.site C.optimalCircle_sites_admissible).principalValue =
      C.diffusivity * C.root ^ 2 :=
  (C.array_value_eq_iff_gaps _ C.optimalCircle_sites_admissible).mpr C.optimal_array_gaps

def PlacementProblem.arrayPrincipalValues (C : PlacementProblem n) : Set ℝ :=
  {ev | ∃ x : Fin n → ℝ, ∃ hx : C.AdmissibleArray x, ev = (C.array x hx).principalValue}

theorem PlacementProblem.array_placement_maximum (C : PlacementProblem n) :
    IsGreatest C.arrayPrincipalValues (C.diffusivity * C.root ^ 2) := by
  constructor
  · exact ⟨C.optimalCircle.site, C.optimalCircle_sites_admissible, C.optimal_array_value.symm⟩
  · rintro ev ⟨x, hx, rfl⟩
    exact C.arbitrary_array_upper_bound x hx

theorem PlacementProblem.array_strict_loss (C : PlacementProblem n)
    (x : Fin n → ℝ) (hx : C.AdmissibleArray x)
    (hne : ¬ ∀ i, x i = (C.array x hx).offset + C.optimalCircle.site i) :
    (C.array x hx).principalValue < C.diffusivity * C.root ^ 2 :=
  lt_of_le_of_ne (C.arbitrary_array_upper_bound x hx)
    (fun he => hne ((C.array_value_eq_iff_sites x hx).mp he))

theorem PlacementProblem.array_optimizer_iff (C : PlacementProblem n)
    (x : Fin n → ℝ) (hx : C.AdmissibleArray x) :
    (∀ y : Fin n → ℝ, ∀ hy : C.AdmissibleArray y,
      (C.array y hy).principalValue ≤ (C.array x hx).principalValue) ↔
      ∀ i, x i = (C.array x hx).offset + C.optimalCircle.site i := by
  constructor
  · intro h
    apply (C.array_value_eq_iff_sites x hx).mp
    apply le_antisymm (C.arbitrary_array_upper_bound x hx)
    have hm := h C.optimalCircle.site C.optimalCircle_sites_admissible
    rwa [C.optimal_array_value] at hm
  · intro he y hy
    rw [(C.array_value_eq_iff_sites x hx).mpr he]
    exact C.arbitrary_array_upper_bound y hy

end TimeTraps.Spectral
