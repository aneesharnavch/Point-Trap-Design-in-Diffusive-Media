module

public import TimeTraps.Spectral.RobinPhaseCoordinates
public import TimeTraps.Spectral.RobinPlacementBound
public import TimeTraps.Spectral.RobinCosineAttainment

@[expose] public section

/-!
Sharp prescribed-strength Robin spectral placement over all admissible physical
sites, with constructive attainment and the complete equality converse.
-/

namespace TimeTraps.Spectral

open Set TimeTraps.Interval
open scoped BigOperators

variable {n : ℕ}

theorem RobinPlacementProblem.sites_eq_of_attainment (C : RobinPlacementProblem n)
    (x : Fin n → ℝ) (hx : C.Admissible x)
    (he : (C.physical x hx).principalValue = C.diffusivity * C.root ^ 2) : x = C.candidateSite := by
  let P := C.physical x hx
  obtain ⟨E, _⟩ := P.principal_eigenstate_exists
  have hk2 : C.root ^ 2 = P.principalValue / P.diffusivity := by
    change C.root ^ 2 = (C.physical x hx).principalValue / C.diffusivity
    rw [he, mul_div_cancel_left₀ _ (ne_of_gt C.diffusivity_pos)]
  have hphase (i : Fin n) := E.phase_values_of_global_eq C.root_pos hk2 C.root_equation i
  have hj : (fun i => E.phase C.root i.succ 0 - E.phase C.root i.castSucc (P.shooting.gap i.castSucc)) =
      (fun i => 2 * C.angle i) := by
    funext i
    rw [(hphase i).1, (hphase i).2]
    change C.angle i - -C.angle i = 2 * C.angle i
    ring
  funext i
  have hp := E.phase_site_formula C.root_pos hk2 i
  rw [hj, (hphase i).2] at hp
  change C.root * x i = C.leftAngle + absorptionPrefix (fun j => 2 * C.angle j) i.castSucc - -C.angle i at hp
  rw [← C.boundary_angle_sum] at hp
  apply mul_left_cancel₀ (ne_of_gt C.root_pos)
  calc
    C.root * x i = C.root * C.boundary i.castSucc + C.angle i := by linarith
    _ = C.root * C.candidateSite i := by
      rw [RobinPlacementProblem.candidateSite, RobinPlacementProblem.cellLength]
      field_simp [ne_of_gt C.root_pos]

theorem RobinPlacementProblem.value_eq_iff_sites (C : RobinPlacementProblem n)
    (x : Fin n → ℝ) (hx : C.Admissible x) :
    (C.physical x hx).principalValue = C.diffusivity * C.root ^ 2 ↔ x = C.candidateSite := by
  constructor
  · exact C.sites_eq_of_attainment x hx
  · intro he
    subst x
    exact C.candidate_principalValue

def RobinPlacementProblem.principalValues (C : RobinPlacementProblem n) : Set ℝ :=
  {ev | ∃ x : Fin n → ℝ, ∃ hx : C.Admissible x, ev = (C.physical x hx).principalValue}

theorem RobinPlacementProblem.placement_maximum (C : RobinPlacementProblem n) :
    IsGreatest C.principalValues (C.diffusivity * C.root ^ 2) := by
  constructor
  · exact ⟨C.candidateSite, C.candidateSite_admissible, C.candidate_principalValue.symm⟩
  · rintro ev ⟨x, hx, rfl⟩
    exact C.arbitrary_upper_bound x hx

theorem RobinPlacementProblem.strict_loss_of_other_sites (C : RobinPlacementProblem n)
    (x : Fin n → ℝ) (hx : C.Admissible x) (hne : x ≠ C.candidateSite) :
    (C.physical x hx).principalValue < C.diffusivity * C.root ^ 2 :=
  lt_of_le_of_ne (C.arbitrary_upper_bound x hx) (fun he => hne ((C.value_eq_iff_sites x hx).mp he))

theorem RobinPlacementProblem.optimizer_iff (C : RobinPlacementProblem n)
    (x : Fin n → ℝ) (hx : C.Admissible x) :
    (∀ y : Fin n → ℝ, ∀ hy : C.Admissible y,
      (C.physical y hy).principalValue ≤ (C.physical x hx).principalValue) ↔ x = C.candidateSite := by
  constructor
  · intro h
    apply (C.value_eq_iff_sites x hx).mp
    apply le_antisymm (C.arbitrary_upper_bound x hx)
    have ho := h C.candidateSite C.candidateSite_admissible
    change C.candidatePhysical.principalValue ≤ (C.physical x hx).principalValue at ho
    rwa [C.candidate_principalValue] at ho
  · intro he
    subst x
    intro y hy
    change (C.physical y hy).principalValue ≤ C.candidatePhysical.principalValue
    rw [C.candidate_principalValue]
    exact C.arbitrary_upper_bound y hy

end TimeTraps.Spectral
