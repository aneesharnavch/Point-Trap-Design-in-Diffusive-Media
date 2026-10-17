module

public import TimeTraps.Spectral.CircleCosine

@[expose] public section

/-! Exact characterization of maximizing cyclic gaps for each prescribed
cyclic ordering of positive strengths. These are intrinsic circle statements. -/

namespace TimeTraps.Spectral

open Set

variable {n : ℕ}

theorem PlacementProblem.circle_value_eq_iff_gaps (C : PlacementProblem n)
    (g : Fin n → ℝ) (hg : C.AdmissibleCircle g) :
    (C.circle g hg).network.principalValue = C.diffusivity * C.root ^ 2 ↔
      g = C.optimalCircleGap := by
  constructor
  · intro he
    let : Nonempty (Fin n) := ⟨⟨0, C.count_pos⟩⟩
    obtain ⟨F⟩ := (C.circle g hg).network.principal_eigenstate_exists
    have hk2 : C.root ^ 2 = (C.circle g hg).network.principalValue / C.diffusivity := by
      rw [he, mul_div_cancel_left₀ _ (ne_of_gt C.diffusivity_pos)]
    have hv := CircleProblem.phase_values_of_global_eq F C.root_pos hk2 C.root_equation
    apply funext
    intro i
    have hl := (hv i).1
    have hr := (hv (finRotate n i)).2
    simp only [Equiv.symm_apply_apply] at hr
    change F.phase C.root i 0 = C.angle i at hl
    change F.phase C.root i (g i) = -C.angle (finRotate n i) at hr
    have ha := F.phase_affine C.root_pos hk2 i ⟨(hg.1 i).le, le_rfl⟩
    change F.phase C.root i (g i) = F.phase C.root i 0 - C.root * g i at ha
    unfold optimalCircleGap
    apply (eq_div_iff (ne_of_gt C.root_pos)).mpr
    linarith
  · rintro rfl
    exact C.optimalCircle_principalValue

def PlacementProblem.circlePrincipalValues (C : PlacementProblem n) : Set ℝ :=
  {ev | ∃ g : Fin n → ℝ, ∃ hg : C.AdmissibleCircle g,
    ev = (C.circle g hg).network.principalValue}

theorem PlacementProblem.circle_placement_maximum (C : PlacementProblem n) :
    IsGreatest C.circlePrincipalValues (C.diffusivity * C.root ^ 2) := by
  constructor
  · exact ⟨C.optimalCircleGap, C.optimalCircleGap_admissible, C.optimalCircle_principalValue.symm⟩
  · rintro ev ⟨g, hg, rfl⟩
    exact C.arbitrary_circle_upper_bound g hg

theorem PlacementProblem.circle_strict_loss (C : PlacementProblem n)
    (g : Fin n → ℝ) (hg : C.AdmissibleCircle g) (hne : g ≠ C.optimalCircleGap) :
    (C.circle g hg).network.principalValue < C.diffusivity * C.root ^ 2 :=
  lt_of_le_of_ne (C.arbitrary_circle_upper_bound g hg)
    (fun he => hne ((C.circle_value_eq_iff_gaps g hg).mp he))

theorem PlacementProblem.circle_optimizer_iff (C : PlacementProblem n)
    (g : Fin n → ℝ) (hg : C.AdmissibleCircle g) :
    (∀ d : Fin n → ℝ, ∀ hd : C.AdmissibleCircle d,
      (C.circle d hd).network.principalValue ≤ (C.circle g hg).network.principalValue) ↔
      g = C.optimalCircleGap := by
  constructor
  · intro h
    apply (C.circle_value_eq_iff_gaps g hg).mp
    apply le_antisymm (C.arbitrary_circle_upper_bound g hg)
    have ho := h C.optimalCircleGap C.optimalCircleGap_admissible
    change C.optimalCircle.network.principalValue ≤ _ at ho
    rwa [C.optimalCircle_principalValue] at ho
  · intro he d hd
    rw [(C.circle_value_eq_iff_gaps g hg).mpr he]
    exact C.arbitrary_circle_upper_bound d hd

end TimeTraps.Spectral
