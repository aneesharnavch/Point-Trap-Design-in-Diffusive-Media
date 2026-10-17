module

public import TimeTraps.Spectral.RobinStrengthComparison
public import TimeTraps.Spectral.StrengthMajorization

@[expose] public section

/-! The strict Robin majorization comparison, with common nonnegative endpoint
coefficients. Majorization keeps its standard descending-prefix definition. -/

namespace TimeTraps.Spectral

open TimeTraps.Analysis

variable {n : ℕ}

theorem RobinPlacementProblem.root_le_of_majorizes (C B : RobinPlacementProblem n)
    (hL : C.length = B.length) (hD : C.diffusivity = B.diffusivity)
    (hβ0 : C.betaLeft = B.betaLeft) (hβL : C.betaRight = B.betaRight)
    (h : Majorizes C.strength B.strength) : C.root ≤ B.root := by
  apply C.root_le_of_phase_sum_le B hL hD hβ0 hβL
  intro k hk
  rw [hD]
  exact scaledArctan_sum_le_of_majorizes h
    (mul_pos (mul_pos (by norm_num) B.diffusivity_pos) hk) C.strength_pos B.strength_pos

theorem RobinPlacementProblem.root_lt_of_majorizes (C B : RobinPlacementProblem n)
    (hL : C.length = B.length) (hD : C.diffusivity = B.diffusivity)
    (hβ0 : C.betaLeft = B.betaLeft) (hβL : C.betaRight = B.betaRight)
    (h : Majorizes C.strength B.strength)
    (hne : ¬ ∃ σ : Equiv.Perm (Fin n), C.strength = B.strength ∘ σ) : C.root < B.root := by
  apply C.root_lt_of_phase_sum_lt B hL hD hβ0 hβL
  intro k hk
  rw [hD]
  exact scaledArctan_sum_lt_of_majorizes h
    (mul_pos (mul_pos (by norm_num) B.diffusivity_pos) hk) C.strength_pos B.strength_pos hne

theorem RobinPlacementProblem.root_eq_of_strength_permutation (C B : RobinPlacementProblem n)
    (hL : C.length = B.length) (hD : C.diffusivity = B.diffusivity)
    (hβ0 : C.betaLeft = B.betaLeft) (hβL : C.betaRight = B.betaRight)
    (h : ∃ σ : Equiv.Perm (Fin n), C.strength = B.strength ∘ σ) : C.root = B.root := by
  have hs := (descending_eq_iff_permuted C.strength B.strength).mpr h
  apply le_antisymm (C.root_le_of_majorizes B hL hD hβ0 hβL (Majorizes.of_permuted h))
  exact B.root_le_of_majorizes C hL.symm hD.symm hβ0.symm hβL.symm
    (Majorizes.of_permuted ((descending_eq_iff_permuted B.strength C.strength).mp hs.symm))

theorem RobinPlacementProblem.root_eq_iff_of_majorizes (C B : RobinPlacementProblem n)
    (hL : C.length = B.length) (hD : C.diffusivity = B.diffusivity)
    (hβ0 : C.betaLeft = B.betaLeft) (hβL : C.betaRight = B.betaRight)
    (h : Majorizes C.strength B.strength) :
    C.root = B.root ↔ ∃ σ : Equiv.Perm (Fin n), C.strength = B.strength ∘ σ := by
  constructor
  · intro he
    by_contra hne
    exact (C.root_lt_of_majorizes B hL hD hβ0 hβL h hne).ne he
  · exact C.root_eq_of_strength_permutation B hL hD hβ0 hβL

end TimeTraps.Spectral
