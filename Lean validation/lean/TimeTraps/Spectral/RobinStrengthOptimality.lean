module

public import TimeTraps.Spectral.RobinStrengthMajorization
public import TimeTraps.Spectral.RobinStrengthSplitting
public import TimeTraps.Spectral.RobinPlacementUniqueness

@[expose] public section

/-! Robin strict Schur concavity and positive splitting for the attained
physical principal-value maximum over all admissible placements. -/

namespace TimeTraps.Spectral

open TimeTraps.Analysis

variable {n : ℕ}

theorem RobinPlacementProblem.schur_le (C B : RobinPlacementProblem n)
    (hL : C.length = B.length) (hD : C.diffusivity = B.diffusivity)
    (hβ0 : C.betaLeft = B.betaLeft) (hβL : C.betaRight = B.betaRight)
    (h : Majorizes C.strength B.strength) :
    C.candidatePhysical.principalValue ≤ B.candidatePhysical.principalValue := by
  rw [C.candidate_principalValue, B.candidate_principalValue, hD]
  have hs : C.root ^ 2 ≤ B.root ^ 2 := by
    nlinarith [C.root_le_of_majorizes B hL hD hβ0 hβL h, C.root_pos, B.root_pos]
  exact mul_le_mul_of_nonneg_left hs B.diffusivity_pos.le

theorem RobinPlacementProblem.schur_lt (C B : RobinPlacementProblem n)
    (hL : C.length = B.length) (hD : C.diffusivity = B.diffusivity)
    (hβ0 : C.betaLeft = B.betaLeft) (hβL : C.betaRight = B.betaRight)
    (h : Majorizes C.strength B.strength)
    (hne : ¬ ∃ σ : Equiv.Perm (Fin n), C.strength = B.strength ∘ σ) :
    C.candidatePhysical.principalValue < B.candidatePhysical.principalValue := by
  rw [C.candidate_principalValue, B.candidate_principalValue, hD]
  have hs : C.root ^ 2 < B.root ^ 2 := by
    nlinarith [C.root_lt_of_majorizes B hL hD hβ0 hβL h hne, C.root_pos, B.root_pos]
  exact mul_lt_mul_of_pos_left hs B.diffusivity_pos

theorem RobinPlacementProblem.schur_eq_iff (C B : RobinPlacementProblem n)
    (hL : C.length = B.length) (hD : C.diffusivity = B.diffusivity)
    (hβ0 : C.betaLeft = B.betaLeft) (hβL : C.betaRight = B.betaRight)
    (h : Majorizes C.strength B.strength) :
    C.candidatePhysical.principalValue = B.candidatePhysical.principalValue ↔
      ∃ σ : Equiv.Perm (Fin n), C.strength = B.strength ∘ σ := by
  constructor
  · intro he
    by_contra hne
    exact (C.schur_lt B hL hD hβ0 hβL h hne).ne he
  · intro hp
    rw [C.candidate_principalValue, B.candidate_principalValue, hD,
      C.root_eq_of_strength_permutation B hL hD hβ0 hβL hp]

theorem RobinPlacementProblem.split_optimal_value_lt (C : RobinPlacementProblem n) (j : Fin n)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = C.strength j) :
    C.candidatePhysical.principalValue < (C.split j a b ha hb).candidatePhysical.principalValue := by
  rw [C.candidate_principalValue, (C.split j a b ha hb).candidate_principalValue]
  change C.diffusivity * C.root ^ 2 < C.diffusivity * (C.split j a b ha hb).root ^ 2
  apply mul_lt_mul_of_pos_left _ C.diffusivity_pos
  nlinarith [C.split_root_lt j ha hb hab, C.root_pos, (C.split j a b ha hb).root_pos]

end TimeTraps.Spectral
