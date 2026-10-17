module

public import TimeTraps.Probability.ReflectedRobinLifetimePlacementOptimization
public import TimeTraps.Spectral.RobinStrengthOptimality

@[expose] public section

/-! Strict Schur concavity and positive splitting for the attained
Robin lifetime-decay optimum. The objective is the limit of logarithms
of literal first-attainment survival probabilities, and the original
prescribed endpoint coefficients and admissible placements are retained. -/

namespace TimeTraps.Probability

open Set TimeTraps.Analysis TimeTraps.Spectral

variable {n : ℕ}

theorem reflectedRobinPlacement_decay_schur_le (C B : RobinPlacementProblem n)
    (hL : C.length = B.length) (hD : C.diffusivity = B.diffusivity)
    (hβ0 : C.betaLeft = B.betaLeft) (hβL : C.betaRight = B.betaRight)
    (h : Majorizes C.strength B.strength)
    {z : ℝ} (hz : z ∈ Icc 0 C.length) :
    reflectedRobinLifetimeDecayRate C.candidatePhysical z ≤
      reflectedRobinLifetimeDecayRate B.candidatePhysical z := by
  have hzB : z ∈ Icc 0 B.length := by simpa only [← hL] using hz
  rw [reflectedRobinLifetimeDecayRate_eq C.candidatePhysical hz,
    reflectedRobinLifetimeDecayRate_eq B.candidatePhysical hzB]
  exact C.schur_le B hL hD hβ0 hβL h

theorem reflectedRobinPlacement_decay_schur_lt (C B : RobinPlacementProblem n)
    (hL : C.length = B.length) (hD : C.diffusivity = B.diffusivity)
    (hβ0 : C.betaLeft = B.betaLeft) (hβL : C.betaRight = B.betaRight)
    (h : Majorizes C.strength B.strength)
    (hne : ¬ ∃ σ : Equiv.Perm (Fin n), C.strength = B.strength ∘ σ)
    {z : ℝ} (hz : z ∈ Icc 0 C.length) :
    reflectedRobinLifetimeDecayRate C.candidatePhysical z <
      reflectedRobinLifetimeDecayRate B.candidatePhysical z := by
  have hzB : z ∈ Icc 0 B.length := by simpa only [← hL] using hz
  rw [reflectedRobinLifetimeDecayRate_eq C.candidatePhysical hz,
    reflectedRobinLifetimeDecayRate_eq B.candidatePhysical hzB]
  exact C.schur_lt B hL hD hβ0 hβL h hne

theorem reflectedRobinPlacement_decay_schur_eq_iff (C B : RobinPlacementProblem n)
    (hL : C.length = B.length) (hD : C.diffusivity = B.diffusivity)
    (hβ0 : C.betaLeft = B.betaLeft) (hβL : C.betaRight = B.betaRight)
    (h : Majorizes C.strength B.strength)
    {z : ℝ} (hz : z ∈ Icc 0 C.length) :
    reflectedRobinLifetimeDecayRate C.candidatePhysical z =
      reflectedRobinLifetimeDecayRate B.candidatePhysical z ↔
        ∃ σ : Equiv.Perm (Fin n), C.strength = B.strength ∘ σ := by
  have hzB : z ∈ Icc 0 B.length := by simpa only [← hL] using hz
  rw [reflectedRobinLifetimeDecayRate_eq C.candidatePhysical hz,
    reflectedRobinLifetimeDecayRate_eq B.candidatePhysical hzB]
  exact C.schur_eq_iff B hL hD hβ0 hβL h

theorem reflectedRobinPlacement_decay_split_lt (C : RobinPlacementProblem n) (j : Fin n)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = C.strength j)
    {z : ℝ} (hz : z ∈ Icc 0 C.length) :
    reflectedRobinLifetimeDecayRate C.candidatePhysical z <
      reflectedRobinLifetimeDecayRate (C.split j a b ha hb).candidatePhysical z := by
  rw [reflectedRobinLifetimeDecayRate_eq C.candidatePhysical hz,
    reflectedRobinLifetimeDecayRate_eq (C.split j a b ha hb).candidatePhysical hz]
  exact C.split_optimal_value_lt j ha hb hab

end TimeTraps.Probability
