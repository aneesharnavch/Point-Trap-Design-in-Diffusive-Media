module

public import TimeTraps.Spectral.RobinPlacementProblem

@[expose] public section

/-! Scalar root comparison with fixed Robin endpoint terms. Counts may differ;
the length, diffusivity and both physical endpoint coefficients are fixed. -/

namespace TimeTraps.Spectral

open scoped BigOperators

variable {n m : ℕ}

theorem RobinPlacementProblem.le_root_of_phase_bound (C : RobinPlacementProblem n)
    {k : ℝ} (hk : 0 < k)
    (hbound : C.length * k ≤ Real.arctan (C.betaLeft / (C.diffusivity * k)) +
      Real.arctan (C.betaRight / (C.diffusivity * k)) +
        2 * ∑ i, Real.arctan (C.strength i / (2 * C.diffusivity * k))) : k ≤ C.root := by
  apply le_robin_capacity_root Finset.univ ⟨⟨0, C.count_pos⟩, Finset.mem_univ _⟩
    (fun i => C.strength i / (2 * C.diffusivity))
    (fun i _ => div_pos (C.strength_pos i) (mul_pos (by norm_num) C.diffusivity_pos))
    (div_nonneg C.betaLeft_nonneg C.diffusivity_pos.le)
    (div_nonneg C.betaRight_nonneg C.diffusivity_pos.le) C.length_pos hk C.root_pos
  · simpa only [robinPhaseCapacity, phaseCapacity, div_div, ← Finset.mul_sum] using C.root_equation
  · simpa only [robinPhaseCapacity, phaseCapacity, div_div, ← Finset.mul_sum] using hbound

theorem RobinPlacementProblem.lt_root_of_phase_bound (C : RobinPlacementProblem n)
    {k : ℝ} (hk : 0 < k)
    (hbound : C.length * k < Real.arctan (C.betaLeft / (C.diffusivity * k)) +
      Real.arctan (C.betaRight / (C.diffusivity * k)) +
        2 * ∑ i, Real.arctan (C.strength i / (2 * C.diffusivity * k))) : k < C.root := by
  apply lt_of_le_of_ne (C.le_root_of_phase_bound hk hbound.le)
  intro he
  rw [he, C.root_equation] at hbound
  exact (lt_irrefl _) hbound

theorem RobinPlacementProblem.root_le_of_phase_sum_le (C : RobinPlacementProblem n)
    (B : RobinPlacementProblem m) (hL : C.length = B.length)
    (hD : C.diffusivity = B.diffusivity)
    (hβ0 : C.betaLeft = B.betaLeft) (hβL : C.betaRight = B.betaRight)
    (hphase : ∀ k, 0 < k →
      (∑ i, Real.arctan (C.strength i / (2 * C.diffusivity * k))) ≤
        ∑ i, Real.arctan (B.strength i / (2 * B.diffusivity * k))) : C.root ≤ B.root := by
  apply B.le_root_of_phase_bound C.root_pos
  rw [← hL, C.root_equation, hD, hβ0, hβL]
  have hp := hphase C.root C.root_pos
  rw [hD] at hp
  linarith

theorem RobinPlacementProblem.root_lt_of_phase_sum_lt (C : RobinPlacementProblem n)
    (B : RobinPlacementProblem m) (hL : C.length = B.length)
    (hD : C.diffusivity = B.diffusivity)
    (hβ0 : C.betaLeft = B.betaLeft) (hβL : C.betaRight = B.betaRight)
    (hphase : ∀ k, 0 < k →
      (∑ i, Real.arctan (C.strength i / (2 * C.diffusivity * k))) <
        ∑ i, Real.arctan (B.strength i / (2 * B.diffusivity * k))) : C.root < B.root := by
  apply B.lt_root_of_phase_bound C.root_pos
  rw [← hL, C.root_equation, hD, hβ0, hβL]
  have hp := hphase C.root C.root_pos
  rw [hD] at hp
  linarith

end TimeTraps.Spectral
