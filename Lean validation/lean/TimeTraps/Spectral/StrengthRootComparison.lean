module

public import TimeTraps.Spectral.PlacementUniqueness

@[expose] public section

/-! Exact comparison of optimized roots from phase-capacity inequalities.
The two problems may have different numbers of independently placed traps. -/

namespace TimeTraps.Spectral

open scoped BigOperators

variable {n m : ℕ}

theorem PlacementProblem.le_root_of_phase_bound (C : PlacementProblem n) {k : ℝ} (hk : 0 < k)
    (hbound : C.length * k ≤ 2 * ∑ i, Real.arctan (C.strength i / (2 * C.diffusivity * k))) :
    k ≤ C.root := by
  apply le_capacity_root Finset.univ ⟨⟨0, C.count_pos⟩, Finset.mem_univ _⟩
    (fun i => C.strength i / (2 * C.diffusivity))
    (fun i _ => div_pos (C.strength_pos i) (mul_pos (by norm_num) C.diffusivity_pos))
    C.length_pos hk C.root_pos
  · simpa only [phaseCapacity, div_div, ← Finset.mul_sum] using C.root_equation
  · simpa only [phaseCapacity, div_div, ← Finset.mul_sum] using hbound

theorem PlacementProblem.lt_root_of_phase_bound (C : PlacementProblem n) {k : ℝ} (hk : 0 < k)
    (hbound : C.length * k < 2 * ∑ i, Real.arctan (C.strength i / (2 * C.diffusivity * k))) :
    k < C.root := by
  apply lt_of_le_of_ne (C.le_root_of_phase_bound hk hbound.le)
  intro he
  rw [he, C.root_equation] at hbound
  exact (lt_irrefl _) hbound

theorem PlacementProblem.root_le_of_phase_sum_le (C : PlacementProblem n) (B : PlacementProblem m)
    (hL : C.length = B.length)
    (hphase : ∀ k, 0 < k →
      (∑ i, Real.arctan (C.strength i / (2 * C.diffusivity * k))) ≤
        ∑ i, Real.arctan (B.strength i / (2 * B.diffusivity * k))) : C.root ≤ B.root := by
  apply B.le_root_of_phase_bound C.root_pos
  rw [← hL, C.root_equation]
  exact mul_le_mul_of_nonneg_left (hphase C.root C.root_pos) (by norm_num)

theorem PlacementProblem.root_lt_of_phase_sum_lt (C : PlacementProblem n) (B : PlacementProblem m)
    (hL : C.length = B.length)
    (hphase : ∀ k, 0 < k →
      (∑ i, Real.arctan (C.strength i / (2 * C.diffusivity * k))) <
        ∑ i, Real.arctan (B.strength i / (2 * B.diffusivity * k))) : C.root < B.root := by
  apply B.lt_root_of_phase_bound C.root_pos
  rw [← hL, C.root_equation]
  exact mul_lt_mul_of_pos_left (hphase C.root C.root_pos) (by norm_num)

end TimeTraps.Spectral
