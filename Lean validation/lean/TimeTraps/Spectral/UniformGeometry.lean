module

public import TimeTraps.Spectral.BudgetProblem

@[expose] public section

/-! Equal strengths give equal cells and the physical midpoint site vector. -/

namespace TimeTraps.Spectral

open scoped BigOperators

variable {n : ℕ}

theorem BudgetProblem.uniform_cellLength (B : BudgetProblem n) (i : Fin n) :
    B.uniform.cellLength i = B.length / n := by
  have he : ∀ j, B.uniform.cellLength j = B.uniform.cellLength i := fun _ => rfl
  have hs := B.uniform.cellLength_sum
  change (∑ j, B.uniform.cellLength j) = B.length at hs
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  apply (eq_div_iff (ne_of_gt B.count_real_pos)).mpr
  linarith

theorem BudgetProblem.uniform_boundary (B : BudgetProblem n) (e : Fin (n + 1)) :
    B.uniform.boundary e = e.val * B.length / n := by
  induction e using Fin.induction with
  | zero => simpa using B.uniform.boundary_zero
  | succ i hi =>
    rw [B.uniform.boundary_succ, hi, B.uniform_cellLength]
    simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    ring

theorem BudgetProblem.uniform_site (B : BudgetProblem n) (i : Fin n) :
    B.uniform.optimalSite i = (2 * (i.val : ℝ) + 1) * B.length / (2 * n) := by
  rw [PlacementProblem.optimalSite, B.uniform_boundary, B.uniform_cellLength]
  simp only [Fin.val_castSucc]
  ring

end TimeTraps.Spectral
