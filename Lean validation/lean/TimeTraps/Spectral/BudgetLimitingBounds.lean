module

public import TimeTraps.Spectral.DimensionlessBudget
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-! Exact finite-budget bounds preceding the spectral limiting statements. -/

namespace TimeTraps.Spectral

open Set

variable {n : ℕ}

theorem BudgetProblem.zeta_lt_tan (B : BudgetProblem n) :
    B.zeta < Real.tan B.zeta :=
  Real.lt_tan B.zeta_pos B.zeta_lt

theorem BudgetProblem.zeta_sq_lt_parameter (B : BudgetProblem n) :
    B.zeta ^ 2 < B.budget * B.length / (4 * B.diffusivity * (n : ℝ) ^ 2) := by
  rw [← B.zeta_equation, pow_two]
  exact mul_lt_mul_of_pos_left B.zeta_lt_tan B.zeta_pos

/-- The exact ratio to the constant-function trial bound in the manuscript. -/
theorem BudgetProblem.constant_trial_ratio (B : BudgetProblem n) :
    B.diffusivity * B.uniform.root ^ 2 =
      B.budget / B.length * (B.zeta / Real.tan B.zeta) := by
  rw [B.zeta_tan, BudgetProblem.zeta]
  field_simp [ne_of_gt B.budget_pos, ne_of_gt B.length_pos,
    ne_of_gt B.count_real_pos, ne_of_gt B.diffusivity_pos, ne_of_gt B.uniform.root_pos]

theorem BudgetProblem.value_lt_constant_trial (B : BudgetProblem n) :
    B.diffusivity * B.uniform.root ^ 2 < B.budget / B.length := by
  rw [B.constant_trial_ratio]
  have ht := Real.tan_pos_of_pos_of_lt_pi_div_two B.zeta_pos B.zeta_lt
  have hr : B.zeta / Real.tan B.zeta < 1 := (div_lt_one ht).mpr B.zeta_lt_tan
  simpa only [mul_one] using
    mul_lt_mul_of_pos_left hr (div_pos B.budget_pos B.length_pos)

theorem BudgetProblem.value_lt_absorbing_cells (B : BudgetProblem n) :
    B.diffusivity * B.uniform.root ^ 2 <
      B.diffusivity * Real.pi ^ 2 * (n : ℝ) ^ 2 / B.length ^ 2 := by
  rw [B.dimensionless_value]
  have hs : B.zeta ^ 2 < (Real.pi / 2) ^ 2 := by
    nlinarith [B.zeta_pos, B.zeta_lt, Real.pi_pos]
  have hc : 0 < 4 * B.diffusivity * (n : ℝ) ^ 2 / B.length ^ 2 :=
    div_pos (mul_pos (mul_pos (by norm_num) B.diffusivity_pos)
      (sq_pos_of_pos B.count_real_pos)) (sq_pos_of_pos B.length_pos)
  calc
    _ < (4 * B.diffusivity * (n : ℝ) ^ 2 / B.length ^ 2) * (Real.pi / 2) ^ 2 :=
      mul_lt_mul_of_pos_left hs hc
    _ = _ := by ring

theorem BudgetProblem.arbitrary_lt_constant_trial (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).Admissible x) :
    ((B.placement κ hκ).physical x hx).principalValue < B.budget / B.length :=
  (B.arbitrary_upper_bound κ hκ x hx).trans_lt B.value_lt_constant_trial

theorem BudgetProblem.arbitrary_lt_absorbing_cells (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).Admissible x) :
    ((B.placement κ hκ).physical x hx).principalValue <
      B.diffusivity * Real.pi ^ 2 * (n : ℝ) ^ 2 / B.length ^ 2 :=
  (B.arbitrary_upper_bound κ hκ x hx).trans_lt B.value_lt_absorbing_cells

end TimeTraps.Spectral
