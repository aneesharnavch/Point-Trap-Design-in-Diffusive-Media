module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Tactic

@[expose] public section

/-! Deterministic second-order Taylor estimates used in the analytical
stochastic change-of-variable proof. No stochastic identity is assumed. -/

namespace TimeTraps.Analysis

open Set
open scoped ContDiff

noncomputable def itoTaylorRemainder (F : ℝ → ℝ) (x y : ℝ) : ℝ :=
  F y - F x - deriv F x * (y - x) - deriv (deriv F) x * (y - x) ^ 2 / 2

theorem itoTaylorRemainder_self (F : ℝ → ℝ) (x : ℝ) :
    itoTaylorRemainder F x x = 0 := by
  simp [itoTaylorRemainder]

theorem itoTaylor_polynomial_two {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    {x y : ℝ} (hxy : x ≠ y) :
    taylorWithinEval F 2 (uIcc x y) x y =
      F x + deriv F x * (y - x) + deriv (deriv F) x * (y - x) ^ 2 / 2 := by
  have h₁ := iteratedDerivWithin_eq_iteratedDeriv (n := 1)
    (uniqueDiffOn_uIcc hxy) (hF.of_le (by norm_num : (1 : ℕ∞ω) ≤ 3)).contDiffAt left_mem_uIcc
  have h₂ := iteratedDerivWithin_eq_iteratedDeriv (n := 2)
    (uniqueDiffOn_uIcc hxy) (hF.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)).contDiffAt left_mem_uIcc
  norm_num [taylorWithinEval_succ, taylor_within_zero_eval, h₁, h₂,
    iteratedDeriv_succ, iteratedDeriv_zero, smul_eq_mul]
  ring

theorem itoTaylorRemainder_lagrange {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    {x y : ℝ} (hxy : x ≠ y) :
    ∃ z ∈ uIoo x y,
      itoTaylorRemainder F x y = iteratedDeriv 3 F z * (y - x) ^ 3 / 6 := by
  obtain ⟨z, hz, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hxy
    hF.contDiffOn
  refine ⟨z, hz, ?_⟩
  rw [itoTaylor_polynomial_two hF hxy] at he
  norm_num at he
  unfold itoTaylorRemainder
  linarith

theorem itoTaylorRemainder_abs_le {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    {M : ℝ} (hb : ∀ z, |iteratedDeriv 3 F z| ≤ M) (x y : ℝ) :
    |itoTaylorRemainder F x y| ≤ M * |y - x| ^ 3 / 6 := by
  by_cases hxy : x = y
  · subst y
    simp [itoTaylorRemainder_self]
  · obtain ⟨z, _, he⟩ := itoTaylorRemainder_lagrange hF hxy
    rw [he, abs_div, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hb z) (pow_nonneg (abs_nonneg _) _)) (by norm_num)

end TimeTraps.Analysis
