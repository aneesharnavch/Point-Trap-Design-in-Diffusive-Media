module

public import TimeTraps.Analysis.ItoTaylorRemainder
public import Mathlib.Topology.UniformSpace.HeineCantor

@[expose] public section

/-! The second-order Taylor remainder for a C2 function is uniformly
small relative to the squared increment on each compact spatial interval.
No third derivative or global modulus of continuity is assumed. -/

namespace TimeTraps.Analysis

open Set
open scoped ContDiff

theorem itoC2_secondDerivative_continuous {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) :
    Continuous (deriv (deriv F)) := by
  have h₁ : ContDiff ℝ 1 (deriv F) := hF.deriv'
  have h₂ : ContDiff ℝ 0 (deriv (deriv F)) := h₁.deriv'
  exact h₂.continuous

theorem itoC2_polynomial_one {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    {x y : ℝ} (hxy : x ≠ y) :
    taylorWithinEval F 1 (uIcc x y) x y = F x + deriv F x * (y - x) := by
  have h₁ := iteratedDerivWithin_eq_iteratedDeriv (n := 1)
    (uniqueDiffOn_uIcc hxy) (hF.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).contDiffAt left_mem_uIcc
  norm_num [taylorWithinEval_succ, taylor_within_zero_eval, h₁,
    iteratedDeriv_succ, iteratedDeriv_zero, smul_eq_mul]
  ring

theorem itoTaylorRemainder_c2_lagrange {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    {x y : ℝ} (hxy : x ≠ y) :
    ∃ z ∈ uIoo x y, itoTaylorRemainder F x y =
      (deriv (deriv F) z - deriv (deriv F) x) * (y - x) ^ 2 / 2 := by
  obtain ⟨z, hz, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hxy hF.contDiffOn
  refine ⟨z, hz, ?_⟩
  rw [itoC2_polynomial_one hF hxy] at he
  norm_num [iteratedDeriv_succ, iteratedDeriv_zero] at he
  unfold itoTaylorRemainder
  linarith

theorem itoTaylorRemainder_c2_compact {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (l r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ Icc l r, ∀ y ∈ Icc l r, |y - x| < δ →
      |itoTaylorRemainder F x y| ≤ ε * (y - x) ^ 2 := by
  have huc : UniformContinuousOn (deriv (deriv F)) (Icc l r) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (itoC2_secondDerivative_continuous hF).continuousOn
  obtain ⟨δ, hδ, hc⟩ := Metric.uniformContinuousOn_iff.mp huc (2 * ε) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy
  by_cases heq : x = y
  · subst y
    simp [itoTaylorRemainder_self]
  obtain ⟨z, hz, he⟩ := itoTaylorRemainder_c2_lagrange hF heq
  have hz' : z ∈ Icc l r := by
    rcases le_total x y with h | h
    · rw [uIoo_of_le h] at hz
      exact ⟨hx.1.trans hz.1.le, hz.2.le.trans hy.2⟩
    · rw [uIoo_of_ge h] at hz
      exact ⟨hy.1.trans hz.1.le, hz.2.le.trans hx.2⟩
  have hdist : dist z x < δ := by
    rw [Real.dist_eq]
    rcases le_total x y with h | h
    · rw [uIoo_of_le h] at hz
      rw [abs_of_nonneg (sub_nonneg.mpr h)] at hxy
      rw [abs_of_nonneg (sub_nonneg.mpr hz.1.le)]
      linarith [hz.2]
    · rw [uIoo_of_ge h] at hz
      rw [abs_of_nonpos (sub_nonpos.mpr h)] at hxy
      rw [abs_of_nonpos (sub_nonpos.mpr hz.2.le)]
      linarith [hz.1]
  have hb : |deriv (deriv F) z - deriv (deriv F) x| ≤ 2 * ε :=
    (hc z hz' x hx hdist).le
  rw [he, abs_div, abs_mul, abs_of_nonneg (sq_nonneg (y - x)), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith [mul_le_mul_of_nonneg_right hb (sq_nonneg (y - x))]

end TimeTraps.Analysis
