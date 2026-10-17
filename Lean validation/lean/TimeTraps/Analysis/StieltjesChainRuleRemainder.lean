module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Tactic

@[expose] public section

/-! A compact first-order remainder estimate for a C1 function. It
controls Stieltjes telescoping errors by the total monotone increment,
without a second derivative or absolute continuity of the integrator. -/

namespace TimeTraps.Analysis

open Set
open scoped ContDiff

theorem stieltjesChainRule_derivative_continuous {F : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) : Continuous (deriv F) := by
  have hd : ContDiff ℝ 0 (deriv F) := hF.deriv'
  exact hd.continuous

theorem stieltjesChainRule_remainder_lagrange {F : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) {x y : ℝ} (hxy : x ≠ y) :
    ∃ z ∈ uIoo x y,
      F y - F x - deriv F x * (y - x) = (deriv F z - deriv F x) * (y - x) := by
  obtain ⟨z, hz, he⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 0) hxy hF.contDiffOn
  refine ⟨z, hz, ?_⟩
  norm_num [taylor_within_zero_eval, iteratedDeriv_succ, iteratedDeriv_zero] at he
  linear_combination he

theorem stieltjesChainRule_remainder_compact {F : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) (l r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ Icc l r, ∀ y ∈ Icc l r, x ≤ y → y - x < δ →
      |F y - F x - deriv F x * (y - x)| ≤ ε * (y - x) := by
  have hu : UniformContinuousOn (deriv F) (Icc l r) :=
    isCompact_Icc.uniformContinuousOn_of_continuous
      (stieltjesChainRule_derivative_continuous hF).continuousOn
  obtain ⟨δ, hδ, hc⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy hsmall
  by_cases heq : x = y
  · subst y
    simp
  obtain ⟨z, hz, he⟩ := stieltjesChainRule_remainder_lagrange hF heq
  rw [uIoo_of_le hxy] at hz
  have hz' : z ∈ Icc l r := ⟨hx.1.trans hz.1.le, hz.2.le.trans hy.2⟩
  have hd : dist z x < δ := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hz.1.le)]
    linarith [hz.2]
  have hb : |deriv F z - deriv F x| ≤ ε := (hc z hz' x hx hd).le
  rw [he, abs_mul, abs_of_nonneg (sub_nonneg.mpr hxy)]
  exact mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr hxy)

end TimeTraps.Analysis
