module

public import TimeTraps.Probability.BrownianIntegralTimeContinuity
public import TimeTraps.Analysis.IntegralCauchySchwarz
public import Mathlib.MeasureTheory.Function.LpOrder

@[expose] public section

/-! Finite running maxima and the deterministic telescoping inequality
underlying the L² maximal estimate. No sample-path regularity is used. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

def finiteRunningMax (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => x 0
  | n + 1 => max (finiteRunningMax x n) (x (n + 1))

theorem finiteRunningMax_le_iff (x : ℕ → ℝ) (n : ℕ) (c : ℝ) :
    finiteRunningMax x n ≤ c ↔ ∀ k ≤ n, x k ≤ c := by
  induction n with
  | zero => simp [finiteRunningMax]
  | succ n ih =>
    rw [finiteRunningMax, max_le_iff, ih]
    constructor
    · rintro ⟨h, hn⟩ k hk
      rcases Nat.eq_or_lt_of_le hk with rfl | hk
      · exact hn
      · exact h k (Nat.le_of_lt_succ hk)
    · intro h
      exact ⟨fun k hk => h k (hk.trans (Nat.le_succ n)), h (n + 1) le_rfl⟩

theorem le_finiteRunningMax (x : ℕ → ℝ) {k n : ℕ} (hkn : k ≤ n) :
    x k ≤ finiteRunningMax x n :=
  (finiteRunningMax_le_iff x n _).mp le_rfl k hkn

theorem finiteRunningMax_nonneg (x : ℕ → ℝ) (hx : 0 ≤ x 0) (n : ℕ) :
    0 ≤ finiteRunningMax x n :=
  hx.trans (le_finiteRunningMax x (Nat.zero_le n))

theorem finiteRunningMax_eq_sup (x : ℕ → ℝ) (n : ℕ) :
    finiteRunningMax x n =
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one x := by
  apply le_antisymm
  · apply (finiteRunningMax_le_iff x n _).mpr
    intro k hk
    exact Finset.le_sup' x (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  · apply Finset.sup'_le
    intro k hk
    exact le_finiteRunningMax x (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

theorem finiteRunningMax_sq_le (x : ℕ → ℝ) (n : ℕ) :
    finiteRunningMax x n ^ 2 ≤ 2 * x n * finiteRunningMax x n -
      2 * ∑ k ∈ Finset.range n, finiteRunningMax x k * (x (k + 1) - x k) := by
  induction n with
  | zero =>
    simp only [finiteRunningMax, Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero]
    nlinarith [sq_nonneg (x 0)]
  | succ n ih =>
    rw [finiteRunningMax, Finset.sum_range_succ]
    by_cases h : finiteRunningMax x n ≤ x (n + 1)
    · rw [max_eq_right h]
      nlinarith [sq_nonneg (x (n + 1) - finiteRunningMax x n)]
    · rw [max_eq_left (le_of_not_ge h)]
      nlinarith

end TimeTraps.Probability
