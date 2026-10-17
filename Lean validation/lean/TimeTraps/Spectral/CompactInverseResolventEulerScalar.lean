module

public import TimeTraps.Spectral.CompactInverseResolvent
public import TimeTraps.Analysis.CompactSpectralSemigroup
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

@[expose] public section

/-! Exact scalar Euler convergence for nonnegative time. The rational
resolvent coefficient is rewritten as the reciprocal of `1+t/(n*μ)`;
the classical exponential limit applies analytically. Its difference
from the heat coefficient is uniformly bounded by one. -/

namespace TimeTraps.Analysis

open Filter
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem CompactPositiveInverse.resolvent_euler_coefficient_tendsto {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (t : ℝ≥0) (i : CompactSpectralIndex T) :
    Tendsto (fun n : ℕ => compactResolventCoefficient (t / (n : ℝ≥0)) i ^ n)
      atTop (𝓝 (compactHeatCoefficient t i)) := by
  have he (n : ℕ) : compactResolventCoefficient (t / (n : ℝ≥0)) i =
      (1 + ((t : ℝ) / i.1) / (n : ℝ))⁻¹ := by
    change i.1 / (i.1 + (t : ℝ) / (n : ℝ)) = _
    calc
      _ = ((i.1 + (t : ℝ) / (n : ℝ)) / i.1)⁻¹ := (inv_div _ _).symm
      _ = _ := by
        congr 1
        rw [add_div, div_self (h.eigenbasis_positive i).ne']
        ring
  have hl := (Real.tendsto_one_add_div_pow_exp ((t : ℝ) / i.1)).inv₀
    (Real.exp_ne_zero ((t : ℝ) / i.1))
  have hl' : Tendsto (fun n : ℕ => compactResolventCoefficient (t / (n : ℝ≥0)) i ^ n)
      atTop (𝓝 ((Real.exp ((t : ℝ) / i.1))⁻¹)) := by
    apply hl.congr
    intro n
    rw [he, inv_pow]
  simpa only [compactHeatCoefficient, neg_div, Real.exp_neg] using hl'

theorem CompactPositiveInverse.resolvent_euler_coefficient_bound {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (t : ℝ≥0) (n : ℕ) (i : CompactSpectralIndex T) :
    |compactResolventCoefficient (t / (n : ℝ≥0)) i ^ n - compactHeatCoefficient t i| ≤ 1 := by
  have hr₀ := pow_nonneg (h.resolventCoefficient_pos (t / (n : ℝ≥0)) i).le n
  have hr₁ : compactResolventCoefficient (t / (n : ℝ≥0)) i ^ n ≤ 1 :=
    pow_le_one₀ (h.resolventCoefficient_pos (t / (n : ℝ≥0)) i).le
      (h.resolventCoefficient_le_one (t / (n : ℝ≥0)) i)
  have hh₀ := (compactHeatCoefficient_pos t i).le
  have hh₁ := h.heatCoefficient_le_one t i
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end TimeTraps.Analysis
