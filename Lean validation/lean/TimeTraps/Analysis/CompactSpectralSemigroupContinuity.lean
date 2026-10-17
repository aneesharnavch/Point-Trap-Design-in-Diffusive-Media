module

public import TimeTraps.Analysis.CompactSpectralSemigroup
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-! Strong continuity of the actual spectral heat operators.  Parseval turns
the squared norm difference into a scalar series, dominated by the summable
squares of the initial coefficients.  This requires no operator-norm
continuity and no finiteness assumption on the basis. -/

namespace TimeTraps.Analysis

open Filter
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem CompactPositiveInverse.heatCoefficient_difference_bound {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s t : ℝ≥0) (i : CompactSpectralIndex T) :
    |compactHeatCoefficient t i - compactHeatCoefficient s i| ≤ 1 := by
  have hs₀ := (compactHeatCoefficient_pos s i).le
  have ht₀ := (compactHeatCoefficient_pos t i).le
  have hs₁ := h.heatCoefficient_le_one s i
  have ht₁ := h.heatCoefficient_le_one t i
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem CompactPositiveInverse.heatSemigroup_difference_sq {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s t : ℝ≥0) (x : E) :
    ‖h.heatSemigroup t x - h.heatSemigroup s x‖ ^ 2 =
      ∑' i : CompactSpectralIndex T,
        ((compactHeatCoefficient t i - compactHeatCoefficient s i) *
          inner ℝ (h.eigenbasis i) x) ^ 2 := by
  rw [← h.parseval (h.heatSemigroup t x - h.heatSemigroup s x)]
  apply tsum_congr
  intro i
  rw [inner_sub_right, h.heatSemigroup_inner, h.heatSemigroup_inner, sub_mul]

theorem CompactPositiveInverse.heatSemigroup_strong_continuous {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : E) :
    Continuous (fun t : ℝ≥0 => h.heatSemigroup t x) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hp : ∀ i : CompactSpectralIndex T,
      Tendsto (fun t : ℝ≥0 =>
        ((compactHeatCoefficient t i - compactHeatCoefficient s i) *
          inner ℝ (h.eigenbasis i) x) ^ 2) (𝓝 s) (𝓝 (0 : ℝ)) := by
    intro i
    simpa only [sub_self, zero_mul, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] using
      ((((compactHeatCoefficient_continuous i).tendsto s).sub_const
        (compactHeatCoefficient s i)).mul_const (inner ℝ (h.eigenbasis i) x)).pow 2
  have hb : ∀ t : ℝ≥0, ∀ i : CompactSpectralIndex T,
      ‖((compactHeatCoefficient t i - compactHeatCoefficient s i) *
        inner ℝ (h.eigenbasis i) x) ^ 2‖ ≤ (inner ℝ (h.eigenbasis i) x) ^ 2 := by
    intro t i
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
    have hd := h.heatCoefficient_difference_bound s t i
    have hd₂ : (compactHeatCoefficient t i - compactHeatCoefficient s i) ^ 2 ≤ 1 := by
      have hp₀ := mul_nonneg (sub_nonneg.mpr hd)
        (show 0 ≤ 1 + |compactHeatCoefficient t i - compactHeatCoefficient s i| by positivity)
      nlinarith [sq_abs (compactHeatCoefficient t i - compactHeatCoefficient s i)]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hd₂ (sq_nonneg (inner ℝ (h.eigenbasis i) x))
  have hd := tendsto_tsum_of_dominated_convergence (h.hasSum_parseval x).summable hp
    (Eventually.of_forall hb)
  have hn : Tendsto (fun t : ℝ≥0 => ‖h.heatSemigroup t x - h.heatSemigroup s x‖ ^ 2)
      (𝓝 s) (𝓝 (0 : ℝ)) := by
    simpa only [← h.heatSemigroup_difference_sq, tsum_zero] using hd
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hn
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero] using hsqrt

theorem CompactPositiveInverse.heatSemigroup_tendsto_zero {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : E) :
    Tendsto (fun t : ℝ≥0 => h.heatSemigroup t x) (𝓝 0) (𝓝 x) := by
  simpa only [h.heatSemigroup_zero, ContinuousLinearMap.id_apply] using
    (h.heatSemigroup_strong_continuous x).tendsto 0

end TimeTraps.Analysis
