module

public import TimeTraps.Analysis.CompactSpectralSemigroupSmoothing

@[expose] public section

/-! The quantitative positive-time regularization bound for the actual
unbounded inverse operator, obtained by Parseval and the scalar exponential
estimate. Every initial Hilbert vector is allowed. -/

namespace TimeTraps.Analysis

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem CompactPositiveInverse.inverse_heat_norm_sq_le {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (t : ℝ≥0) (ht : 0 < t) (x : E) :
    ‖inverseOperator T h.injective
      ⟨h.heatSemigroup t x, h.heatSemigroup_mem_domain_of_pos t ht x⟩‖ ^ 2 ≤
      (1 / (t : ℝ)) ^ 2 * ‖x‖ ^ 2 :=
  hasSum_le (h.heat_reciprocal_square_bound t ht x)
    (h.hasSum_inverse_norm ⟨_, h.heatSemigroup_mem_domain_of_pos t ht x⟩)
    ((h.hasSum_parseval x).mul_left ((1 / (t : ℝ)) ^ 2))

theorem CompactPositiveInverse.inverse_heat_norm_le {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (t : ℝ≥0) (ht : 0 < t) (x : E) :
    ‖inverseOperator T h.injective
      ⟨h.heatSemigroup t x, h.heatSemigroup_mem_domain_of_pos t ht x⟩‖ ≤
      ‖x‖ / (t : ℝ) := by
  have hb := h.inverse_heat_norm_sq_le t ht x
  have ht' : 0 < (t : ℝ) := ht
  have he : (1 / (t : ℝ)) ^ 2 * ‖x‖ ^ 2 = (‖x‖ / (t : ℝ)) ^ 2 := by ring
  rw [he] at hb
  nlinarith [norm_nonneg (inverseOperator T h.injective
    ⟨h.heatSemigroup t x, h.heatSemigroup_mem_domain_of_pos t ht x⟩),
    div_nonneg (norm_nonneg x) ht'.le]

end TimeTraps.Analysis
