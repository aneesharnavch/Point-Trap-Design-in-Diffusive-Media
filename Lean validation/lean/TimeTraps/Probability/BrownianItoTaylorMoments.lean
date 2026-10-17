module

public import TimeTraps.Analysis.IntegralThirdMoment
public import TimeTraps.Analysis.ItoTaylorRemainder
public import TimeTraps.Probability.BrownianQuadraticVariationMoments

@[expose] public section

/-! Analytic third absolute moment bounds for Brownian increments.
These control the cubic Taylor remainder without computing sample paths. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory TimeTraps.Analysis
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownian_increment_abs_cube_integrable (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    Integrable (fun ω => |B t ω - B s ω| ^ 3) P :=
  memLp_integrable_abs_cube (brownian_increment_memLp hB s t 2 (by norm_num))
    (brownian_increment_square_memLp hB s t)

theorem brownian_increment_abs_cube_sq_le (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    (∫ ω, |B t ω - B s ω| ^ 3 ∂P) ^ 2 ≤ 3 * |t.val - s.val| ^ 3 := by
  have h := memLp_integral_abs_cube_sq_le (brownian_increment_memLp hB s t 2 (by norm_num))
    (brownian_increment_square_memLp hB s t)
  rw [brownian_increment_second_moment hB, brownian_increment_fourth_moment hB] at h
  exact h.trans_eq (by ring)

theorem brownian_increment_abs_cube_le (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    (∫ ω, |B t ω - B s ω| ^ 3 ∂P) ≤
      Real.sqrt 3 * |t.val - s.val| * Real.sqrt |t.val - s.val| := by
  have h := Real.le_sqrt_of_sq_le (brownian_increment_abs_cube_sq_le hB s t)
  calc
    _ ≤ Real.sqrt (3 * |t.val - s.val| ^ 3) := h
    _ = Real.sqrt (3 * (|t.val - s.val| ^ 2 * |t.val - s.val|)) := by rw [pow_succ]
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq_eq_abs, abs_abs]
      ring

end TimeTraps.Probability
