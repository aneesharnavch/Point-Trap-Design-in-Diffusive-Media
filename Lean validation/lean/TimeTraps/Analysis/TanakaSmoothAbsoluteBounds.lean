module

public import TimeTraps.Analysis.TanakaSmoothAbsoluteDerivatives

@[expose] public section

/-! Global derivative bounds and nonnegative curvature for the
smooth absolute value, with the smoothing scale explicit. -/

namespace TimeTraps.Analysis

theorem tanakaSmoothAbs_first_bound {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    |deriv (tanakaSmoothAbs ε) x| ≤ 1 := by
  rw [tanakaSmoothAbs_deriv hε, abs_div, abs_of_pos (tanakaSmoothAbs_pos hε x)]
  exact (div_le_one (tanakaSmoothAbs_pos hε x)).2 (abs_le_tanakaSmoothAbs ε x)

theorem tanakaSmoothAbs_second_nonneg {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    0 ≤ deriv (deriv (tanakaSmoothAbs ε)) x := by
  rw [tanakaSmoothAbs_second_deriv hε]
  exact div_nonneg (sq_nonneg ε) (pow_nonneg (tanakaSmoothAbs_pos hε x).le 3)

theorem tanakaSmoothAbs_second_bound {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    |deriv (deriv (tanakaSmoothAbs ε)) x| ≤ 1 / ε := by
  rw [abs_of_nonneg (tanakaSmoothAbs_second_nonneg hε x), tanakaSmoothAbs_second_deriv hε]
  apply (div_le_div_iff₀ (pow_pos (tanakaSmoothAbs_pos hε x) 3) hε).2
  nlinarith [pow_le_pow_left₀ hε.le (epsilon_le_tanakaSmoothAbs hε.le x) 3]

theorem tanakaSmoothAbs_third_bound {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    |iteratedDeriv 3 (tanakaSmoothAbs ε) x| ≤ 3 / ε ^ 2 := by
  have hs := tanakaSmoothAbs_pos hε x
  have hn := ne_of_gt hs
  have he := epsilon_le_tanakaSmoothAbs hε.le x
  calc
    _ = 3 * ε ^ 2 * |x| / tanakaSmoothAbs ε x ^ 5 := by
      rw [tanakaSmoothAbs_third_deriv hε]
      simp [abs_div, abs_mul, abs_of_pos hε, abs_of_pos hs]
    _ ≤ 3 * ε ^ 2 * tanakaSmoothAbs ε x / tanakaSmoothAbs ε x ^ 5 := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hs.le 5)
      exact mul_le_mul_of_nonneg_left (abs_le_tanakaSmoothAbs ε x) (by positivity)
    _ = 3 * ε ^ 2 / tanakaSmoothAbs ε x ^ 4 := by
      field_simp
    _ ≤ 3 * ε ^ 2 / ε ^ 4 := by
      exact div_le_div_of_nonneg_left (by positivity) (pow_pos hε 4)
        (pow_le_pow_left₀ hε.le he 4)
    _ = 3 / ε ^ 2 := by
      field_simp

end TimeTraps.Analysis
