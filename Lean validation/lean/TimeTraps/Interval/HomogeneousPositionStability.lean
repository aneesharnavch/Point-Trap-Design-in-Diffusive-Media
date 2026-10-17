module

public import TimeTraps.Interval.MeanPositionStability
public import TimeTraps.Interval.HomogeneousStrengthStability

@[expose] public section

/-! The global position and combined strength/position certificates for the
independently defined physical mean on [0,1]. All cell shares come from the
actual weak solution. -/

namespace TimeTraps.Interval

open Set TimeTraps.Analysis
open scoped BigOperators

variable {n : ℕ} {D K : ℝ}

theorem homogeneous_mean_position_stability (hD : 0 < D) (hK : 0 < K)
    (E : IntervalDesign (homogeneous 1 D zero_lt_one hD) n K) :
    (∑ i, (E.geometry.site i - meanGridMidpoint i) ^ 2) /
      (6 * D * (n : ℝ) * ((n : ℝ) + Real.sqrt (discreteDirichletConstant n)) ^ 2) ≤
      E.meanCost - (1 / K + 1 / (12 * D * (n : ℝ) ^ 2)) := by
  have hx (i : Fin n) : E.geometry.site i ∈ Icc (0 : ℝ) 1 := by
    have hi := E.geometry.site_interior i
    rw [E.homogeneous_source] at hi
    exact ⟨hi.1.le, hi.2.le⟩
  rw [E.homogeneous_meanCost_eq_score]
  simpa only [div_one] using
    cdf_mean_position_stability E.strength E.geometry.site E.partition hD hK
      E.strength_pos E.strength_sum hx

theorem homogeneous_mean_combined_stability {θ : ℝ} (hD : 0 < D) (hK : 0 < K)
    (E : IntervalDesign (homogeneous 1 D zero_lt_one hD) n K) (hθ : θ ∈ Icc (0 : ℝ) 1) :
    θ * ((∑ i, (E.geometry.site i - meanGridMidpoint i) ^ 2) /
      (6 * D * (n : ℝ) * ((n : ℝ) + Real.sqrt (discreteDirichletConstant n)) ^ 2)) +
    (1 - θ) * ((∑ i, (E.strength i - K / (n : ℝ)) ^ 2) /
      (K ^ 2 * (6 * D * (n : ℝ) + K))) ≤
      E.meanCost - (1 / K + 1 / (12 * D * (n : ℝ) ^ 2)) := by
  have hp := mul_le_mul_of_nonneg_left (homogeneous_mean_position_stability hD hK E) hθ.1
  have hs := mul_le_mul_of_nonneg_left (homogeneous_mean_strength_stability hD hK E)
    (sub_nonneg.mpr hθ.2)
  linarith

end TimeTraps.Interval
