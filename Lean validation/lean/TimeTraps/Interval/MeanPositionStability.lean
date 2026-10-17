module

public import TimeTraps.Interval.MeanMidpointGeometry
public import TimeTraps.Analysis.DiscreteDirichletPoincare
public import TimeTraps.Analysis.EuclideanSquare

@[expose] public section

/-! Global position stability of the homogeneous mean score on the unit
interval. The cumulative-share displacement has zero boundary values, so
the sharp discrete Dirichlet constant controls its midpoint displacement.
No lower bound on an individual share is assumed. -/

namespace TimeTraps.Interval

open scoped BigOperators
open Set TimeTraps.Analysis

variable {n : ℕ}

theorem mean_midpoint_poincare (Q : StrictPartition n) :
    (∑ i, (meanCellMidpoint Q i - meanGridMidpoint i) ^ 2) ≤
      discreteDirichletConstant n * ∑ i, (Q.width i - 1 / (n : ℝ)) ^ 2 := by
  have hp := discrete_dirichlet_poincare Q.size_pos (meanPrefixDeviation Q)
    (meanPrefixDeviation_first Q) (meanPrefixDeviation_last Q)
  simp_rw [meanPrefixDeviation_difference] at hp
  exact (mean_midpoint_drift_bound Q).trans hp

theorem cdf_mean_midpoint_error_control {D K : ℝ} (κ x : Fin n → ℝ)
    (Q : StrictPartition n) (hD : 0 < D) (hK : 0 < K)
    (hκ : ∀ i, 0 < κ i) (hs : ∑ i, κ i = K) :
    (∑ i, (meanCellMidpoint Q i - meanGridMidpoint i) ^ 2) ≤
      (6 * D * (n : ℝ) *
        (cdfMeanScore 1 D κ Q.width x - (1 / K + 1 / (12 * D * (n : ℝ) ^ 2)))) *
          discreteDirichletConstant n := by
  have hb := mul_le_mul_of_nonneg_left
    (cdf_mean_share_error_control κ x Q hD hK hκ hs)
    (discreteDirichletConstant_nonneg n)
  exact (mean_midpoint_poincare Q).trans (by simpa only [mul_comm] using hb)

theorem cdf_mean_grid_error_control {D K : ℝ} (κ x : Fin n → ℝ)
    (Q : StrictPartition n) (hD : 0 < D) (hK : 0 < K)
    (hκ : ∀ i, 0 < κ i) (hs : ∑ i, κ i = K) (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
    (∑ i, (x i - meanGridMidpoint i) ^ 2) ≤
      (6 * D * (n : ℝ) *
        (cdfMeanScore 1 D κ Q.width x - (1 / K + 1 / (12 * D * (n : ℝ) ^ 2)))) *
          ((n : ℝ) + Real.sqrt (discreteDirichletConstant n)) ^ 2 := by
  let Δ := cdfMeanScore 1 D κ Q.width x - (1 / K + 1 / (12 * D * (n : ℝ) ^ 2))
  have hΔ : 0 ≤ Δ := by
    have hl := cdf_mean_lower_bound (L := 1) κ Q.width x zero_lt_one hD hK Q.size_pos
      hκ (fun i => (Q.width_pos i).le) hs Q.width_sum
    simp only [one_pow] at hl
    exact sub_nonneg.mpr hl
  have he : (∑ i, (x i - meanCellMidpoint Q i) ^ 2) ≤
      (6 * D * (n : ℝ) * Δ) * (n : ℝ) ^ 2 := by
    convert cdf_mean_position_error_control κ x Q hD hK hκ hs hx using 1
    dsimp [Δ]
    ring
  have hb := finite_sum_add_sq_control Finset.univ
    (fun i => x i - meanCellMidpoint Q i)
    (fun i => meanCellMidpoint Q i - meanGridMidpoint i)
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hD.le)
      (Nat.cast_nonneg n)) hΔ) (Nat.cast_nonneg n) he
    (cdf_mean_midpoint_error_control κ x Q hD hK hκ hs)
  simpa only [sub_add_sub_cancel] using hb

theorem cdf_mean_position_stability {D K : ℝ} (κ x : Fin n → ℝ)
    (Q : StrictPartition n) (hD : 0 < D) (hK : 0 < K)
    (hκ : ∀ i, 0 < κ i) (hs : ∑ i, κ i = K) (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
    (∑ i, (x i - meanGridMidpoint i) ^ 2) /
      (6 * D * (n : ℝ) * ((n : ℝ) + Real.sqrt (discreteDirichletConstant n)) ^ 2) ≤
      cdfMeanScore 1 D κ Q.width x - (1 / K + 1 / (12 * D * (n : ℝ) ^ 2)) := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr Q.size_pos
  have hden : 0 < 6 * D * (n : ℝ) *
      ((n : ℝ) + Real.sqrt (discreteDirichletConstant n)) ^ 2 :=
    mul_pos (mul_pos (mul_pos (by norm_num) hD) hn)
      (sq_pos_of_pos (add_pos_of_pos_of_nonneg hn (Real.sqrt_nonneg _)))
  apply (div_le_iff₀ hden).mpr
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    cdf_mean_grid_error_control κ x Q hD hK hκ hs hx

theorem cdf_mean_combined_stability {D K θ : ℝ} (κ x : Fin n → ℝ)
    (Q : StrictPartition n) (hD : 0 < D) (hK : 0 < K)
    (hκ : ∀ i, 0 < κ i) (hs : ∑ i, κ i = K) (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1)
    (hθ : θ ∈ Icc (0 : ℝ) 1) :
    θ * ((∑ i, (x i - meanGridMidpoint i) ^ 2) /
      (6 * D * (n : ℝ) * ((n : ℝ) + Real.sqrt (discreteDirichletConstant n)) ^ 2)) +
    (1 - θ) * ((∑ i, (κ i - K / (n : ℝ)) ^ 2) / (K ^ 2 * (6 * D * (n : ℝ) + K))) ≤
      cdfMeanScore 1 D κ Q.width x - (1 / K + 1 / (12 * D * (n : ℝ) ^ 2)) := by
  have hxbound := mul_le_mul_of_nonneg_left
    (cdf_mean_position_stability κ x Q hD hK hκ hs hx) hθ.1
  have hκbound := mul_le_mul_of_nonneg_left
    (cdf_mean_strength_stability κ Q.width x hD hK Q.size_pos hκ Q.width_pos hs Q.width_sum)
    (sub_nonneg.mpr hθ.2)
  linarith

end TimeTraps.Interval
