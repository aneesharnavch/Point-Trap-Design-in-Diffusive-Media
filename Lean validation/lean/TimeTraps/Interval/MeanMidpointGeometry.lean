module

public import TimeTraps.Interval.MeanPositionControl

@[expose] public section

/-! Exact cumulative-share geometry for the position-stability estimate. -/

namespace TimeTraps.Interval

open scoped BigOperators

variable {n : ℕ}

theorem meanPrefixDeviation_first (Q : StrictPartition n) : meanPrefixDeviation Q 0 = 0 := by
  simp [meanPrefixDeviation, Q.first]

theorem meanPrefixDeviation_last (Q : StrictPartition n) :
    meanPrefixDeviation Q (Fin.last n) = 0 := by
  simp [meanPrefixDeviation, Q.last, ne_of_gt (Nat.cast_pos.mpr Q.size_pos : (0 : ℝ) < n)]

theorem meanPrefixDeviation_difference (Q : StrictPartition n) (i : Fin n) :
    meanPrefixDeviation Q i.succ - meanPrefixDeviation Q i.castSucc = Q.width i - 1 / (n : ℝ) := by
  unfold meanPrefixDeviation StrictPartition.width
  simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

theorem mean_midpoint_decomposition (Q : StrictPartition n) (i : Fin n) :
    meanCellMidpoint Q i - meanGridMidpoint i =
      (meanPrefixDeviation Q i.castSucc + meanPrefixDeviation Q i.succ) / 2 := by
  unfold meanCellMidpoint meanGridMidpoint meanPrefixDeviation
  simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

theorem finite_midpoint_square_bound (s : Fin (n + 1) → ℝ)
    (h0 : s 0 = 0) (hlast : s (Fin.last n) = 0) :
    (∑ i : Fin n, ((s i.castSucc + s i.succ) / 2) ^ 2) ≤ ∑ e, s e ^ 2 := by
  have hb : (∑ i : Fin n, ((s i.castSucc + s i.succ) / 2) ^ 2) ≤
      ∑ i : Fin n, (s i.castSucc ^ 2 + s i.succ ^ 2) / 2 := by
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg (s i.castSucc - s i.succ)]
  have ha := Fin.sum_univ_castSucc (fun e => s e ^ 2)
  have hc := Fin.sum_univ_succ (fun e => s e ^ 2)
  rw [hlast, zero_pow (by decide : 2 ≠ 0), add_zero] at ha
  rw [h0, zero_pow (by decide : 2 ≠ 0), zero_add] at hc
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← ha, ← hc] at hb
  linarith

theorem mean_midpoint_drift_bound (Q : StrictPartition n) :
    (∑ i, (meanCellMidpoint Q i - meanGridMidpoint i) ^ 2) ≤
      ∑ e, meanPrefixDeviation Q e ^ 2 := by
  simp_rw [mean_midpoint_decomposition]
  exact finite_midpoint_square_bound _ (meanPrefixDeviation_first Q) (meanPrefixDeviation_last Q)

theorem cdf_mean_share_error_control {D K : ℝ} (κ x : Fin n → ℝ)
    (Q : StrictPartition n) (hD : 0 < D) (hK : 0 < K)
    (hκ : ∀ i, 0 < κ i) (hs : ∑ i, κ i = K) :
    (∑ i, (Q.width i - 1 / (n : ℝ)) ^ 2) ≤ 6 * D * (n : ℝ) *
      (cdfMeanScore 1 D κ Q.width x - (1 / K + 1 / (12 * D * (n : ℝ) ^ 2))) := by
  have hd := cdf_mean_deficit_identity (L := 1) (D := D) κ Q.width x Q.size_pos
    (ne_of_gt hK) (fun i => ne_of_gt (hκ i)) hs Q.width_sum
  simp only [one_pow, one_mul] at hd
  have hsquare := mul_le_mul_of_nonneg_left
    (meanShareLoss_square_bound Q.width (fun i => (Q.width_pos i).le))
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (mul_pos (show (0 : ℝ) < 12 by norm_num) hD).le)
  have hc : (1 / (12 * D)) * ((2 / (n : ℝ)) *
      (∑ i, (Q.width i - 1 / (n : ℝ)) ^ 2)) =
      (∑ i, (Q.width i - 1 / (n : ℝ)) ^ 2) / (6 * D * (n : ℝ)) := by ring
  rw [hc] at hsquare
  have h1 := meanStrengthLoss_nonneg K κ Q.width hκ
  have h2 := mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD.le)
    (meanPositionLoss_nonneg Q.width x (fun i => (Q.width_pos i).le))
  have hden : 0 < 6 * D * (n : ℝ) :=
    mul_pos (mul_pos (by norm_num) hD) (Nat.cast_pos.mpr Q.size_pos)
  have hb : (∑ i, (Q.width i - 1 / (n : ℝ)) ^ 2) / (6 * D * (n : ℝ)) ≤
      cdfMeanScore 1 D κ Q.width x - (1 / K + 1 / (12 * D * (n : ℝ) ^ 2)) := by linarith
  simpa only [mul_comm] using (div_le_iff₀ hden).mp hb

end TimeTraps.Interval
