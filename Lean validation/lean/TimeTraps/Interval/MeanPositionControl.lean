module

public import TimeTraps.Interval.MeanStrengthStability
public import TimeTraps.Interval.UniformPartition
public import TimeTraps.Interval.StrictPartition

@[expose] public section

/-! The unequal-share term supplies uniform position control even when an
individual absorption share is arbitrarily small. -/

namespace TimeTraps.Interval

open Set
open scoped BigOperators

variable {n : ℕ}

noncomputable def meanCellMidpoint (Q : StrictPartition n) (i : Fin n) : ℝ :=
  (Q.point i.castSucc + Q.point i.succ) / 2

noncomputable def meanGridMidpoint (i : Fin n) : ℝ := (2 * (i.val : ℝ) + 1) / (2 * (n : ℝ))

noncomputable def meanPrefixDeviation (Q : StrictPartition n) (e : Fin (n + 1)) : ℝ :=
  Q.point e - (e.val : ℝ) / n

theorem meanCellMidpoint_mem (Q : StrictPartition n) (i : Fin n) :
    meanCellMidpoint Q i ∈ Icc (0 : ℝ) 1 := by
  have hl := Q.point_mem i.castSucc
  have hr := Q.point_mem i.succ
  unfold meanCellMidpoint
  constructor <;> linarith [hl.1, hl.2, hr.1, hr.2]

theorem mean_position_error_sq_le_one (Q : StrictPartition n) {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) (i : Fin n) :
    (x i - meanCellMidpoint Q i) ^ 2 ≤ 1 := by
  have hm := meanCellMidpoint_mem Q i
  have hi := hx i
  have hl : -1 ≤ x i - meanCellMidpoint Q i := by linarith [hi.1, hm.2]
  have hr : x i - meanCellMidpoint Q i ≤ 1 := by linarith [hi.2, hm.1]
  nlinarith [mul_nonneg (sub_nonneg.mpr hr)
    (show 0 ≤ x i - meanCellMidpoint Q i + 1 by linarith)]

theorem meanPositionLoss_width (Q : StrictPartition n) (x : Fin n → ℝ) :
    meanPositionLoss Q.width x = ∑ i, Q.width i * (x i - meanCellMidpoint Q i) ^ 2 := by
  unfold meanPositionLoss meanCellMidpoint
  simp_rw [Q.prefix_width]

theorem bounded_error_square_control {c β a p e : ℝ}
    (hβ : 0 ≤ β) (hp : 0 ≤ p) (he : e ^ 2 ≤ 1) (hc : 2 * β * a ≤ c) :
    β * a ^ 2 * e ^ 2 ≤ c * p * e ^ 2 + β * (p - a) ^ 2 := by
  have hbr : 0 ≤ c + β * (p - 2 * a) := by nlinarith [mul_nonneg hβ hp]
  have h1 := mul_nonneg (mul_nonneg hβ (sub_nonneg.mpr he)) (sq_nonneg (p - a))
  have h2 := mul_nonneg (mul_nonneg hp (sq_nonneg e)) hbr
  have hid : c * p * e ^ 2 + β * (p - a) ^ 2 - β * a ^ 2 * e ^ 2 =
      β * (1 - e ^ 2) * (p - a) ^ 2 + p * e ^ 2 * (c + β * (p - 2 * a)) := by ring
  linarith

theorem mean_position_term_control {D p e : ℝ} (hD : 0 < D) (hn : 0 < n)
    (hp : 0 ≤ p) (he : e ^ 2 ≤ 1) :
    e ^ 2 / (6 * D * (n : ℝ) ^ 3) ≤
      p * e ^ 2 / D + (p - 1 / (n : ℝ)) ^ 2 / (6 * D * (n : ℝ)) := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < 3 * D * (n : ℝ) ^ 2 := mul_pos (mul_pos (by norm_num) hD) (sq_pos_of_pos hn')
  have hc : 2 * (1 / (6 * D * (n : ℝ))) * (1 / (n : ℝ)) ≤ 1 / D := by
    rw [show 2 * (1 / (6 * D * (n : ℝ))) * (1 / (n : ℝ)) =
      1 / (3 * D * (n : ℝ) ^ 2) by field_simp; ring]
    apply (div_le_div_iff₀ hden hD).mpr
    have hnn : 0 ≤ 3 * (n : ℝ) ^ 2 - 1 := by nlinarith
    nlinarith [mul_nonneg hD.le hnn]
  have hb := bounded_error_square_control
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      (mul_pos (mul_pos (by norm_num) hD) hn').le) hp he hc
  convert hb using 1 <;> field_simp [ne_of_gt hD, ne_of_gt hn']

theorem mean_position_share_control {D : ℝ} (Q : StrictPartition n) (x : Fin n → ℝ)
    (hD : 0 < D) (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
    (∑ i, (x i - meanCellMidpoint Q i) ^ 2) / (6 * D * (n : ℝ) ^ 3) ≤
      (1 / D) * meanPositionLoss Q.width x + (1 / (12 * D)) * meanShareLoss Q.width := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr Q.size_pos
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => mean_position_term_control hD Q.size_pos (Q.width_pos i).le
      (mean_position_error_sq_le_one Q hx i))
  have hs := mul_le_mul_of_nonneg_left
    (meanShareLoss_square_bound Q.width (fun i => (Q.width_pos i).le))
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (mul_pos (show (0 : ℝ) < 12 by norm_num) hD).le)
  have hc : (1 / (12 * D)) * ((2 / (n : ℝ)) *
      (∑ i, (Q.width i - 1 / (n : ℝ)) ^ 2)) =
      (∑ i, (Q.width i - 1 / (n : ℝ)) ^ 2) / (6 * D * (n : ℝ)) := by ring
  rw [hc] at hs
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div] at hsum
  rw [meanPositionLoss_width]
  calc
    _ ≤ (∑ i, Q.width i * (x i - meanCellMidpoint Q i) ^ 2) / D +
        (1 / (12 * D)) * meanShareLoss Q.width := hsum.trans (add_le_add le_rfl hs)
    _ = _ := by ring

theorem cdf_mean_position_error_control {D K : ℝ} (κ x : Fin n → ℝ)
    (Q : StrictPartition n) (hD : 0 < D) (hK : 0 < K)
    (hκ : ∀ i, 0 < κ i) (hs : ∑ i, κ i = K) (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
    (∑ i, (x i - meanCellMidpoint Q i) ^ 2) ≤ 6 * D * (n : ℝ) ^ 3 *
      (cdfMeanScore 1 D κ Q.width x - (1 / K + 1 / (12 * D * (n : ℝ) ^ 2))) := by
  have hd := cdf_mean_deficit_identity (L := 1) (D := D) κ Q.width x Q.size_pos
    (ne_of_gt hK) (fun i => ne_of_gt (hκ i)) hs Q.width_sum
  simp only [one_pow, one_mul] at hd
  have he := mean_position_share_control Q x hD hx
  have hn := meanStrengthLoss_nonneg K κ Q.width hκ
  have hden : 0 < 6 * D * (n : ℝ) ^ 3 :=
    mul_pos (mul_pos (by norm_num) hD) (pow_pos (Nat.cast_pos.mpr Q.size_pos) _)
  have hbound : (∑ i, (x i - meanCellMidpoint Q i) ^ 2) / (6 * D * (n : ℝ) ^ 3) ≤
      cdfMeanScore 1 D κ Q.width x - (1 / K + 1 / (12 * D * (n : ℝ) ^ 2)) := by linarith
  simpa only [mul_comm] using (div_le_iff₀ hden).mp hbound

end TimeTraps.Interval
