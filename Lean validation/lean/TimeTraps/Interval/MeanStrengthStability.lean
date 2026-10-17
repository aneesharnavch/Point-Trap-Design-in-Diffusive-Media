module

public import TimeTraps.Interval.CDFDeficit

@[expose] public section

/-!
The strength half of the global homogeneous mean-deficit stability estimate
on the unit interval. The constant is obtained by completing a square after
the exact strength/share loss bounds. There is no smallness, minimum-share,
or site-separation assumption. Physical mean identification is separate.
-/

namespace TimeTraps.Interval

open scoped BigOperators

variable {n : ℕ}

theorem meanStrengthLoss_square_bound {K : ℝ} (κ p : Fin n → ℝ)
    (hκ : ∀ i, 0 < κ i) (hs : ∑ i, κ i = K) :
    (∑ i, (p i - κ i / K) ^ 2) / K ≤ meanStrengthLoss K κ p := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  have hi : κ i ≤ K := by
    rw [← hs]
    exact Finset.single_le_sum (fun j _ => (hκ j).le) (Finset.mem_univ i)
  exact div_le_div_of_nonneg_left (sq_nonneg _) (hκ i) hi

theorem meanShareLoss_square_bound (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) :
    (2 / (n : ℝ)) * (∑ i, (p i - 1 / (n : ℝ)) ^ 2) ≤ meanShareLoss p := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_left (hp i) : 2 / (n : ℝ) ≤ p i + 2 / (n : ℝ))
    (sq_nonneg (p i - 1 / (n : ℝ)))
  simpa only [mul_comm] using h

theorem mean_two_square_bound {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (v w : ℝ) :
    (v - w) ^ 2 / (A + B) ≤ v ^ 2 / A + w ^ 2 / B := by
  apply (div_le_iff₀ (add_pos hA hB)).mpr
  have he : (v ^ 2 / A + w ^ 2 / B) * (A + B) - (v - w) ^ 2 =
      (B * v + A * w) ^ 2 / (A * B) := by
    field_simp [ne_of_gt hA, ne_of_gt hB]
    ring
  have hp := div_nonneg (sq_nonneg (B * v + A * w)) (mul_pos hA hB).le
  linarith

theorem meanStrengthShare_square_bound {D K : ℝ} (κ p : Fin n → ℝ)
    (hD : 0 < D) (hK : 0 < K) (hn : 0 < n)
    (hκ : ∀ i, 0 < κ i) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, κ i = K) :
    (∑ i, (κ i / K - 1 / (n : ℝ)) ^ 2) / (K + 6 * D * (n : ℝ)) ≤
      meanStrengthLoss K κ p + (1 / (12 * D)) * meanShareLoss p := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hB : 0 < 6 * D * (n : ℝ) := mul_pos (mul_pos (by norm_num) hD) hn'
  have hpair : (∑ i, (κ i / K - 1 / (n : ℝ)) ^ 2) / (K + 6 * D * (n : ℝ)) ≤
      (∑ i, (p i - κ i / K) ^ 2) / K +
        (∑ i, (p i - 1 / (n : ℝ)) ^ 2) / (6 * D * (n : ℝ)) := by
    rw [Finset.sum_div, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have h := mean_two_square_bound hK hB (p i - κ i / K) (p i - 1 / (n : ℝ))
    have he : ((p i - κ i / K) - (p i - 1 / (n : ℝ))) ^ 2 =
        (κ i / K - 1 / (n : ℝ)) ^ 2 := by ring
    rwa [he] at h
  have hco : 0 ≤ (1 : ℝ) / (12 * D) :=
    div_nonneg (by norm_num) (mul_pos (by norm_num) hD).le
  have hshare := mul_le_mul_of_nonneg_left (meanShareLoss_square_bound p hp) hco
  have hc : (1 / (12 * D)) * ((2 / (n : ℝ)) *
      (∑ i, (p i - 1 / (n : ℝ)) ^ 2)) =
        (∑ i, (p i - 1 / (n : ℝ)) ^ 2) / (6 * D * (n : ℝ)) := by
    field_simp [ne_of_gt hD, ne_of_gt hn']
    ring
  rw [hc] at hshare
  exact hpair.trans (add_le_add (meanStrengthLoss_square_bound κ p hκ hs) hshare)

theorem cdf_mean_normalized_strength_stability {D K : ℝ} (κ p x : Fin n → ℝ)
    (hD : 0 < D) (hK : 0 < K) (hn : 0 < n)
    (hκ : ∀ i, 0 < κ i) (hp : ∀ i, 0 < p i)
    (hs : ∑ i, κ i = K) (hm : ∑ i, p i = 1) :
    (∑ i, (κ i / K - 1 / (n : ℝ)) ^ 2) / (K + 6 * D * (n : ℝ)) ≤
      cdfMeanScore 1 D κ p x - (1 / K + 1 / (12 * D * (n : ℝ) ^ 2)) := by
  have he := cdf_mean_deficit_identity (L := 1) (D := D) κ p x hn (ne_of_gt hK)
    (fun i => ne_of_gt (hκ i)) hs hm
  simp only [one_pow, one_mul] at he
  have hpos := mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD.le)
    (meanPositionLoss_nonneg p x (fun i => (hp i).le))
  have hb := meanStrengthShare_square_bound κ p hD hK hn hκ (fun i => (hp i).le) hs
  linarith

theorem cdf_mean_strength_stability {D K : ℝ} (κ p x : Fin n → ℝ)
    (hD : 0 < D) (hK : 0 < K) (hn : 0 < n)
    (hκ : ∀ i, 0 < κ i) (hp : ∀ i, 0 < p i)
    (hs : ∑ i, κ i = K) (hm : ∑ i, p i = 1) :
    (∑ i, (κ i - K / (n : ℝ)) ^ 2) / (K ^ 2 * (6 * D * (n : ℝ) + K)) ≤
      cdfMeanScore 1 D κ p x - (1 / K + 1 / (12 * D * (n : ℝ) ^ 2)) := by
  have hn' : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  have hterm (i : Fin n) : (κ i / K - 1 / (n : ℝ)) ^ 2 =
      (κ i - K / (n : ℝ)) ^ 2 / K ^ 2 := by
    field_simp [ne_of_gt hK, hn']
  have hb := cdf_mean_normalized_strength_stability κ p x hD hK hn hκ hp hs hm
  simp_rw [hterm] at hb
  rw [← Finset.sum_div, div_div] at hb
  simpa only [add_comm] using hb

end TimeTraps.Interval
