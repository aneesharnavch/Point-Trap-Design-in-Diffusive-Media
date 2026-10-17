module

public import TimeTraps.Interval.CDFSquare
public import TimeTraps.Analysis.CubicMoment

@[expose] public section

/-!
Exact finite deficit behind the homogeneous stationary-average optimum.
The physical weak-state identification is supplied separately. Here the
shares have total one and the strengths have the prescribed total budget.
-/

namespace TimeTraps.Interval

open TimeTraps.Analysis
open scoped BigOperators

variable {n : ℕ}

noncomputable def meanStrengthLoss (K : ℝ) (κ p : Fin n → ℝ) : ℝ :=
  ∑ i, (p i - κ i / K) ^ 2 / κ i

noncomputable def meanPositionLoss (p x : Fin n → ℝ) : ℝ :=
  ∑ i, p i * (x i - (absorptionPrefix p i.castSucc + absorptionPrefix p i.succ) / 2) ^ 2

noncomputable def meanShareLoss (p : Fin n → ℝ) : ℝ :=
  ∑ i, (p i - 1 / (n : ℝ)) ^ 2 * (p i + 2 / (n : ℝ))

noncomputable def cdfMeanScore (L D : ℝ) (κ p x : Fin n → ℝ) : ℝ :=
  L * (∑ i, p i ^ 2 / κ i) + (L ^ 2 / D) * cdfSquareScore p x

theorem meanStrengthLoss_identity {K : ℝ} (κ p : Fin n → ℝ)
    (hK : K ≠ 0) (hκ : ∀ i, κ i ≠ 0) (hs : ∑ i, κ i = K) (hp : ∑ i, p i = 1) :
    meanStrengthLoss K κ p = (∑ i, p i ^ 2 / κ i) - 1 / K := by
  have he (i : Fin n) : (p i - κ i / K) ^ 2 / κ i =
      p i ^ 2 / κ i - (2 / K) * p i + (1 / K ^ 2) * κ i := by
    field_simp [hK, hκ i]
    ring
  unfold meanStrengthLoss
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, hs, hp]
  field_simp [hK]
  ring

theorem meanShareLoss_identity (p : Fin n → ℝ) (hn : 0 < n) (hp : ∑ i, p i = 1) :
    meanShareLoss p = (∑ i, p i ^ 3) - 1 / (n : ℝ) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  have hs : (∑ i : Fin n, (1 : ℝ)) = n := by simp
  have hm : (∑ i : Fin n, 1 * p i) = 1 := by simpa using hp
  have he := weighted_cubic_identity Finset.univ (fun _ : Fin n => (1 : ℝ)) p hn' hs hm
  simpa only [meanShareLoss, one_mul, one_pow, mul_one, show 2 * (1 / (n : ℝ)) = 2 / (n : ℝ) by ring]
    using he

theorem cdf_mean_deficit_identity {L D K : ℝ} (κ p x : Fin n → ℝ)
    (hn : 0 < n) (hK : K ≠ 0) (hκ : ∀ i, κ i ≠ 0)
    (hs : ∑ i, κ i = K) (hp : ∑ i, p i = 1) :
    cdfMeanScore L D κ p x - (L / K + L ^ 2 / (12 * D * (n : ℝ) ^ 2)) =
      L * meanStrengthLoss K κ p + (L ^ 2 / D) * meanPositionLoss p x +
        (L ^ 2 / (12 * D)) * meanShareLoss p := by
  rw [cdfMeanScore, cdfSquareScore_identity p x hp, meanStrengthLoss_identity κ p hK hκ hs hp,
    meanShareLoss_identity p hn hp]
  unfold meanPositionLoss
  rw [Finset.sum_add_distrib, ← Finset.sum_div]
  ring

theorem meanStrengthLoss_nonneg (K : ℝ) (κ p : Fin n → ℝ) (hκ : ∀ i, 0 < κ i) :
    0 ≤ meanStrengthLoss K κ p :=
  Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (hκ i).le)

theorem meanPositionLoss_nonneg (p x : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) :
    0 ≤ meanPositionLoss p x :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (sq_nonneg _))

theorem meanShareLoss_nonneg (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) :
    0 ≤ meanShareLoss p :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _)
    (add_nonneg (hp i) (div_nonneg (by norm_num) (Nat.cast_nonneg n))))

theorem cdf_mean_lower_bound {L D K : ℝ} (κ p x : Fin n → ℝ)
    (hL : 0 < L) (hD : 0 < D) (hK : 0 < K) (hn : 0 < n)
    (hκ : ∀ i, 0 < κ i) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, κ i = K) (hm : ∑ i, p i = 1) :
    L / K + L ^ 2 / (12 * D * (n : ℝ) ^ 2) ≤ cdfMeanScore L D κ p x := by
  have he := cdf_mean_deficit_identity (L := L) (D := D) κ p x hn (ne_of_gt hK)
    (fun i => ne_of_gt (hκ i)) hs hm
  have h1 := mul_nonneg hL.le (meanStrengthLoss_nonneg K κ p hκ)
  have h2 := mul_nonneg (div_nonneg (sq_nonneg L) hD.le) (meanPositionLoss_nonneg p x hp)
  have h3 := mul_nonneg (div_nonneg (sq_nonneg L) (mul_pos (show (0 : ℝ) < 12 by norm_num) hD).le)
    (meanShareLoss_nonneg p hp)
  linarith

theorem meanStrengthLoss_eq_zero_iff (K : ℝ) (κ p : Fin n → ℝ) (hκ : ∀ i, 0 < κ i) :
    meanStrengthLoss K κ p = 0 ↔ ∀ i, p i = κ i / K := by
  rw [meanStrengthLoss, Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => div_nonneg (sq_nonneg _) (hκ i).le)]
  simp only [Finset.mem_univ, forall_true_left, div_eq_zero_iff, ne_of_gt (hκ _), or_false,
    sq_eq_zero_iff, sub_eq_zero]

theorem meanPositionLoss_eq_zero_iff (p x : Fin n → ℝ) (hp : ∀ i, 0 < p i) :
    meanPositionLoss p x = 0 ↔ ∀ i,
      x i = (absorptionPrefix p i.castSucc + absorptionPrefix p i.succ) / 2 := by
  rw [meanPositionLoss, Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => mul_nonneg (hp i).le (sq_nonneg _))]
  simp only [Finset.mem_univ, forall_true_left, mul_eq_zero, ne_of_gt (hp _), false_or,
    sq_eq_zero_iff, sub_eq_zero]

theorem meanShareLoss_eq_zero_iff (p : Fin n → ℝ) (hn : 0 < n) (hp : ∀ i, 0 ≤ p i) :
    meanShareLoss p = 0 ↔ ∀ i, p i = 1 / (n : ℝ) := by
  have hpos (i : Fin n) : 0 < p i + 2 / (n : ℝ) :=
    add_pos_of_nonneg_of_pos (hp i) (div_pos (by norm_num) (Nat.cast_pos.mpr hn))
  rw [meanShareLoss, Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => mul_nonneg (sq_nonneg _) (hpos i).le)]
  simp only [Finset.mem_univ, forall_true_left, mul_eq_zero, ne_of_gt (hpos _), or_false,
    sq_eq_zero_iff, sub_eq_zero]

end TimeTraps.Interval
