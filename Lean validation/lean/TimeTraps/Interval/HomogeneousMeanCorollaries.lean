module

public import TimeTraps.Interval.HomogeneousMeanDeficit
public import TimeTraps.Interval.HomogeneousCDF
public import TimeTraps.Analysis.DiscreteDirichletPoincare

@[expose] public section

/-!
The explicit small-count checks in expanded chapter 02, lines 1658–1800.
The general optimizer and its quadratic profile are already proved; here
the physical one- and two-trap deficits and the displayed CDF and discrete
constant evaluations are reduced exactly, without numerical approximation.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {D K : ℝ} {hD : 0 < D}

theorem homogeneous_one_trap_deficit (hK : 0 < K)
    (E : IntervalDesign (homogeneous 1 D zero_lt_one hD) 1 K) :
    E.meanCost - (1 / K + 1 / (12 * D)) =
      (E.geometry.site 0 - 1 / 2) ^ 2 / D := by
  have hs : E.strength 0 = K := by simpa only [Fin.sum_univ_one] using E.strength_sum
  have hp : E.partition.width 0 = 1 := by
    simpa only [Fin.sum_univ_one] using E.partition.width_sum
  have he := homogeneous_mean_deficit hK E
  simp [meanStrengthLoss, meanPositionLoss, meanShareLoss, absorptionPrefix,
    hs, hp, ne_of_gt hK] at he
  convert he using 1 <;> ring

theorem homogeneous_two_trap_deficit (hK : 0 < K)
    (E : IntervalDesign (homogeneous 1 D zero_lt_one hD) 2 K) :
    E.meanCost - (1 / K + 1 / (48 * D)) =
      (E.partition.width 0 - E.strength 0 / K) ^ 2 *
        (1 / E.strength 0 + 1 / (K - E.strength 0)) +
      (1 / D) * (E.partition.width 0 * (E.geometry.site 0 - E.partition.width 0 / 2) ^ 2 +
        (1 - E.partition.width 0) * (E.geometry.site 1 - (1 + E.partition.width 0) / 2) ^ 2) +
      (1 / (4 * D)) * (E.partition.width 0 - 1 / 2) ^ 2 := by
  have hs : E.strength 0 + E.strength 1 = K := by
    simpa only [Fin.sum_univ_two] using E.strength_sum
  have hp : E.partition.width 0 + E.partition.width 1 = 1 := by
    simpa only [Fin.sum_univ_two] using E.partition.width_sum
  have hs1 : E.strength 1 = K - E.strength 0 := by linarith
  have hp1 : E.partition.width 1 = 1 - E.partition.width 0 := by linarith
  have he := homogeneous_mean_deficit hK E
  simp [meanStrengthLoss, meanPositionLoss, meanShareLoss, absorptionPrefix,
    Fin.sum_univ_two, hs1, hp1] at he
  have hm : 1 - E.partition.width 0 - (K - E.strength 0) / K =
      -(E.partition.width 0 - E.strength 0 / K) := by
    field_simp [ne_of_gt hK]
    ring
  rw [hm] at he
  convert he using 1 <;> ring

theorem homogeneous_two_trap_cdf
    (E : IntervalDesign (homogeneous 1 D zero_lt_one hD) 2 K) (z : ℝ) :
    E.geometry.absorptionCDF E.partition.width z =
      if E.geometry.site 1 ≤ z then 1
      else if E.geometry.site 0 ≤ z then E.partition.width 0 else 0 := by
  have hp : E.partition.width 0 + E.partition.width 1 = 1 := by
    simpa only [Fin.sum_univ_two] using E.partition.width_sum
  rw [E.homogeneous_absorptionCDF]
  simp only [Fin.sum_univ_two, div_one]
  by_cases h1 : E.geometry.site 1 ≤ z
  · have h0 : E.geometry.site 0 ≤ z :=
      (E.geometry.site_strictMono (by decide : (0 : Fin 2) < 1)).le.trans h1
    simp only [h1, h0, if_pos, hp]
  · simp [h1]

theorem centered_two_trap_cdf_integral :
    (∫ x in (0 : ℝ)..(1 / 4 : ℝ), x ^ 2) +
      (∫ x in (1 / 4 : ℝ)..(3 / 4 : ℝ), (1 / 2 - x) ^ 2) +
      (∫ x in (3 / 4 : ℝ)..1, (1 - x) ^ 2) = 1 / 48 := by
  have h0 := cdf_square_gap_integral 0 0 (1 / 4)
  have h1 := cdf_square_gap_integral (1 / 2) (1 / 4) (3 / 4)
  have h2 := cdf_square_gap_integral 1 (3 / 4) 1
  simp only [zero_sub, neg_sq] at h0
  rw [h0, h1, h2]
  norm_num

theorem mean_dirichlet_constant_two : discreteDirichletConstant 2 = 1 / 2 := by
  rw [discreteDirichletConstant_eq (by norm_num : 2 ≤ 2)]
  norm_num [Real.sin_pi_div_four, div_pow]

end TimeTraps.Interval
