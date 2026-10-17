module

public import TimeTraps.Interval.HomogeneousMeanEnergy
public import TimeTraps.Interval.CDFDeficit

@[expose] public section

/-!
The exact three-part deficit for the Lebesgue mean of every homogeneous
physical weak design. The objective is defined from its actual state, and
all absorption shares are derived from that same weak solution.
-/

namespace TimeTraps.Interval

open Set MeasureTheory
open scoped BigOperators

variable {n : ℕ} {K : ℝ}

/-- The actual Lebesgue mean; no optimizing formula defines this objective. -/
noncomputable def IntervalDesign.meanCost {A : IntervalMedium}
    (E : IntervalDesign A n K) : ℝ :=
  (∫ x in A.source.left..A.source.right, E.state x) / (A.source.right - A.source.left)

variable {L D : ℝ} {hL : 0 < L} {hD : 0 < D}

theorem IntervalDesign.homogeneous_meanCost
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    E.meanCost = (∫ x in (0 : ℝ)..L, E.state x) / L := by
  simp only [meanCost, homogeneous, sub_zero]

theorem IntervalDesign.homogeneous_meanCost_eq_score
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    E.meanCost = cdfMeanScore L D E.strength E.partition.width
      (fun i => E.geometry.site i / L) := by
  rw [E.homogeneous_meanCost]
  exact homogeneous_mean_energy E

theorem homogeneous_mean_deficit (hK : 0 < K)
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    E.meanCost - (L / K + L ^ 2 / (12 * D * (n : ℝ) ^ 2)) =
      L * meanStrengthLoss K E.strength E.partition.width +
        (L ^ 2 / D) * meanPositionLoss E.partition.width
          (fun i => E.geometry.site i / L) +
        (L ^ 2 / (12 * D)) * meanShareLoss E.partition.width := by
  rw [E.homogeneous_meanCost_eq_score]
  exact cdf_mean_deficit_identity E.strength E.partition.width
    (fun i => E.geometry.site i / L) E.partition.size_pos (ne_of_gt hK)
    (fun i => ne_of_gt (E.strength_pos i)) E.strength_sum E.partition.width_sum

theorem homogeneous_mean_lower_bound (hK : 0 < K)
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    L / K + L ^ 2 / (12 * D * (n : ℝ) ^ 2) ≤ E.meanCost := by
  rw [E.homogeneous_meanCost_eq_score]
  exact cdf_mean_lower_bound E.strength E.partition.width (fun i => E.geometry.site i / L)
    hL hD hK E.partition.size_pos E.strength_pos
    (fun i => (E.partition.width_pos i).le) E.strength_sum E.partition.width_sum

theorem homogeneous_mean_losses_zero (hK : 0 < K)
    (E : IntervalDesign (homogeneous L D hL hD) n K)
    (hmean : E.meanCost = L / K + L ^ 2 / (12 * D * (n : ℝ) ^ 2)) :
    meanStrengthLoss K E.strength E.partition.width = 0 ∧
      meanPositionLoss E.partition.width (fun i => E.geometry.site i / L) = 0 ∧
      meanShareLoss E.partition.width = 0 := by
  have he := homogeneous_mean_deficit hK E
  rw [hmean, sub_self] at he
  have hs := meanStrengthLoss_nonneg K E.strength E.partition.width E.strength_pos
  have hx := meanPositionLoss_nonneg E.partition.width (fun i => E.geometry.site i / L)
    (fun i => (E.partition.width_pos i).le)
  have hp := meanShareLoss_nonneg E.partition.width (fun i => (E.partition.width_pos i).le)
  have hcx : 0 < L ^ 2 / D := div_pos (sq_pos_of_pos hL) hD
  have hcp : 0 < L ^ 2 / (12 * D) :=
    div_pos (sq_pos_of_pos hL) (mul_pos (by norm_num) hD)
  have hs' := mul_nonneg hL.le hs
  have hx' := mul_nonneg hcx.le hx
  have hp' := mul_nonneg hcp.le hp
  have hz1 : L * meanStrengthLoss K E.strength E.partition.width = 0 := by linarith
  have hz2 : (L ^ 2 / D) * meanPositionLoss E.partition.width
      (fun i => E.geometry.site i / L) = 0 := by linarith
  have hz3 : (L ^ 2 / (12 * D)) * meanShareLoss E.partition.width = 0 := by linarith
  exact ⟨(mul_eq_zero.mp hz1).resolve_left (ne_of_gt hL),
    (mul_eq_zero.mp hz2).resolve_left (ne_of_gt hcx),
    (mul_eq_zero.mp hz3).resolve_left (ne_of_gt hcp)⟩

theorem homogeneous_mean_parameters_of_eq (hK : 0 < K)
    (E : IntervalDesign (homogeneous L D hL hD) n K)
    (hmean : E.meanCost = L / K + L ^ 2 / (12 * D * (n : ℝ) ^ 2)) :
    (∀ i, E.geometry.site i = (2 * (i.val : ℝ) + 1) * L / (2 * n)) ∧
      (∀ i, E.strength i = K / n) := by
  obtain ⟨hs, hx, hp⟩ := homogeneous_mean_losses_zero hK E hmean
  have hshare := (meanShareLoss_eq_zero_iff E.partition.width E.partition.size_pos
    (fun i => (E.partition.width_pos i).le)).mp hp
  have hQ := E.partition.eq_uniform_of_width E.partition.size_pos hshare
  have hposition := (meanPositionLoss_eq_zero_iff E.partition.width
    (fun i => E.geometry.site i / L) E.partition.width_pos).mp hx
  have hstrength := (meanStrengthLoss_eq_zero_iff K E.strength E.partition.width
    E.strength_pos).mp hs
  constructor
  · intro i
    have hi := hposition i
    rw [E.partition.prefix_width, E.partition.prefix_width, hQ,
      StrictPartition.uniform_point, StrictPartition.uniform_point] at hi
    simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at hi
    calc
      E.geometry.site i = (((i.val : ℝ) / n + ((i.val : ℝ) + 1) / n) / 2) * L :=
        (div_eq_iff (ne_of_gt hL)).mp hi
      _ = _ := by ring
  · intro i
    have hi := hstrength i
    rw [hshare i] at hi
    calc
      E.strength i = (1 / (n : ℝ)) * K := ((eq_div_iff (ne_of_gt hK)).mp hi).symm
      _ = K / n := by ring

end TimeTraps.Interval
