module

public import TimeTraps.Interval.MeanStrengthStability
public import TimeTraps.Interval.HomogeneousMeanDeficit

@[expose] public section

/-!
Global strength stability for the actual Lebesgue mean of every physical
homogeneous weak design on [0,1]. Absorption shares are derived from its
weak state; the stated physical strengths remain the design parameters.
-/

namespace TimeTraps.Interval

open scoped BigOperators

variable {n : ℕ} {D K : ℝ}

theorem homogeneous_mean_strength_stability (hD : 0 < D) (hK : 0 < K)
    (E : IntervalDesign (homogeneous 1 D zero_lt_one hD) n K) :
    (∑ i, (E.strength i - K / (n : ℝ)) ^ 2) / (K ^ 2 * (6 * D * (n : ℝ) + K)) ≤
      E.meanCost - (1 / K + 1 / (12 * D * (n : ℝ) ^ 2)) := by
  rw [E.homogeneous_meanCost_eq_score]
  exact cdf_mean_strength_stability E.strength E.partition.width
    (fun i => E.geometry.site i / 1) hD hK E.partition.size_pos E.strength_pos
    E.partition.width_pos E.strength_sum E.partition.width_sum

end TimeTraps.Interval
