module

public import TimeTraps.Probability.HomogeneousLifetimeObjective

@[expose] public section

/-! Sharp worst-start and uniform-start mean lifetime optimization over
the original homogeneous physical design space. These bounds concern
ordinary expectations of the actual independently killed reflected
process. The full midpoint/equal-strength equality classes and attained
minima transfer from the independently proved deterministic objectives. -/

namespace TimeTraps.Probability

open Set TimeTraps.Interval

variable {L D K : ℝ} {n : ℕ}

theorem homogeneousLifetimeWorst_lower_bound
    (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K)
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    L / K + L ^ 2 / (8 * D * (n : ℝ) ^ 2) ≤ homogeneousLifetimeWorst E := by
  rw [homogeneousLifetimeWorst_eq]
  exact homogeneous_lower_bound hL hD hn hK E

theorem homogeneousLifetimeMean_lower_bound
    (hL : 0 < L) (hD : 0 < D) (hK : 0 < K)
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    L / K + L ^ 2 / (12 * D * (n : ℝ) ^ 2) ≤ homogeneousLifetimeMean E := by
  rw [homogeneousLifetimeMean_eq]
  exact homogeneous_mean_lower_bound hK E

theorem homogeneousLifetimeWorst_eq_iff
    (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K)
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    homogeneousLifetimeWorst E = L / K + L ^ 2 / (8 * D * (n : ℝ) ^ 2) ↔
      (∀ i, E.geometry.site i = (2 * (i.val : ℝ) + 1) * L / (2 * n)) ∧
      (∀ i, E.strength i = K / n) := by
  rw [homogeneousLifetimeWorst_eq]
  exact homogeneous_cost_eq_iff hL hD hn hK E

theorem homogeneousLifetimeMean_eq_iff
    (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K)
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    homogeneousLifetimeMean E = L / K + L ^ 2 / (12 * D * (n : ℝ) ^ 2) ↔
      (∀ i, E.geometry.site i = (2 * (i.val : ℝ) + 1) * L / (2 * n)) ∧
      (∀ i, E.strength i = K / n) := by
  rw [homogeneousLifetimeMean_eq]
  exact homogeneous_mean_cost_eq_iff hL hD hn hK E

theorem homogeneousLifetimeWorst_minimum
    (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K) :
    IsLeast (range (fun E : IntervalDesign (homogeneous L D hL hD) n K =>
      homogeneousLifetimeWorst E)) (L / K + L ^ 2 / (8 * D * (n : ℝ) ^ 2)) := by
  simpa only [homogeneousLifetimeWorst_eq] using homogeneous_minimum hL hD hn hK

theorem homogeneousLifetimeMean_minimum
    (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K) :
    IsLeast (range (fun E : IntervalDesign (homogeneous L D hL hD) n K =>
      homogeneousLifetimeMean E)) (L / K + L ^ 2 / (12 * D * (n : ℝ) ^ 2)) := by
  simpa only [homogeneousLifetimeMean_eq] using homogeneous_mean_minimum hL hD hn hK

end TimeTraps.Probability
