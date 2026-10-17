module

public import TimeTraps.Probability.HomogeneousAttainmentLifetimeObjective
public import TimeTraps.Probability.HomogeneousLifetimeOptimization

@[expose] public section

/-! The sharp homogeneous lifetime objectives with the paper's literal
first-attainment convention. Both lower bounds, complete midpoint and
equal-strength equality classes, and attained minima concern the ordinary
expectation of that lifetime in the original physical design space. -/

namespace TimeTraps.Probability

open Set TimeTraps.Interval

variable {L D K : ℝ} {n : ℕ}

theorem homogeneousAttainmentLifetimeWorst_lower_bound
    (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K)
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    L / K + L ^ 2 / (8 * D * (n : ℝ) ^ 2) ≤ homogeneousAttainmentLifetimeWorst E := by
  rw [homogeneousAttainmentLifetimeWorst_eq_strict]
  exact homogeneousLifetimeWorst_lower_bound hL hD hn hK E

theorem homogeneousAttainmentLifetimeMean_lower_bound
    (hL : 0 < L) (hD : 0 < D) (hK : 0 < K)
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    L / K + L ^ 2 / (12 * D * (n : ℝ) ^ 2) ≤ homogeneousAttainmentLifetimeMean E := by
  rw [homogeneousAttainmentLifetimeMean_eq_strict]
  exact homogeneousLifetimeMean_lower_bound hL hD hK E

theorem homogeneousAttainmentLifetimeWorst_eq_iff
    (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K)
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    homogeneousAttainmentLifetimeWorst E = L / K + L ^ 2 / (8 * D * (n : ℝ) ^ 2) ↔
      (∀ i, E.geometry.site i = (2 * (i.val : ℝ) + 1) * L / (2 * n)) ∧
      (∀ i, E.strength i = K / n) := by
  rw [homogeneousAttainmentLifetimeWorst_eq_strict]
  exact homogeneousLifetimeWorst_eq_iff hL hD hn hK E

theorem homogeneousAttainmentLifetimeMean_eq_iff
    (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K)
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    homogeneousAttainmentLifetimeMean E = L / K + L ^ 2 / (12 * D * (n : ℝ) ^ 2) ↔
      (∀ i, E.geometry.site i = (2 * (i.val : ℝ) + 1) * L / (2 * n)) ∧
      (∀ i, E.strength i = K / n) := by
  rw [homogeneousAttainmentLifetimeMean_eq_strict]
  exact homogeneousLifetimeMean_eq_iff hL hD hn hK E

theorem homogeneousAttainmentLifetimeWorst_minimum
    (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K) :
    IsLeast (range (fun E : IntervalDesign (homogeneous L D hL hD) n K =>
      homogeneousAttainmentLifetimeWorst E)) (L / K + L ^ 2 / (8 * D * (n : ℝ) ^ 2)) := by
  simpa only [homogeneousAttainmentLifetimeWorst_eq_strict] using
    homogeneousLifetimeWorst_minimum hL hD hn hK

theorem homogeneousAttainmentLifetimeMean_minimum
    (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K) :
    IsLeast (range (fun E : IntervalDesign (homogeneous L D hL hD) n K =>
      homogeneousAttainmentLifetimeMean E)) (L / K + L ^ 2 / (12 * D * (n : ℝ) ^ 2)) := by
  simpa only [homogeneousAttainmentLifetimeMean_eq_strict] using
    homogeneousLifetimeMean_minimum hL hD hn hK

end TimeTraps.Probability
