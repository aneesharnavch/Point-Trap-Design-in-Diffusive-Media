module

public import TimeTraps.Interval.HomogeneousMeanDeficit
public import TimeTraps.Interval.HomogeneousMean

@[expose] public section

/-!
The deterministic homogeneous mean optimum is attained over the independent
physical weak-design space. Its complete equality class agrees with the
homogeneous worst-start optimizer. No stochastic lifetime identification is
used or asserted by these statements.
-/

namespace TimeTraps.Interval

open Set

variable {n : ℕ} {K : ℝ}

def IntervalDesign.MeanOptimal {A : IntervalMedium} (E : IntervalDesign A n K) : Prop :=
  ∀ F : IntervalDesign A n K, E.meanCost ≤ F.meanCost

theorem IntervalDesign.meanOptimal_iff_isLeast {A : IntervalMedium}
    (E : IntervalDesign A n K) :
    E.MeanOptimal ↔ IsLeast (range (fun F : IntervalDesign A n K => F.meanCost)) E.meanCost := by
  constructor
  · intro hE
    refine ⟨⟨E, rfl⟩, ?_⟩
    rintro M ⟨F, rfl⟩
    exact hE F
  · intro hE F
    exact hE.2 ⟨F, rfl⟩

variable {L D : ℝ}

theorem homogeneous_mean_cost_eq_iff (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K)
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    E.meanCost = L / K + L ^ 2 / (12 * D * (n : ℝ) ^ 2) ↔
      (∀ i, E.geometry.site i = (2 * (i.val : ℝ) + 1) * L / (2 * n)) ∧
      (∀ i, E.strength i = K / n) := by
  constructor
  · exact homogeneous_mean_parameters_of_eq hK E
  · intro hp
    rw [E.homogeneous_meanCost]
    exact homogeneous_optimal_mean hL hD hn hK E ((homogeneous_optimal_iff hL hD hn hK E).mpr hp)

theorem homogeneous_mean_minimum (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K) :
    IsLeast (range (fun E : IntervalDesign (homogeneous L D hL hD) n K => E.meanCost))
      (L / K + L ^ 2 / (12 * D * (n : ℝ) ^ 2)) := by
  refine ⟨⟨(homogeneous L D hL hD).construct (StrictPartition.uniform n hn) hK, ?_⟩, ?_⟩
  · change ((homogeneous L D hL hD).construct (StrictPartition.uniform n hn) hK).meanCost = _
    rw [IntervalDesign.homogeneous_meanCost]
    exact homogeneous_construct_mean hL hD hn hK
  · rintro M ⟨E, rfl⟩
    exact homogeneous_mean_lower_bound hK E

theorem homogeneous_mean_optimal_iff_cost_eq
    (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K)
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    E.MeanOptimal ↔ E.meanCost = L / K + L ^ 2 / (12 * D * (n : ℝ) ^ 2) := by
  constructor
  · intro hE
    have hleast := homogeneous_mean_minimum hL hD hn hK
    exact (E.meanOptimal_iff_isLeast.mp hE).unique hleast
  · intro hE F
    rw [hE]
    exact homogeneous_mean_lower_bound hK F

theorem homogeneous_mean_optimal_iff
    (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K)
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    E.MeanOptimal ↔
      (∀ i, E.geometry.site i = (2 * (i.val : ℝ) + 1) * L / (2 * n)) ∧
      (∀ i, E.strength i = K / n) :=
  (homogeneous_mean_optimal_iff_cost_eq hL hD hn hK E).trans
    (homogeneous_mean_cost_eq_iff hL hD hn hK E)

theorem homogeneous_mean_optimal_iff_worst_start
    (hL : 0 < L) (hD : 0 < D) (hn : 0 < n) (hK : 0 < K)
    (E : IntervalDesign (homogeneous L D hL hD) n K) : E.MeanOptimal ↔ E.Optimal :=
  (homogeneous_mean_optimal_iff hL hD hn hK E).trans
    (homogeneous_optimal_iff hL hD hn hK E).symm

end TimeTraps.Interval
