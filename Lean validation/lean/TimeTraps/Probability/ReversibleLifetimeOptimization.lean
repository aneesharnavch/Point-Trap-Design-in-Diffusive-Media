module

public import TimeTraps.Probability.ReversibleLifetimeObjective

@[expose] public section

/-! The full arbitrary-medium partition minimum and optimizer class
hold for actual first-attainment expected lifetimes. Every admissible
physical design remains in the comparison class. -/

namespace TimeTraps.Probability

open Set TimeTraps.Interval

variable {A : IntervalMedium} {n : ℕ} {K : ℝ}

theorem reversibleLifetimeWorst_partition_lower_bound (E : IntervalDesign A n K) (hK : 0 < K) :
    E.partition.closed.root A.cellWeight (div_pos hK A.source.mass_pos) ≤ reversibleLifetimeWorst E := by
  rw [reversibleLifetimeWorst_eq]
  exact E.partition_root_lower_bound hK

theorem reversibleLifetimeWorst_global_minimum (A : IntervalMedium) (hn : 0 < n)
    {K : ℝ} (hK : 0 < K) :
    ∃ Q : StrictPartition n,
      IsLeast (range (fun P : StrictPartition n =>
        P.closed.root A.cellWeight (div_pos hK A.source.mass_pos)))
        (Q.closed.root A.cellWeight (div_pos hK A.source.mass_pos)) ∧
      IsLeast (range (fun E : IntervalDesign A n K => reversibleLifetimeWorst E))
        (Q.closed.root A.cellWeight (div_pos hK A.source.mass_pos)) := by
  rw [reversibleLifetimeWorst_values_eq]
  exact A.global_minimum hn hK

theorem reversibleLifetimeWorst_optimal_iff (E : IntervalDesign A n K) :
    (∀ F : IntervalDesign A n K, reversibleLifetimeWorst E ≤ reversibleLifetimeWorst F) ↔ E.Optimal := by
  simp only [reversibleLifetimeWorst_eq, IntervalDesign.Optimal]

theorem reversibleLifetimeWorst_optimizer_iff (E : IntervalDesign A n K) (hK : 0 < K) :
    (∀ F : IntervalDesign A n K, reversibleLifetimeWorst E ≤ reversibleLifetimeWorst F) ↔
      ∃ Q : StrictPartition n,
        (∀ P : StrictPartition n,
          Q.closed.root A.cellWeight (div_pos hK A.source.mass_pos) ≤
            P.closed.root A.cellWeight (div_pos hK A.source.mass_pos)) ∧
        (∀ i, E.geometry.site i = A.partitionSites Q i) ∧
        (∀ i, E.strength i = A.partitionStrength Q
          (Q.closed.root A.cellWeight (div_pos hK A.source.mass_pos)) i) :=
  (reversibleLifetimeWorst_optimal_iff E).trans (E.optimal_iff_reconstruction hK)

theorem reversibleLifetimeWorst_construct_attains (A : IntervalMedium) (Q : StrictPartition n)
    {K : ℝ} (hK : 0 < K)
    (hQ : ∀ P : StrictPartition n,
      Q.closed.root A.cellWeight (div_pos hK A.source.mass_pos) ≤
        P.closed.root A.cellWeight (div_pos hK A.source.mass_pos)) :
    IsLeast (range (fun E : IntervalDesign A n K => reversibleLifetimeWorst E))
      (Q.closed.root A.cellWeight (div_pos hK A.source.mass_pos)) := by
  rw [reversibleLifetimeWorst_values_eq, ← A.construct_cost Q hK]
  exact ((A.construct Q hK).optimal_iff_isLeast).mp (A.construct_optimal Q hK hQ)

end TimeTraps.Probability
