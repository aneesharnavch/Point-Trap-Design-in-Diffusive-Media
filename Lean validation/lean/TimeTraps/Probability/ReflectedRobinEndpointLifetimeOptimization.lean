module

public import TimeTraps.Probability.ReflectedRobinEndpointLifetimeObjective

@[expose] public section

/-! Complete global minimization and equality characterization for the
actual physical worst-start lifetime. Every original endpoint design
remains a competitor; the scalar comparison includes closed partitions. -/

namespace TimeTraps.Probability

open Set TimeTraps.Analysis TimeTraps.Interval

variable {A : EndpointArchitecture} {B : IntervalMedium} {K : ℝ}

theorem reflectedRobinEndpointLifetimeWorst_partition_lower_bound (E : EndpointPhysicalDesign A B K) :
    A.root E.partition.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos) ≤
      reflectedRobinEndpointLifetimeWorst E := by
  rw [reflectedRobinEndpointLifetimeWorst_eq]
  exact E.partition_root_bound

theorem reflectedRobinEndpointLifetimeWorst_global_minimum (A : EndpointArchitecture) (B : IntervalMedium)
    {K : ℝ} (hK : 0 < K) :
    ∃ Q : StrictPartition A.count,
      IsLeast (range (fun P : ClosedPartition A.count =>
        A.root P B.cellWeight (div_pos hK B.source.mass_pos)))
        (A.root Q.closed B.cellWeight (div_pos hK B.source.mass_pos)) ∧
      IsLeast (range (fun E : EndpointPhysicalDesign A B K => reflectedRobinEndpointLifetimeWorst E))
        (A.root Q.closed B.cellWeight (div_pos hK B.source.mass_pos)) := by
  rw [reflectedRobinEndpointLifetimeWorst_values_eq]
  exact endpoint_physical_scalar_minimum A B hK

theorem reflectedRobinEndpointLifetimeWorst_optimal_iff (E : EndpointPhysicalDesign A B K) :
    (∀ F : EndpointPhysicalDesign A B K,
      reflectedRobinEndpointLifetimeWorst E ≤ reflectedRobinEndpointLifetimeWorst F) ↔ E.Optimal := by
  simp only [reflectedRobinEndpointLifetimeWorst_eq, EndpointPhysicalDesign.Optimal]

theorem reflectedRobinEndpointLifetimeWorst_optimizer_iff (E : EndpointPhysicalDesign A B K) :
    (∀ F : EndpointPhysicalDesign A B K,
      reflectedRobinEndpointLifetimeWorst E ≤ reflectedRobinEndpointLifetimeWorst F) ↔
      (∀ P : ClosedPartition A.count,
        A.root E.partition.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos) ≤
          A.root P B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos)) ∧
      (∀ i, A.sourceSite E.geometry i = A.reconstructionSite E.partition B.cellWeight i) ∧
      (∀ i, E.reactions.activeStrength i = B.endpointPartitionStrength A E.partition
        (A.root E.partition.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos)) i) ∧
      EqOn (reflectedRobinEndpointLifetimeExpectation E) (B.endpointPartitionState A E.partition
        (A.root E.partition.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos)))
        (Icc B.source.left B.source.right) := by
  rw [reflectedRobinEndpointLifetimeWorst_optimal_iff, E.optimal_iff_reconstruction]
  constructor
  · rintro ⟨hp, hs, hk, hu⟩
    exact ⟨hp, hs, hk, (reflectedRobinEndpointLifetimeExpectation_eqOn E).trans hu⟩
  · rintro ⟨hp, hs, hk, hu⟩
    exact ⟨hp, hs, hk, (reflectedRobinEndpointLifetimeExpectation_eqOn E).symm.trans hu⟩

theorem reflectedRobinEndpointLifetimeWorst_optimizer_physicalSites (E : EndpointPhysicalDesign A B K)
    (hE : ∀ F : EndpointPhysicalDesign A B K,
      reflectedRobinEndpointLifetimeWorst E ≤ reflectedRobinEndpointLifetimeWorst F) (i : Fin A.count) :
    A.physicalSite E.geometry i = B.source.inverse (A.reconstructionSite E.partition B.cellWeight i) :=
  E.optimal_physicalSites ((reflectedRobinEndpointLifetimeWorst_optimal_iff E).mp hE) i

theorem reflectedRobinEndpointLifetimeWorst_construct_attains
    (A : EndpointArchitecture) (B : IntervalMedium) (Q : StrictPartition A.count)
    {K : ℝ} (hK : 0 < K)
    (hQ : ∀ P : ClosedPartition A.count,
      A.root Q.closed B.cellWeight (div_pos hK B.source.mass_pos) ≤
        A.root P B.cellWeight (div_pos hK B.source.mass_pos)) :
    IsLeast (range (fun E : EndpointPhysicalDesign A B K => reflectedRobinEndpointLifetimeWorst E))
      (A.root Q.closed B.cellWeight (div_pos hK B.source.mass_pos)) := by
  rw [reflectedRobinEndpointLifetimeWorst_values_eq, ← B.endpointPartitionDesign_cost A Q hK]
  exact ((B.endpointPartitionDesign A Q hK).optimal_iff_isLeast).mp
    ((endpoint_reconstruction_optimal_iff Q hK).mpr hQ)

theorem reflectedRobinEndpointLifetimeWorst_partition_attainment
    (A : EndpointArchitecture) (B : IntervalMedium) (Q : StrictPartition A.count)
    {K : ℝ} (hK : 0 < K) :
    ∃ E : EndpointPhysicalDesign A B K, E.partition = Q ∧
      reflectedRobinEndpointLifetimeWorst E = A.root Q.closed B.cellWeight (div_pos hK B.source.mass_pos) :=
  ⟨B.endpointPartitionDesign A Q hK, B.endpointPartitionDesign_partition A Q hK,
    (reflectedRobinEndpointLifetimeWorst_eq _).trans (B.endpointPartitionDesign_cost A Q hK)⟩

end TimeTraps.Probability
