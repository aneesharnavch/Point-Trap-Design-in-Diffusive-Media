module

public import TimeTraps.Probability.ReflectedRobinEndpointLifetimeOptimization
public import TimeTraps.Interval.EndpointParameterEquality

@[expose] public section

/-! A physical parameter vector minimizes actual lifetime exactly when
it comes from a scalar-minimizing mixed partition. No candidate is
restricted to reconstructed states in the definition of the objective. -/

namespace TimeTraps.Probability

open Set TimeTraps.Analysis TimeTraps.Interval

variable {A : EndpointArchitecture} {B : IntervalMedium} {K : ℝ}

theorem reflectedRobinEndpointLifetimeWorst_optimizer_parameters_iff (E : EndpointPhysicalDesign A B K) :
    (∀ F : EndpointPhysicalDesign A B K,
      reflectedRobinEndpointLifetimeWorst E ≤ reflectedRobinEndpointLifetimeWorst F) ↔
      (∀ P : ClosedPartition A.count,
        A.root E.partition.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos) ≤
          A.root P B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos)) ∧
      (∀ j, E.geometry.site j = B.partitionSites E.partition (A.interiorCell j)) ∧
      (∀ i, E.reactions.activeStrength i = B.endpointPartitionStrength A E.partition
        (A.root E.partition.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos)) i) :=
  (reflectedRobinEndpointLifetimeWorst_optimal_iff E).trans E.optimal_iff_reconstruction_parameters

theorem reflectedRobinEndpointLifetimeWorst_optimizer_exists_parameters_iff (E : EndpointPhysicalDesign A B K) :
    (∀ F : EndpointPhysicalDesign A B K,
      reflectedRobinEndpointLifetimeWorst E ≤ reflectedRobinEndpointLifetimeWorst F) ↔
      ∃ Q : StrictPartition A.count,
      (∀ P : ClosedPartition A.count,
        A.root Q.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos) ≤
          A.root P B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos)) ∧
      (∀ j, E.geometry.site j = B.partitionSites Q (A.interiorCell j)) ∧
      (∀ i, E.reactions.activeStrength i = B.endpointPartitionStrength A Q
        (A.root Q.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos)) i) :=
  (reflectedRobinEndpointLifetimeWorst_optimal_iff E).trans E.optimal_iff_exists_reconstruction_parameters

end TimeTraps.Probability
