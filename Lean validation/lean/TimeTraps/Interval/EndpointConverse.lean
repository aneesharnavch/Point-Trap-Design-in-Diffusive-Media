module

public import TimeTraps.Interval.EndpointStateEquality
public import TimeTraps.Interval.EndpointOptimality

@[expose] public section

/-! Complete reconstruction characterization of actual endpoint physical
optimizers. The partition is the state's own absorption partition; the
sites, strengths, and state are the independently verified reconstruction.
Only ordinary cells use balanced centers. Reactive endpoint cells retain
their fixed endpoints and full one-sided barriers, also when m = 0. -/

namespace TimeTraps.Interval

open Set TimeTraps.Analysis

variable {A : EndpointArchitecture} {B : IntervalMedium} {K : ℝ}

theorem EndpointPhysicalDesign.optimal_sourceSites (E : EndpointPhysicalDesign A B K)
    (hE : E.Optimal) (i : Fin A.count) :
    A.sourceSite E.geometry i = A.reconstructionSite E.partition B.cellWeight i := by
  have he := E.equation.mixed_budget_equality_sites (E.optimal_budget_eq hE) i
  change A.sourceSite E.geometry i = A.reconstructionSite E.partition E.geometry.medium.cellWeight i at he
  rwa [E.medium_eq] at he

theorem EndpointPhysicalDesign.optimal_physicalSites (E : EndpointPhysicalDesign A B K)
    (hE : E.Optimal) (i : Fin A.count) :
    A.physicalSite E.geometry i = B.source.inverse (A.reconstructionSite E.partition B.cellWeight i) := by
  have he := E.equation.mixed_budget_equality_physicalSites (E.optimal_budget_eq hE) i
  have hs : E.geometry.source = B.source := congrArg IntervalMedium.source E.medium_eq
  change A.physicalSite E.geometry i =
    E.geometry.source.inverse (A.reconstructionSite E.partition E.geometry.medium.cellWeight i) at he
  rwa [E.medium_eq, hs] at he

theorem EndpointPhysicalDesign.optimal_interiorSites (E : EndpointPhysicalDesign A B K)
    (hE : E.Optimal) (j : Fin A.interiorCount) :
    E.geometry.site j = B.partitionSites E.partition (A.interiorCell j) := by
  have he := E.equation.mixed_budget_equality_interiorSites (E.optimal_budget_eq hE) j
  change E.geometry.site j = E.geometry.medium.partitionSites E.partition (A.interiorCell j) at he
  rwa [E.medium_eq] at he

theorem EndpointPhysicalDesign.optimal_activeStrength (E : EndpointPhysicalDesign A B K)
    (hE : E.Optimal) (i : Fin A.count) :
    E.reactions.activeStrength i = B.endpointPartitionStrength A E.partition
      (A.root E.partition.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos)) i := by
  have he := E.equation.mixed_budget_equality_strength (E.optimal_budget_eq hE) i
  change E.reactions.activeStrength i = E.geometry.medium.endpointPartitionStrength A E.partition E.cost i at he
  rwa [E.medium_eq, E.optimal_cost_eq_root hE] at he

theorem EndpointPhysicalDesign.optimal_state (E : EndpointPhysicalDesign A B K) (hE : E.Optimal) :
    EqOn E.state (B.endpointPartitionState A E.partition
      (A.root E.partition.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos)))
      (Icc B.source.left B.source.right) := by
  have he := E.equation.mixed_budget_equality_state (E.optimal_budget_eq hE)
  have hs : E.geometry.source = B.source := congrArg IntervalMedium.source E.medium_eq
  change EqOn E.state (E.geometry.medium.endpointPartitionState A E.partition E.cost)
    (Icc E.geometry.source.left E.geometry.source.right) at he
  rwa [E.medium_eq, hs, E.optimal_cost_eq_root hE] at he

theorem EndpointPhysicalDesign.optimal_cellHeights (E : EndpointPhysicalDesign A B K)
    (hE : E.Optimal) (e : Fin (A.interiorCount + 1)) :
    B.source.transformed E.state (E.partition.point (A.gapBoundary e)) =
      A.root E.partition.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos) := by
  have he := E.equation.mixed_budget_equality_boundaries (E.optimal_budget_eq hE) e
  have hs : E.geometry.source = B.source := congrArg IntervalMedium.source E.medium_eq
  change E.geometry.source.transformed E.state (E.partition.point (A.gapBoundary e)) = E.cost at he
  rwa [hs, E.optimal_cost_eq_root hE] at he

theorem EndpointPhysicalDesign.optimal_siteValues (E : EndpointPhysicalDesign A B K)
    (hE : E.Optimal) (i : Fin A.count) :
    E.state (A.physicalSite E.geometry i) =
      A.root E.partition.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos) -
        A.barrier E.partition.closed B.cellWeight i := by
  have he := E.equation.mixed_budget_equality_loss (E.optimal_budget_eq hE) i
  change E.cost - E.state (A.physicalSite E.geometry i) =
    A.barrier E.partition.closed E.geometry.medium.cellWeight i at he
  rw [E.medium_eq, E.optimal_cost_eq_root hE] at he
  linarith

/-- Actual physical optimality is equivalent to a scalar-minimizing
absorption partition and its full position, strength, and state reconstruction. -/
theorem EndpointPhysicalDesign.optimal_iff_reconstruction (E : EndpointPhysicalDesign A B K) :
    E.Optimal ↔
      (∀ P : ClosedPartition A.count,
        A.root E.partition.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos) ≤
          A.root P B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos)) ∧
      (∀ i, A.sourceSite E.geometry i = A.reconstructionSite E.partition B.cellWeight i) ∧
      (∀ i, E.reactions.activeStrength i = B.endpointPartitionStrength A E.partition
        (A.root E.partition.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos)) i) ∧
      EqOn E.state (B.endpointPartitionState A E.partition
        (A.root E.partition.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos)))
        (Icc B.source.left B.source.right) := by
  constructor
  · intro hE
    exact ⟨E.optimal_partition_minimal hE, E.optimal_sourceSites hE,
      E.optimal_activeStrength hE, E.optimal_state hE⟩
  · rintro ⟨hmin, _, _, hstate⟩
    apply E.optimal_iff_root_partition.mpr
    exact ⟨E.cost_eq_of_partition_state E.partition _ hstate, hmin⟩

end TimeTraps.Interval
