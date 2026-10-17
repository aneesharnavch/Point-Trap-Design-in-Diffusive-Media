module

public import TimeTraps.Interval.EndpointAttainment

@[expose] public section

/-! Scalar equality conditions forced by physical endpoint optimality.
The closed-partition comparison includes repeated nodes, while every
physical design has a strict absorption partition. -/

namespace TimeTraps.Interval

open Set TimeTraps.Analysis

variable {A : EndpointArchitecture} {B : IntervalMedium} {K : ℝ}

theorem EndpointPhysicalDesign.optimal_iff_isLeast (E : EndpointPhysicalDesign A B K) :
    E.Optimal ↔ IsLeast (range (fun F : EndpointPhysicalDesign A B K => F.cost)) E.cost := by
  constructor
  · intro hE
    refine ⟨⟨E, rfl⟩, ?_⟩
    rintro M ⟨F, rfl⟩
    exact hE F
  · intro hE F
    exact hE.2 ⟨F, rfl⟩

theorem EndpointPhysicalDesign.optimal_cost_eq_root (E : EndpointPhysicalDesign A B K)
    (hE : E.Optimal) :
    E.cost = A.root E.partition.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos) := by
  apply le_antisymm _ E.partition_root_bound
  have h := hE (B.endpointPartitionDesign A E.partition E.reactions.budget_pos)
  rwa [B.endpointPartitionDesign_cost] at h

theorem EndpointPhysicalDesign.optimal_partition_minimal (E : EndpointPhysicalDesign A B K)
    (hE : E.Optimal) (P : ClosedPartition A.count) :
    A.root E.partition.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos) ≤
      A.root P B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos) := by
  obtain ⟨Q, hQ⟩ := A.strict_minimum_exists B.cellWeight
    (div_pos E.reactions.budget_pos B.source.mass_pos)
  rw [← E.optimal_cost_eq_root hE]
  have h := hE (B.endpointPartitionDesign A Q E.reactions.budget_pos)
  rw [B.endpointPartitionDesign_cost] at h
  exact h.trans (hQ P)

theorem EndpointPhysicalDesign.optimal_iff_root_partition (E : EndpointPhysicalDesign A B K) :
    E.Optimal ↔
      E.cost = A.root E.partition.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos) ∧
      (∀ P : ClosedPartition A.count,
        A.root E.partition.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos) ≤
          A.root P B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos)) := by
  constructor
  · intro hE
    exact ⟨E.optimal_cost_eq_root hE, E.optimal_partition_minimal hE⟩
  · rintro ⟨he, hp⟩ F
    rw [he]
    exact (hp F.partition.closed).trans F.partition_root_bound

theorem EndpointPhysicalDesign.optimal_budget_eq (E : EndpointPhysicalDesign A B K)
    (hE : E.Optimal) :
    budget Finset.univ (E.reactions.activeShare E.geometry E.state)
      (A.barrier E.partition.closed E.geometry.medium.cellWeight) E.cost =
        K / E.geometry.source.mass := by
  have hs : E.geometry.source = B.source := congrArg IntervalMedium.source E.medium_eq
  have hw : E.partition.closed.width = E.reactions.activeShare E.geometry E.state :=
    funext E.equation.partition_width
  rw [E.medium_eq, hs, E.optimal_cost_eq_root hE, ← hw]
  exact (A.root_spec E.partition.closed B.cellWeight
    (div_pos E.reactions.budget_pos B.source.mass_pos)).2

theorem endpoint_reconstruction_optimal_iff (Q : StrictPartition A.count) (hK : 0 < K) :
    (B.endpointPartitionDesign A Q hK).Optimal ↔
      (∀ P : ClosedPartition A.count,
        A.root Q.closed B.cellWeight (div_pos hK B.source.mass_pos) ≤
          A.root P B.cellWeight (div_pos hK B.source.mass_pos)) := by
  rw [EndpointPhysicalDesign.optimal_iff_root_partition,
    B.endpointPartitionDesign_cost, B.endpointPartitionDesign_partition]
  exact and_iff_right rfl

end TimeTraps.Interval
