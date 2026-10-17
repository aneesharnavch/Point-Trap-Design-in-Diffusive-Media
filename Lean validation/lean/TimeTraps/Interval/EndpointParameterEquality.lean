module

public import TimeTraps.Interval.EndpointConverse
public import TimeTraps.Interval.PhysicalDesign

@[expose] public section

/-! Equal physical parameters determine the complete endpoint state by
uniqueness of the original full-H1 weak equation. This removes state
equality as an extra premise from the reconstruction converse. -/

namespace TimeTraps.Interval

open Set

variable {A : EndpointArchitecture} {B : IntervalMedium} {K : ℝ}

theorem EndpointReactions.nodal_eq_of_active (R T : EndpointReactions A K)
    (hκ : ∀ i, R.activeStrength i = T.activeStrength i) : R.nodal = T.nodal := by
  funext v
  by_cases hv : ∃ i, A.activeNode i = v
  · obtain ⟨i, rfl⟩ := hv
    exact hκ i
  · rcases A.inactiveNode v hv with ⟨hl, rfl⟩ | ⟨hr, rfl⟩
    · rw [R.nodal_first, T.nodal_first, R.left_zero hl, T.left_zero hl]
    · rw [R.nodal_last, T.nodal_last, R.right_zero hr, T.right_zero hr]

theorem EndpointPhysicalDesign.state_eq_of_parameters (E F : EndpointPhysicalDesign A B K)
    (hsite : ∀ j, E.geometry.site j = F.geometry.site j)
    (hκ : ∀ i, E.reactions.activeStrength i = F.reactions.activeStrength i) :
    EqOn E.state F.state (Icc B.source.left B.source.right) := by
  have hG := OrderedMedium.eq_of_medium_sites (E.medium_eq.trans F.medium_eq.symm) hsite
  have hR := E.reactions.nodal_eq_of_active F.reactions hκ
  have hw := E.equation
  rw [hG] at hw
  have ht : EndpointWeakEquation F.geometry F.reactions E.state := by
    refine ⟨hw.energy, ?_⟩
    intro v hv
    have he := hw.weak_form v hv
    rwa [hR] at he
  have he := endpoint_weak_state_unique ht F.equation
  have hs : F.geometry.source = B.source := congrArg IntervalMedium.source F.medium_eq
  simpa only [hs] using he

theorem EndpointPhysicalDesign.cost_eq_of_parameters (E F : EndpointPhysicalDesign A B K)
    (hsite : ∀ j, E.geometry.site j = F.geometry.site j)
    (hκ : ∀ i, E.reactions.activeStrength i = F.reactions.activeStrength i) : E.cost = F.cost := by
  have he := E.state_eq_of_parameters F hsite hκ
  apply le_antisymm
  · obtain ⟨x, hx, hcost⟩ := E.cost_isGreatest.1
    rw [← hcost, he hx]
    exact F.cost_isGreatest.2 ⟨x, hx, rfl⟩
  · obtain ⟨x, hx, hcost⟩ := F.cost_isGreatest.1
    rw [← hcost, ← he hx]
    exact E.cost_isGreatest.2 ⟨x, hx, rfl⟩

theorem EndpointPhysicalDesign.state_eq_of_reconstruction_parameters (E : EndpointPhysicalDesign A B K)
    (Q : StrictPartition A.count)
    (hsite : ∀ j, E.geometry.site j = B.partitionSites Q (A.interiorCell j))
    (hκ : ∀ i, E.reactions.activeStrength i = B.endpointPartitionStrength A Q
      (A.root Q.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos)) i) :
    EqOn E.state (B.endpointPartitionState A Q
      (A.root Q.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos)))
      (Icc B.source.left B.source.right) := by
  apply E.state_eq_of_parameters (B.endpointPartitionDesign A Q E.reactions.budget_pos)
  · intro j
    exact (hsite j).trans (B.endpointPartitionGeometry_site A Q j).symm
  · intro i
    exact (hκ i).trans (B.endpointPartitionReactions_active A Q
      (A.root_spec Q.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos)).1
      (A.root_spec Q.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos)).2 i).symm

theorem EndpointPhysicalDesign.cost_eq_of_reconstruction_parameters (E : EndpointPhysicalDesign A B K)
    (Q : StrictPartition A.count)
    (hsite : ∀ j, E.geometry.site j = B.partitionSites Q (A.interiorCell j))
    (hκ : ∀ i, E.reactions.activeStrength i = B.endpointPartitionStrength A Q
      (A.root Q.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos)) i) :
    E.cost = A.root Q.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos) :=
  E.cost_eq_of_partition_state Q _ (E.state_eq_of_reconstruction_parameters Q hsite hκ)

theorem EndpointPhysicalDesign.optimal_iff_reconstruction_parameters (E : EndpointPhysicalDesign A B K) :
    E.Optimal ↔
      (∀ P : ClosedPartition A.count,
        A.root E.partition.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos) ≤
          A.root P B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos)) ∧
      (∀ j, E.geometry.site j = B.partitionSites E.partition (A.interiorCell j)) ∧
      (∀ i, E.reactions.activeStrength i = B.endpointPartitionStrength A E.partition
        (A.root E.partition.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos)) i) := by
  constructor
  · intro hE
    exact ⟨E.optimal_partition_minimal hE, E.optimal_interiorSites hE, E.optimal_activeStrength hE⟩
  · rintro ⟨hmin, hsite, hκ⟩
    exact E.optimal_iff_root_partition.mpr
      ⟨E.cost_eq_of_reconstruction_parameters E.partition hsite hκ, hmin⟩

theorem EndpointPhysicalDesign.optimal_iff_exists_reconstruction_parameters (E : EndpointPhysicalDesign A B K) :
    E.Optimal ↔ ∃ Q : StrictPartition A.count,
      (∀ P : ClosedPartition A.count,
        A.root Q.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos) ≤
          A.root P B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos)) ∧
      (∀ j, E.geometry.site j = B.partitionSites Q (A.interiorCell j)) ∧
      (∀ i, E.reactions.activeStrength i = B.endpointPartitionStrength A Q
        (A.root Q.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos)) i) := by
  constructor
  · intro hE
    exact ⟨E.partition, E.optimal_iff_reconstruction_parameters.mp hE⟩
  · rintro ⟨Q, hmin, hsite, hκ⟩ F
    rw [E.cost_eq_of_reconstruction_parameters Q hsite hκ]
    exact (hmin F.partition.closed).trans F.partition_root_bound

end TimeTraps.Interval
