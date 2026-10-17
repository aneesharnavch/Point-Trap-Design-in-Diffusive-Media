module

public import TimeTraps.Interval.EndpointHomogeneousRoot
public import TimeTraps.Interval.EndpointHomogeneousSites
public import TimeTraps.Interval.UniformPartition

@[expose] public section

/-! The actual physical 2m+b minimax law and the unique homogeneous
absorption shares, active strengths, and interior positions. -/

namespace TimeTraps.Interval

open Set TimeTraps.Analysis

variable (A : EndpointArchitecture) {L D K : ℝ}

theorem endpoint_homogeneous_normalized_height (hL : 0 < L) (hD : 0 < D) (hK : 0 < K) :
    1 / (K / (homogeneous L D hL hD).source.mass) + (L ^ 2 / D) / (2 * A.sideTotal ^ 2) =
      L / K + L ^ 2 / (2 * D * A.sideTotal ^ 2) := by
  rw [homogeneous_mass]
  field_simp [ne_of_gt hL, ne_of_gt hD, ne_of_gt hK, ne_of_gt A.sideTotal_pos]

theorem endpoint_homogeneous_root (hL : 0 < L) (hD : 0 < D) (hK : 0 < K) :
    A.root A.homogeneousPartition.closed (homogeneous L D hL hD).cellWeight
      (div_pos hK (homogeneous L D hL hD).source.mass_pos) =
      L / K + L ^ 2 / (2 * D * A.sideTotal ^ 2) := by
  rw [A.homogeneousPartition_root _ (fun z _ => homogeneous_weight hL hD z)]
  exact endpoint_homogeneous_normalized_height A hL hD hK

theorem endpoint_homogeneous_barrier (hL : 0 < L) (hD : 0 < D) (i : Fin A.count) :
    A.barrier A.homogeneousPartition.closed (homogeneous L D hL hD).cellWeight i =
      L ^ 2 / (2 * D * A.sideTotal ^ 2) := by
  rw [A.homogeneousPartition_barrier _ (fun z _ => homogeneous_weight hL hD z)]
  ring

theorem endpoint_homogeneous_strength (hL : 0 < L) (hD : 0 < D) (hK : 0 < K) (i : Fin A.count) :
    (homogeneous L D hL hD).endpointPartitionStrength A A.homogeneousPartition
      (A.root A.homogeneousPartition.closed (homogeneous L D hL hD).cellWeight
        (div_pos hK (homogeneous L D hL hD).source.mass_pos)) i = K * A.homogeneousShare i := by
  unfold IntervalMedium.endpointPartitionStrength
  rw [endpoint_homogeneous_root A hL hD hK, endpoint_homogeneous_barrier A hL hD i,
    homogeneous_mass, add_sub_cancel_right]
  change L * A.homogeneousPartition.closed.width i / (L / K) = _
  rw [A.homogeneousPartition_width]
  field_simp [ne_of_gt hL, ne_of_gt hK]

theorem endpoint_homogeneous_construct_cost (hL : 0 < L) (hD : 0 < D) (hK : 0 < K) :
    ((homogeneous L D hL hD).endpointPartitionDesign A A.homogeneousPartition hK).cost =
      L / K + L ^ 2 / (2 * D * A.sideTotal ^ 2) := by
  rw [IntervalMedium.endpointPartitionDesign_cost]
  exact endpoint_homogeneous_root A hL hD hK

theorem endpoint_homogeneous_lower_bound (hL : 0 < L) (hD : 0 < D)
    (E : EndpointPhysicalDesign A (homogeneous L D hL hD) K) :
    L / K + L ^ 2 / (2 * D * A.sideTotal ^ 2) ≤ E.cost := by
  have h := A.constant_root_lower E.partition.closed (homogeneous L D hL hD).cellWeight
    (fun z _ => homogeneous_weight hL hD z)
    (div_pos E.reactions.budget_pos (homogeneous L D hL hD).source.mass_pos)
  rw [endpoint_homogeneous_normalized_height A hL hD E.reactions.budget_pos] at h
  exact h.trans E.partition_root_bound

theorem endpoint_homogeneous_minimum (hL : 0 < L) (hD : 0 < D) (hK : 0 < K) :
    IsLeast (range (fun E : EndpointPhysicalDesign A (homogeneous L D hL hD) K => E.cost))
      (L / K + L ^ 2 / (2 * D * A.sideTotal ^ 2)) := by
  refine ⟨⟨(homogeneous L D hL hD).endpointPartitionDesign A A.homogeneousPartition hK,
    endpoint_homogeneous_construct_cost A hL hD hK⟩, ?_⟩
  rintro M ⟨E, rfl⟩
  exact endpoint_homogeneous_lower_bound A hL hD E

theorem endpoint_homogeneous_optimal_partition (hL : 0 < L) (hD : 0 < D)
    (E : EndpointPhysicalDesign A (homogeneous L D hL hD) K) (hE : E.Optimal) :
    E.partition = A.homogeneousPartition := by
  have he := (A.constant_minimizer_iff E.partition.closed (homogeneous L D hL hD).cellWeight
    (fun z _ => homogeneous_weight hL hD z)
    (div_pos E.reactions.budget_pos (homogeneous L D hL hD).source.mass_pos)).mp
      (E.optimal_partition_minimal hE)
  apply E.partition.eq_of_point_eq
  exact congrArg ClosedPartition.point he

theorem endpoint_homogeneous_optimal_cost (hL : 0 < L) (hD : 0 < D)
    (E : EndpointPhysicalDesign A (homogeneous L D hL hD) K) (hE : E.Optimal) :
    E.cost = L / K + L ^ 2 / (2 * D * A.sideTotal ^ 2) := by
  rw [E.optimal_cost_eq_root hE, endpoint_homogeneous_optimal_partition A hL hD E hE]
  exact endpoint_homogeneous_root A hL hD E.reactions.budget_pos

theorem endpoint_homogeneous_optimal_shares (hL : 0 < L) (hD : 0 < D)
    (E : EndpointPhysicalDesign A (homogeneous L D hL hD) K) (hE : E.Optimal) (i : Fin A.count) :
    E.reactions.activeShare E.geometry E.state i = A.homogeneousShare i := by
  rw [← E.equation.partition_width]
  change E.partition.closed.width i = _
  rw [endpoint_homogeneous_optimal_partition A hL hD E hE, A.homogeneousPartition_width]

theorem endpoint_homogeneous_optimal_strengths (hL : 0 < L) (hD : 0 < D)
    (E : EndpointPhysicalDesign A (homogeneous L D hL hD) K) (hE : E.Optimal) (i : Fin A.count) :
    E.reactions.activeStrength i = K * A.homogeneousShare i := by
  rw [E.optimal_activeStrength hE, endpoint_homogeneous_optimal_partition A hL hD E hE]
  exact endpoint_homogeneous_strength A hL hD E.reactions.budget_pos i

theorem endpoint_homogeneous_optimal_sites (hL : 0 < L) (hD : 0 < D)
    (E : EndpointPhysicalDesign A (homogeneous L D hL hD) K) (hE : E.Optimal) (j : Fin A.interiorCount) :
    E.geometry.site j = L * ((A.leftReactive.toNat : ℝ) + 2 * (j.val : ℝ) + 1) / A.sideTotal := by
  rw [E.optimal_interiorSites hE, endpoint_homogeneous_optimal_partition A hL hD E hE]
  exact A.homogeneous_interior_sites hL hD j

theorem endpoint_homogeneous_optimal_site_values (hL : 0 < L) (hD : 0 < D)
    (E : EndpointPhysicalDesign A (homogeneous L D hL hD) K) (hE : E.Optimal) (i : Fin A.count) :
    E.state (A.physicalSite E.geometry i) = L / K := by
  rw [E.optimal_siteValues hE, endpoint_homogeneous_optimal_partition A hL hD E hE,
    endpoint_homogeneous_root A hL hD E.reactions.budget_pos, endpoint_homogeneous_barrier A hL hD i]
  ring

end TimeTraps.Interval
