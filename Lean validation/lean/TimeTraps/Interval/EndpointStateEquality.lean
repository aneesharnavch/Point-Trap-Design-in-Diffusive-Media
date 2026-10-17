module

public import TimeTraps.Interval.EndpointHeightEquality

@[expose] public section

/-! Equality identifies the complete analytic physical profile. The
argument integrates the actual transformed flux and fixes its additive
constant at a proved maximum; no equality of proof fields is required. -/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {A : EndpointArchitecture} {K : ℝ}

theorem EndpointWeakEquation.mixed_budget_equality_CDF {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w)
    (hb : budget Finset.univ (R.activeShare D w) (A.barrier hw.partition.closed D.medium.cellWeight)
      (D.essentialNorm w) = K / D.source.mass) :
    R.activeCDF D w = A.reconstructionCDF hw.partition D.medium.cellWeight := by
  funext z
  apply Finset.sum_congr rfl
  intro i _
  rw [hw.mixed_budget_equality_sites hb i]
  change (if _ then R.activeShare D w i else 0) = (if _ then hw.partition.closed.width i else 0)
  rw [hw.partition_width]

theorem EndpointWeakEquation.mixed_budget_equality_slope {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w)
    (hb : budget Finset.univ (R.activeShare D w) (A.barrier hw.partition.closed D.medium.cellWeight)
      (D.essentialNorm w) = K / D.source.mass) :
    R.activeSlope D w = D.medium.endpointPartitionSlope A hw.partition := by
  funext z
  unfold EndpointReactions.activeSlope IntervalMedium.endpointPartitionSlope
  rw [hw.mixed_budget_equality_CDF hb]
  rfl

theorem EndpointWeakEquation.transformed_difference {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    D.source.transformed w b - D.source.transformed w a = ∫ t in a..b, R.activeSlope D w t := by
  rcases le_total a b with hab | hba
  · exact (hw.transformed_integral ha.1 hb.2 hab).symm
  · rw [intervalIntegral.integral_symm, hw.transformed_integral hb.1 ha.2 hba]
    ring

theorem EndpointWeakEquation.mixed_budget_equality_transformed {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w)
    (hb : budget Finset.univ (R.activeShare D w) (A.barrier hw.partition.closed D.medium.cellWeight)
      (D.essentialNorm w) = K / D.source.mass) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    D.source.transformed w z = D.medium.endpointPartitionProfile A hw.partition (D.essentialNorm w) z := by
  have he := hw.transformed_difference (hw.partition.point_mem (A.gapBoundary 0)) hz
  rw [hw.mixed_budget_equality_slope hb, hw.mixed_budget_equality_anchor hb] at he
  unfold IntervalMedium.endpointPartitionProfile
  linarith

theorem EndpointWeakEquation.mixed_budget_equality_state {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w)
    (hb : budget Finset.univ (R.activeShare D w) (A.barrier hw.partition.closed D.medium.cellWeight)
      (D.essentialNorm w) = K / D.source.mass) :
    EqOn w (D.medium.endpointPartitionState A hw.partition (D.essentialNorm w))
      (Icc D.source.left D.source.right) := by
  intro x hx
  have he := hw.mixed_budget_equality_transformed hb (D.source.coordinate_mem hx)
  rw [D.source.transformed_coordinate w hx] at he
  exact he

theorem EndpointWeakEquation.mixed_budget_equality_boundaries {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w)
    (hb : budget Finset.univ (R.activeShare D w) (A.barrier hw.partition.closed D.medium.cellWeight)
      (D.essentialNorm w) = K / D.source.mass) (e : Fin (A.interiorCount + 1)) :
    D.source.transformed w (hw.partition.point (A.gapBoundary e)) = D.essentialNorm w := by
  rw [hw.mixed_budget_equality_transformed hb (hw.partition.point_mem _),
    D.medium.endpointPartitionProfile_boundary]

theorem EndpointWeakEquation.mixed_budget_equality_physicalSites {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w)
    (hb : budget Finset.univ (R.activeShare D w) (A.barrier hw.partition.closed D.medium.cellWeight)
      (D.essentialNorm w) = K / D.source.mass) (i : Fin A.count) :
    A.physicalSite D i = D.source.inverse (A.reconstructionSite hw.partition D.medium.cellWeight i) := by
  rw [← hw.mixed_budget_equality_sites hb i]
  exact (D.source.inverse_coordinate (A.physicalSite_mem D i)).symm

theorem EndpointWeakEquation.mixed_budget_equality_interiorSites {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w)
    (hb : budget Finset.univ (R.activeShare D w) (A.barrier hw.partition.closed D.medium.cellWeight)
      (D.essentialNorm w) = K / D.source.mass) (j : Fin A.interiorCount) :
    D.site j = D.medium.partitionSites hw.partition (A.interiorCell j) := by
  have he := hw.mixed_budget_equality_physicalSites hb (A.interiorCell j)
  rw [A.reconstructionSite_ordinary _ _ _ (A.kind_interiorCell j)] at he
  change D.site j = D.source.inverse (hw.partition.center D.medium.cellWeight (A.interiorCell j))
  simpa only [EndpointArchitecture.physicalSite, A.activeNode_interior, OrderedMedium.site] using he

theorem EndpointPhysicalDesign.cost_eq_of_partition_state {B : IntervalMedium}
    (E : EndpointPhysicalDesign A B K) (Q : StrictPartition A.count) (M : ℝ)
    (he : EqOn E.state (B.endpointPartitionState A Q M) (Icc B.source.left B.source.right)) :
    E.cost = M := by
  have hm := E.cost_isGreatest
  apply le_antisymm
  · obtain ⟨x, hx, hxM⟩ := hm.1
    rw [← hxM, he hx]
    exact B.endpointPartitionState_le A Q M hx
  · apply hm.2
    refine ⟨B.source.inverse (Q.point (A.gapBoundary 0)), B.source.inverse_mem _, ?_⟩
    rw [he (B.source.inverse_mem _), B.endpointPartitionState_boundary]

end TimeTraps.Interval
