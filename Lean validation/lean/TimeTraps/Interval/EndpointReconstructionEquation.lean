module

public import TimeTraps.Interval.EndpointReconstructionStrength
public import TimeTraps.Interval.EndpointReconstructionBoundary

@[expose] public section

/-! Verification of the original full-H1 endpoint equation for the
constructed physical state, followed by its actual essential norm. -/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators

theorem IntervalMedium.endpointPartitionFlux_tail (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (e : Fin (A.interiorCount + 1)) :
    B.endpointPartitionFlux A Q e 0 = B.source.mass *
      (Q.point (A.gapBoundary e) - B.source.coordinate ((B.endpointPartitionGeometry A Q).node e.castSucc)) := by
  simp only [endpointPartitionFlux, add_zero]

theorem IntervalMedium.endpointPartitionFlux_head (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (e : Fin (A.interiorCount + 1)) :
    B.endpointPartitionFlux A Q e ((B.endpointPartitionGeometry A Q).gapLength e) =
      B.source.mass * (Q.point (A.gapBoundary e) -
        B.source.coordinate ((B.endpointPartitionGeometry A Q).node e.succ)) := by
  simp only [endpointPartitionFlux, OrderedMedium.gapLength, add_sub_cancel]

theorem IntervalMedium.endpointPartitionFlux_jump (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (i : Fin A.interiorCount) :
    B.endpointPartitionFlux A Q i.succ 0 -
      B.endpointPartitionFlux A Q i.castSucc ((B.endpointPartitionGeometry A Q).gapLength i.castSucc) =
        B.source.mass * Q.width (A.interiorCell i) := by
  rw [B.endpointPartitionFlux_tail, B.endpointPartitionFlux_head]
  change B.source.mass * (Q.point (A.gapBoundary i.succ) -
      B.source.coordinate ((B.endpointPartitionGeometry A Q).site i)) -
    B.source.mass * (Q.point (A.gapBoundary i.castSucc) -
      B.source.coordinate ((B.endpointPartitionGeometry A Q).site i)) =
    B.source.mass * (Q.point (A.gapBoundary i.succ) - Q.point (A.gapBoundary i.castSucc))
  ring

theorem IntervalMedium.endpointPartition_graph_equation (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) {K M : ℝ}
    (hM : ∀ i, A.barrier Q.closed B.cellWeight i < M)
    (hroot : budget Finset.univ Q.width (A.barrier Q.closed B.cellWeight) M = K / B.source.mass) :
    GraphEquation (B.endpointPartitionGeometry A Q).graph
      (B.endpointPartitionReactions A Q hM hroot).nodal
      (fun v => B.endpointPartitionState A Q M ((B.endpointPartitionGeometry A Q).node v))
      ((B.endpointPartitionGeometry A Q).gapRestriction (B.endpointPartitionState A Q M))
      (B.endpointPartitionFlux A Q) := by
  refine ⟨B.endpointPartition_edge_equation A Q M, ?_, ?_, ?_⟩
  · intro e
    change B.endpointPartitionState A Q M ((B.endpointPartitionGeometry A Q).node e.castSucc + 0) = _
    rw [add_zero]
    rfl
  · intro e
    change B.endpointPartitionState A Q M ((B.endpointPartitionGeometry A Q).node e.castSucc +
      ((B.endpointPartitionGeometry A Q).node e.succ - (B.endpointPartitionGeometry A Q).node e.castSucc)) = _
    rw [add_sub_cancel]
    rfl
  · intro v
    change (B.endpointPartitionReactions A Q hM hroot).nodal v *
      B.endpointPartitionState A Q M ((B.endpointPartitionGeometry A Q).node v) =
        vertexFlux Fin.castSucc Fin.succ _ _ v
    rw [B.endpointPartitionReaction_nodal]
    refine Fin.cases ?_ (fun k => ?_) v
    · rw [A.activeLift_width_left, path_flux_first, B.endpointPartitionFlux_tail]
      change _ = B.source.mass * (Q.point (A.gapBoundary 0) -
        B.source.coordinate ((B.endpointPartitionGeometry A Q).node 0))
      rw [(B.endpointPartitionGeometry A Q).node_first]
      change _ = B.source.mass * (Q.point (A.gapBoundary 0) - B.source.coordinate B.source.left)
      rw [B.source.coordinate_left, sub_zero]
    · refine Fin.lastCases ?_ (fun i => ?_) k
      · change B.source.mass * A.activeLift Q.width (Fin.last (A.interiorCount + 1)) =
          vertexFlux Fin.castSucc Fin.succ _ _ (Fin.last (A.interiorCount + 1))
        rw [A.activeLift_width_right, path_flux_last]
        change B.source.mass * (1 - Q.point (A.gapBoundary (Fin.last A.interiorCount))) =
          -B.endpointPartitionFlux A Q (Fin.last A.interiorCount)
            ((B.endpointPartitionGeometry A Q).gapLength (Fin.last A.interiorCount))
        rw [B.endpointPartitionFlux_head]
        change _ = -(B.source.mass * (Q.point (A.gapBoundary (Fin.last A.interiorCount)) -
          B.source.coordinate ((B.endpointPartitionGeometry A Q).node (Fin.last (A.interiorCount + 1)))))
        rw [(B.endpointPartitionGeometry A Q).node_last]
        change _ = -(B.source.mass * (Q.point (A.gapBoundary (Fin.last A.interiorCount)) -
          B.source.coordinate B.source.right))
        rw [B.source.coordinate_right]
        ring
      · change B.source.mass * A.activeLift Q.width (trapNode i) =
          vertexFlux Fin.castSucc Fin.succ _ _ (trapNode i)
        rw [A.activeLift_interior, path_flux_trap]
        exact (B.endpointPartitionFlux_jump A Q i).symm

theorem IntervalMedium.endpointPartition_weak_equation (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) {K M : ℝ}
    (hM : ∀ i, A.barrier Q.closed B.cellWeight i < M)
    (hroot : budget Finset.univ Q.width (A.barrier Q.closed B.cellWeight) M = K / B.source.mass) :
    EndpointWeakEquation (B.endpointPartitionGeometry A Q) (B.endpointPartitionReactions A Q hM hroot)
      (B.endpointPartitionState A Q M) :=
  (B.endpointPartitionGeometry A Q).endpointWeak_of_strong (B.endpointPartition_graph_equation A Q hM hroot)

theorem IntervalMedium.endpointPartition_norm (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) {K M : ℝ}
    (hM : ∀ i, A.barrier Q.closed B.cellWeight i < M)
    (hroot : budget Finset.univ Q.width (A.barrier Q.closed B.cellWeight) M = K / B.source.mass) :
    (B.endpointPartitionGeometry A Q).essentialNorm (B.endpointPartitionState A Q M) = M := by
  have hm := (B.endpointPartition_weak_equation A Q hM hroot).essentialNorm_isGreatest
  apply le_antisymm
  · obtain ⟨x, hx, he⟩ := hm.1
    rw [← he]
    exact B.endpointPartitionState_le A Q M hx
  · apply hm.2
    exact ⟨B.source.inverse (Q.point (A.gapBoundary 0)), B.source.inverse_mem _,
      B.endpointPartitionState_boundary A Q M 0⟩

end TimeTraps.Interval
