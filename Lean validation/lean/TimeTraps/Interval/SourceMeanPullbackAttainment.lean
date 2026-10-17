module

public import TimeTraps.Interval.SourceMeanPullbackGraph

@[expose] public section

/-! Physical attainment from the effective unit-coordinate optimizer. The
assembled state satisfies the full H1 weak equation, and agrees pointwise
with the unit state composed with the physical source coordinate. -/

namespace TimeTraps.Interval

open Set TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators

variable {n : ℕ}

noncomputable def sourceMeanPullbackState (A : IntervalMedium) (D : OrderedMedium n)
    (hD : D.source = (homogeneous 1 1 zero_lt_one zero_lt_one).source)
    (U : Fin (n + 2) → ℝ) (u : Fin (n + 1) → ℝ → ℝ) : ℝ → ℝ :=
  (sourceMeanPullbackGeometry A D hD).assembledState U (sourceMeanPullbackEdgeState A D hD u)

theorem sourceMeanPullbackState_coordinate (A : IntervalMedium) (D : OrderedMedium n)
    (hD : D.source = (homogeneous 1 1 zero_lt_one zero_lt_one).source)
    (haD : D.conductance = sourceMeanConductance A)
    {κ : Fin n → ℝ} {U : Fin (n + 2) → ℝ} {u j : Fin (n + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph (nodalStrength κ) U u j) :
    EqOn (sourceMeanPullbackState A D hD U u)
      (fun x => D.assembledState U u (A.source.coordinate x)) (Icc A.source.left A.source.right) := by
  intro x hx
  let G := sourceMeanPullbackGeometry A D hD
  obtain ⟨e, he⟩ := G.gap_cover hx
  have ht : x - G.node e.castSucc ∈ Icc 0 (G.gapLength e) := by
    exact ⟨sub_nonneg.mpr he.1, sub_le_sub_right he.2 _⟩
  have hp := sourceMeanPullback_graph_equation A D hD haD h
  have hg := G.assembledState_gap hp.energy_membership e ht
  have hu := D.assembledState_gap h.energy_membership e
    (sourceMeanGapCoordinate_mem A D hD e ht)
  dsimp only [sourceMeanPullbackEdgeState, sourceMeanGapCoordinate, G] at hg hu
  simp only [add_sub_cancel] at hg hu
  exact hg.trans hu.symm

noncomputable def sourceMeanGridGeometry (A : IntervalMedium) (Q : StrictPartition n) : OrderedMedium n :=
  sourceMeanPullbackGeometry A
    (variableGridGeometry Q (sourceMeanConductance A) (sourceMeanConductance_continuous A)
      (sourceMeanConductance_pos A)) rfl

noncomputable def sourceMeanGridState (A : IntervalMedium) (Q : StrictPartition n) (K : ℝ) : ℝ → ℝ :=
  sourceMeanPullbackState A
    (variableGridGeometry Q (sourceMeanConductance A) (sourceMeanConductance_continuous A)
      (sourceMeanConductance_pos A)) rfl
    (variableGridNodal Q (sourceMeanConductance A) (sourceMeanConductance_continuous A)
      (sourceMeanConductance_pos A) (K / A.source.mass))
    (variableGridEdgeState Q (sourceMeanConductance A) (K / A.source.mass))

variable (A : IntervalMedium) (Q : StrictPartition n) (K : ℝ) (hK : 0 < K)
  (hmin : ∀ P : ClosedPartition n, Q.closed.gridCost A.cellWeight ≤ P.gridCost A.cellWeight)

include hK hmin in
theorem sourceMeanGrid_weak_equation :
    WeakIntervalEquation (sourceMeanGridGeometry A Q) (variableGridStrength Q K) (sourceMeanGridState A Q K) := by
  have hm : ∀ P : ClosedPartition n,
      Q.closed.gridCost (variableMeanWeight (sourceMeanConductance A) (sourceMeanConductance_continuous A)
        (sourceMeanConductance_pos A)) ≤ P.gridCost (variableMeanWeight (sourceMeanConductance A)
          (sourceMeanConductance_continuous A) (sourceMeanConductance_pos A)) := by
    rwa [sourceMeanConductance_weight]
  have hu := variableGrid_graph_equation Q (sourceMeanConductance A) (sourceMeanConductance_continuous A)
    (sourceMeanConductance_pos A) (K / A.source.mass) (div_pos hK A.source.mass_pos) hm
  have hp := sourceMeanPullback_weak_equation A _ rfl rfl hu
  have hk : (fun i => A.source.mass * variableGridStrength Q (K / A.source.mass) i) =
      variableGridStrength Q K := by
    funext i
    unfold variableGridStrength
    field_simp [ne_of_gt A.source.mass_pos]
  rw [hk] at hp
  exact hp

include hK hmin in
theorem sourceMeanGridState_trap (i : Fin n) :
    sourceMeanGridState A Q K ((sourceMeanGridGeometry A Q).site i) = A.source.mass / K := by
  have hm : ∀ P : ClosedPartition n,
      Q.closed.gridCost (variableMeanWeight (sourceMeanConductance A) (sourceMeanConductance_continuous A)
        (sourceMeanConductance_pos A)) ≤ P.gridCost (variableMeanWeight (sourceMeanConductance A)
          (sourceMeanConductance_continuous A) (sourceMeanConductance_pos A)) := by
    rwa [sourceMeanConductance_weight]
  have hu := variableGrid_graph_equation Q (sourceMeanConductance A) (sourceMeanConductance_continuous A)
    (sourceMeanConductance_pos A) (K / A.source.mass) (div_pos hK A.source.mass_pos) hm
  have hp := sourceMeanPullback_graph_equation A _ rfl rfl hu
  change (sourceMeanGridGeometry A Q).assembledState _ _
    ((sourceMeanGridGeometry A Q).node (trapNode i)) = _
  rw [(sourceMeanGridGeometry A Q).assembledState_node hp.energy_membership, variableGridNodal_trap]
  exact one_div_div _ _

noncomputable def sourceMeanDesign : IntervalDesign A n K where
  geometry := sourceMeanGridGeometry A Q
  medium_eq := rfl
  strength := variableGridStrength Q K
  strength_pos := variableGridStrength_pos Q hK
  strength_sum := variableGridStrength_sum Q K
  state := sourceMeanGridState A Q K
  equation := sourceMeanGrid_weak_equation A Q K hK hmin

theorem sourceMeanDesign_site (i : Fin n) :
    (sourceMeanDesign A Q K hK hmin).geometry.site i =
      A.source.inverse (weightedCDFMidpoint Q.width i) := by
  change A.source.inverse ((variableGridGeometry Q (sourceMeanConductance A)
    (sourceMeanConductance_continuous A) (sourceMeanConductance_pos A)).site i) = _
  rw [variableGridGeometry_site, Q.canonicalMidpoint_eq]

theorem sourceMeanDesign_strength (i : Fin n) :
    (sourceMeanDesign A Q K hK hmin).strength i = K * Q.width i := rfl

theorem sourceMeanDesign_width (i : Fin n) :
    (sourceMeanDesign A Q K hK hmin).partition.width i = Q.width i := by
  rw [IntervalDesign.source_share]
  change variableGridStrength Q K i * sourceMeanGridState A Q K ((sourceMeanGridGeometry A Q).site i) /
    A.source.mass = _
  rw [sourceMeanGridState_trap A Q K hK hmin]
  unfold variableGridStrength
  field_simp [ne_of_gt hK, ne_of_gt A.source.mass_pos]

theorem sourceMeanDesign_partition : (sourceMeanDesign A Q K hK hmin).partition = Q :=
  strictPartition_eq_of_width_eq _ Q (funext (sourceMeanDesign_width A Q K hK hmin))

theorem sourceMeanDesign_mean :
    (sourceMeanDesign A Q K hK hmin).sourceMeanCost = A.source.mass / K + Q.closed.gridCost A.cellWeight := by
  apply (source_mean_grid_eq_iff hK _ Q.closed hmin).mpr
  rw [sourceMeanDesign_partition]
  refine ⟨?_, sourceMeanDesign_site A Q K hK hmin, rfl⟩
  intro i
  rw [sourceMeanDesign_strength]
  exact (mul_div_cancel_left₀ _ (ne_of_gt hK)).symm

end TimeTraps.Interval
