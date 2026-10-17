module

public import TimeTraps.Interval.VariableMeanGraph
public import TimeTraps.Interval.VariableMeanDeficit

@[expose] public section

/-! A minimizing weighted grid gives an actual physical weak design with
the prescribed sites, strengths and absorption shares, attaining the sharp
mean value. The physical state is assembled from the proved edge solutions. -/

namespace TimeTraps.Interval

open Set TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators

variable {n : ℕ} (Q : StrictPartition n) (a : ℝ → ℝ)
  (ha : ContinuousOn a (Icc (0 : ℝ) 1))
  (hapos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < a x) (K : ℝ)

noncomputable def variableGridState : ℝ → ℝ :=
  (variableGridGeometry Q a ha hapos).assembledState (variableGridNodal Q a ha hapos K)
    (variableGridEdgeState Q a K)

variable (hK : 0 < K)
  (hmin : ∀ P : ClosedPartition n, Q.closed.gridCost (variableMeanWeight a ha hapos) ≤
    P.gridCost (variableMeanWeight a ha hapos))

include hK hmin in
theorem variableGrid_weak_equation :
    WeakIntervalEquation (variableGridGeometry Q a ha hapos) (variableGridStrength Q K)
      (variableGridState Q a ha hapos K) :=
  (variableGridGeometry Q a ha hapos).assembledState_weak
    (variableGrid_graph_equation Q a ha hapos K hK hmin)

include hK hmin in
theorem variableGridState_trap (i : Fin n) :
    variableGridState Q a ha hapos K ((variableGridGeometry Q a ha hapos).site i) = 1 / K := by
  change (variableGridGeometry Q a ha hapos).assembledState _ _
    ((variableGridGeometry Q a ha hapos).node (trapNode i)) = _
  rw [(variableGridGeometry Q a ha hapos).assembledState_node
    (variableGrid_graph_equation Q a ha hapos K hK hmin).energy_membership,
    variableGridNodal_trap]

include hK hmin in
theorem variableGridState_gap (e : Fin (n + 1)) {t : ℝ}
    (ht : t ∈ Icc 0 ((variableGridGeometry Q a ha hapos).gapLength e)) :
    variableGridState Q a ha hapos K ((variableGridGeometry Q a ha hapos).node e.castSucc + t) =
      variableGridEdgeState Q a K e t :=
  (variableGridGeometry Q a ha hapos).assembledState_gap
    (variableGrid_graph_equation Q a ha hapos K hK hmin).energy_membership e ht

noncomputable def variableMeanDesign : IntervalDesign (variableUnitMedium a ha hapos) n K where
  geometry := variableGridGeometry Q a ha hapos
  medium_eq := rfl
  strength := variableGridStrength Q K
  strength_pos := variableGridStrength_pos Q hK
  strength_sum := variableGridStrength_sum Q K
  state := variableGridState Q a ha hapos K
  equation := variableGrid_weak_equation Q a ha hapos K hK hmin

theorem variableMeanDesign_site (i : Fin n) :
    (variableMeanDesign Q a ha hapos K hK hmin).geometry.site i = Q.closed.canonicalMidpoint i :=
  variableGridGeometry_site Q a ha hapos i

theorem variableMeanDesign_strength (i : Fin n) :
    (variableMeanDesign Q a ha hapos K hK hmin).strength i = K * Q.width i := rfl

theorem variableMeanDesign_width (i : Fin n) :
    (variableMeanDesign Q a ha hapos K hK hmin).partition.width i = Q.width i := by
  rw [IntervalDesign.variable_share]
  change variableGridStrength Q K i *
    variableGridState Q a ha hapos K ((variableGridGeometry Q a ha hapos).site i) = _
  rw [variableGridState_trap Q a ha hapos K hK hmin,
    variableGridStrength_reaction Q (ne_of_gt hK)]

theorem strictPartition_eq_of_width_eq {m : ℕ} (P R : StrictPartition m)
    (hw : P.width = R.width) : P = R := by
  have hp : P.point = R.point := by
    funext e
    rw [← P.prefix_width e, hw, R.prefix_width]
  cases P
  cases R
  cases hp
  rfl

theorem variableMeanDesign_partition :
    (variableMeanDesign Q a ha hapos K hK hmin).partition = Q :=
  strictPartition_eq_of_width_eq _ Q (funext (variableMeanDesign_width Q a ha hapos K hK hmin))

theorem variableMeanDesign_mean :
    (variableMeanDesign Q a ha hapos K hK hmin).meanCost =
      1 / K + Q.closed.gridCost (variableMeanWeight a ha hapos) := by
  rw [variable_mean_energy, variableMeanDesign_partition]
  change (∑ i, Q.width i ^ 2 / (K * Q.width i)) +
    weightedCDFScore (variableMeanWeight a ha hapos) Q.width
      (variableGridGeometry Q a ha hapos).site = _
  have hx : (variableGridGeometry Q a ha hapos).site = weightedCDFMidpoint Q.width := by
    funext i
    rw [variableGridGeometry_site, Q.canonicalMidpoint_eq]
  rw [hx, ← Q.gridCost_eq_weightedCDFScore]
  have hr : (∑ i, Q.width i ^ 2 / (K * Q.width i)) = 1 / K := by
    calc
      _ = ∑ i, Q.width i / K := by
        apply Finset.sum_congr rfl
        intro i _
        field_simp [ne_of_gt hK, ne_of_gt (Q.width_pos i)]
      _ = _ := by rw [← Finset.sum_div, Q.width_sum]
  rw [hr]

end TimeTraps.Interval
