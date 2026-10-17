module

public import TimeTraps.Interval.VariableMeanGeometry
public import TimeTraps.Interval.WeightedGridCentroid

@[expose] public section

/-! Exact integral edge states for the mean-optimal grid construction.
Each noninitial gap is anchored at its left trap; the initial gap is
anchored at its right trap. All trap anchors have the value 1/K. -/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph

variable {n : ℕ}

noncomputable def variableGridPrimitive (a : ℝ → ℝ) (q x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, (q - t) / a t

theorem variableGridPrimitive_continuous (a : ℝ → ℝ)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hapos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < a x) (q : ℝ) :
    ContinuousOn (variableGridPrimitive a q) (Icc (0 : ℝ) 1) :=
  integral_primitive_continuousOn zero_le_one
    ((continuousOn_const.sub continuousOn_id).div ha (fun x hx => ne_of_gt (hapos x hx)))

theorem variableGridPrimitive_derivative (a : ℝ → ℝ)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hapos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < a x) (q : ℝ) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (variableGridPrimitive a q) ((q - x) / a x) x :=
  integral_primitive_hasDerivAt
    ((continuousOn_const.sub continuousOn_id).div ha (fun x hx => ne_of_gt (hapos x hx))) hx

theorem variableGridPrimitive_sub (a : ℝ → ℝ)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hapos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < a x) (q : ℝ) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    variableGridPrimitive a q y - variableGridPrimitive a q x =
      ∫ t in x..y, (q - t) / a t := by
  have hi {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
      IntervalIntegrable (fun t => (q - t) / a t) volume 0 z :=
    (((continuousOn_const.sub continuousOn_id).div ha
      (fun x hx => ne_of_gt (hapos x hx))).mono
      (Icc_subset_Icc le_rfl hz.2)).intervalIntegrable_of_Icc hz.1
  exact intervalIntegral.integral_interval_sub_left (hi hy) (hi hx)

noncomputable def variableGridAnchor (Q : StrictPartition n) (e : Fin (n + 1)) : ℝ :=
  if e = 0 then Q.closed.canonicalCellNode e.succ else Q.closed.canonicalCellNode e.castSucc

noncomputable def variableGridEdgeState (Q : StrictPartition n) (a : ℝ → ℝ) (K : ℝ)
    (e : Fin (n + 1)) (t : ℝ) : ℝ :=
  1 / K + variableGridPrimitive a (Q.point e) (Q.closed.canonicalCellNode e.castSucc + t) -
    variableGridPrimitive a (Q.point e) (variableGridAnchor Q e)

noncomputable def variableGridFlux (Q : StrictPartition n) (e : Fin (n + 1)) (t : ℝ) : ℝ :=
  Q.point e - (Q.closed.canonicalCellNode e.castSucc + t)

theorem variableGrid_edge_equation (Q : StrictPartition n) (a : ℝ → ℝ)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hapos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < a x) (K : ℝ) (e : Fin (n + 1)) :
    EdgeEquation ((variableGridGeometry Q a ha hapos).graph.conductance e)
      ((variableGridGeometry Q a ha hapos).graph.source e)
      0 ((variableGridGeometry Q a ha hapos).gapLength e)
      (variableGridEdgeState Q a K e) (variableGridFlux Q e) := by
  let D := variableGridGeometry Q a ha hapos
  have hcont : ContinuousOn (fun t => variableGridPrimitive a (Q.point e)
      (Q.closed.canonicalCellNode e.castSucc + t)) (Icc 0 (D.gapLength e)) :=
    (variableGridPrimitive_continuous a ha hapos _).comp
      (continuous_const.add continuous_id).continuousOn (fun _ ht => D.gap_point_mem e ht)
  refine ⟨(continuousOn_const.add hcont).sub continuousOn_const, ?_, ?_, ?_⟩
  · exact continuousOn_const.sub (continuousOn_const.add continuousOn_id)
  · intro t ht
    have hx : D.node e.castSucc + t ∈ Ioo (0 : ℝ) 1 := D.gap_point_interior e ht
    have hd := ((variableGridPrimitive_derivative a ha hapos (Q.point e) hx).comp t
      ((hasDerivAt_id t).const_add (D.node e.castSucc))).const_add (1 / K)
    have he := hd.sub_const (variableGridPrimitive a (Q.point e) (variableGridAnchor Q e))
    change HasDerivAt (fun x => 1 / K + variableGridPrimitive a (Q.point e)
      (Q.closed.canonicalCellNode e.castSucc + x) -
        variableGridPrimitive a (Q.point e) (variableGridAnchor Q e))
      ((Q.point e - (Q.closed.canonicalCellNode e.castSucc + t)) /
        a (Q.closed.canonicalCellNode e.castSucc + t)) t
    simpa only [D, variableGridGeometry_node, mul_one, Function.comp_def] using he
  · intro t _
    have hd := ((hasDerivAt_id t).const_add (Q.closed.canonicalCellNode e.castSucc)).const_sub
      (Q.point e)
    change HasDerivAt (fun x => Q.point e - (Q.closed.canonicalCellNode e.castSucc + x)) (-1) t
    simpa only [id_eq] using hd

theorem variableGridEdgeState_tail (Q : StrictPartition n) (a : ℝ → ℝ) (K : ℝ)
    (e : Fin (n + 1)) (he : e ≠ 0) : variableGridEdgeState Q a K e 0 = 1 / K := by
  simp only [variableGridEdgeState, variableGridAnchor, if_neg he, add_zero, add_sub_cancel_right]

theorem variableGridEdgeState_first_head (Q : StrictPartition n) (a : ℝ → ℝ)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hapos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < a x) (K : ℝ) :
    variableGridEdgeState Q a K 0 ((variableGridGeometry Q a ha hapos).gapLength 0) = 1 / K := by
  simp [variableGridEdgeState, variableGridAnchor, OrderedMedium.gapLength, variableGridGeometry_node]

theorem variableGridEdgeState_interior_head (Q : StrictPartition n) (a : ℝ → ℝ)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hapos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < a x) (K : ℝ)
    (hmin : ∀ P : ClosedPartition n,
      Q.closed.gridCost (variableMeanWeight a ha hapos) ≤ P.gridCost (variableMeanWeight a ha hapos))
    (e : Fin (n + 1)) (he0 : 0 < e.val) (hen : e.val < n) :
    variableGridEdgeState Q a K e ((variableGridGeometry Q a ha hapos).gapLength e) = 1 / K := by
  have he : e ≠ 0 := by intro he; simp [he] at he0
  have hi := Q.grid_centroid_residual (variableMeanWeight a ha hapos) hmin e he0 hen
  have heq : (fun t => (variableMeanWeight a ha hapos).value t * (Q.point e - t)) =
      fun t => (Q.point e - t) / a t := by funext t; dsimp [variableMeanWeight]; ring
  rw [heq] at hi
  have hd := variableGridPrimitive_sub a ha hapos (Q.point e)
    (Q.closed.canonicalCellNode_mem e.castSucc) (Q.closed.canonicalCellNode_mem e.succ)
  rw [hi] at hd
  simp only [variableGridEdgeState, variableGridAnchor, if_neg he,
    OrderedMedium.gapLength, variableGridGeometry_node, add_sub_cancel]
  linarith

theorem variableGridFlux_tail (Q : StrictPartition n) (e : Fin (n + 1)) :
    variableGridFlux Q e 0 = Q.point e - Q.closed.canonicalCellNode e.castSucc := by
  simp only [variableGridFlux, add_zero]

theorem variableGridFlux_head (Q : StrictPartition n) (a : ℝ → ℝ)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hapos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < a x) (e : Fin (n + 1)) :
    variableGridFlux Q e ((variableGridGeometry Q a ha hapos).gapLength e) =
      Q.point e - Q.closed.canonicalCellNode e.succ := by
  simp only [variableGridFlux, OrderedMedium.gapLength, variableGridGeometry_node, add_sub_cancel]

end TimeTraps.Interval
