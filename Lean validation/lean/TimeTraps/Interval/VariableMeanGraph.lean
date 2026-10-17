module

public import TimeTraps.Interval.VariableMeanEdges

@[expose] public section

/-! Exact nodal matching and vertex reactions for the variable-medium mean
construction. The interior head values use the checked centroid equations. -/

namespace TimeTraps.Interval

open Set TimeTraps.Analysis TimeTraps.Graph

variable {n : ℕ} (Q : StrictPartition n) (a : ℝ → ℝ)
  (ha : ContinuousOn a (Icc (0 : ℝ) 1))
  (hapos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < a x) (K : ℝ)

noncomputable def variableGridNodal : Fin (n + 2) → ℝ :=
  Fin.cons (variableGridEdgeState Q a K 0 0)
    (Fin.snoc (fun _ : Fin n => 1 / K)
      (variableGridEdgeState Q a K (Fin.last n)
        ((variableGridGeometry Q a ha hapos).gapLength (Fin.last n))))

theorem variableGridNodal_first :
    variableGridNodal Q a ha hapos K 0 = variableGridEdgeState Q a K 0 0 := by
  simp only [variableGridNodal, Fin.cons_zero]

theorem variableGridNodal_last :
    variableGridNodal Q a ha hapos K (Fin.last (n + 1)) =
      variableGridEdgeState Q a K (Fin.last n)
        ((variableGridGeometry Q a ha hapos).gapLength (Fin.last n)) := by
  change Fin.cons _ _ (Fin.last n).succ = _
  simp only [Fin.cons_succ, Fin.snoc_last]

theorem variableGridNodal_trap (i : Fin n) :
    variableGridNodal Q a ha hapos K (trapNode i) = 1 / K := by
  change Fin.cons _ _ i.castSucc.succ = _
  simp only [Fin.cons_succ, Fin.snoc_castSucc]

theorem variableGrid_nodal_tail (e : Fin (n + 1)) :
    variableGridEdgeState Q a K e 0 = variableGridNodal Q a ha hapos K e.castSucc := by
  refine Fin.cases ?_ (fun i => ?_) e
  · exact (variableGridNodal_first Q a ha hapos K).symm
  · rw [variableGridEdgeState_tail Q a K i.succ (Fin.succ_ne_zero i),
      Fin.castSucc_succ]
    exact (variableGridNodal_trap Q a ha hapos K i).symm

theorem variableGrid_nodal_head
    (hmin : ∀ P : ClosedPartition n, Q.closed.gridCost (variableMeanWeight a ha hapos) ≤
      P.gridCost (variableMeanWeight a ha hapos)) (e : Fin (n + 1)) :
    variableGridEdgeState Q a K e ((variableGridGeometry Q a ha hapos).gapLength e) =
      variableGridNodal Q a ha hapos K e.succ := by
  refine Fin.lastCases ?_ (fun i => ?_) e
  · exact (variableGridNodal_last Q a ha hapos K).symm
  · change variableGridEdgeState Q a K i.castSucc _ =
      variableGridNodal Q a ha hapos K (trapNode i)
    rw [variableGridNodal_trap]
    by_cases he : i.castSucc = 0
    · rw [he]
      exact variableGridEdgeState_first_head Q a ha hapos K
    · apply variableGridEdgeState_interior_head Q a ha hapos K hmin
      · have hv : i.val ≠ 0 := fun h => he (Fin.ext h)
        change 0 < i.val
        omega
      · exact i.isLt

theorem variableGridFlux_reflecting :
    variableGridFlux Q 0 0 = 0 ∧
      variableGridFlux Q (Fin.last n) ((variableGridGeometry Q a ha hapos).gapLength (Fin.last n)) = 0 := by
  constructor
  · rw [variableGridFlux_tail, Q.first]
    change 0 - Q.closed.canonicalCellNode 0 = 0
    rw [Q.closed.canonicalCellNode_first, sub_self]
  · rw [variableGridFlux_head, Q.last]
    change 1 - Q.closed.canonicalCellNode (Fin.last (n + 1)) = 0
    rw [Q.closed.canonicalCellNode_last, sub_self]

theorem variableGridFlux_jump (i : Fin n) :
    variableGridFlux Q i.succ 0 - variableGridFlux Q i.castSucc
      ((variableGridGeometry Q a ha hapos).gapLength i.castSucc) = Q.width i := by
  rw [variableGridFlux_tail, variableGridFlux_head]
  simp only [Fin.castSucc_succ, StrictPartition.width]
  ring

theorem variableGrid_graph_equation (hK : 0 < K)
    (hmin : ∀ P : ClosedPartition n, Q.closed.gridCost (variableMeanWeight a ha hapos) ≤
      P.gridCost (variableMeanWeight a ha hapos)) :
    GraphEquation (variableGridGeometry Q a ha hapos).graph
      (nodalStrength (variableGridStrength Q K)) (variableGridNodal Q a ha hapos K)
      (variableGridEdgeState Q a K) (variableGridFlux Q) := by
  refine ⟨variableGrid_edge_equation Q a ha hapos K,
    variableGrid_nodal_tail Q a ha hapos K,
    variableGrid_nodal_head Q a ha hapos K hmin, ?_⟩
  intro v
  change nodalStrength (variableGridStrength Q K) v * variableGridNodal Q a ha hapos K v =
    vertexFlux Fin.castSucc Fin.succ _ _ v
  refine Fin.cases ?_ (fun k => ?_) v
  · rw [nodalStrength_first, zero_mul, path_flux_first,
      (variableGridFlux_reflecting Q a ha hapos).1]
  · refine Fin.lastCases ?_ (fun i => ?_) k
    · change nodalStrength (variableGridStrength Q K) (Fin.last (n + 1)) * _ =
        vertexFlux Fin.castSucc Fin.succ _ _ (Fin.last (n + 1))
      rw [nodalStrength_last, zero_mul, path_flux_last]
      change 0 = -variableGridFlux Q (Fin.last n)
        ((variableGridGeometry Q a ha hapos).gapLength (Fin.last n))
      rw [(variableGridFlux_reflecting Q a ha hapos).2, neg_zero]
    · change nodalStrength (variableGridStrength Q K) (trapNode i) *
        variableGridNodal Q a ha hapos K (trapNode i) =
          vertexFlux Fin.castSucc Fin.succ _ _ (trapNode i)
      rw [nodalStrength_trap, variableGridNodal_trap, path_flux_trap,
        variableGridStrength_reaction Q (ne_of_gt hK)]
      exact (variableGridFlux_jump Q a ha hapos i).symm

end TimeTraps.Interval
