module

public import TimeTraps.Interval.WeightedGridCells
public import TimeTraps.Interval.PartitionMove

@[expose] public section

/-! Fixed-cell comparison with arbitrary candidate grids. The independent
nearest-grid cost is bounded above by assigning each old cell to its indexed
candidate node. This permits variational arguments without moving boundaries. -/

namespace TimeTraps.Interval

open Set MeasureTheory
open scoped BigOperators

variable {n : ℕ}

noncomputable def ClosedPartition.assignedGridCost (Q P : ClosedPartition n) (W : CellWeight) : ℝ :=
  ∑ e : Fin (n + 1), ∫ z in Q.canonicalCellNode e.castSucc..Q.canonicalCellNode e.succ,
    W.value z * (P.point e - z) ^ 2

theorem ClosedPartition.canonical_integral_sum (Q : ClosedPartition n) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) :
    (∑ e : Fin (n + 1), ∫ z in Q.canonicalCellNode e.castSucc..Q.canonicalCellNode e.succ,
      f z) = ∫ z in (0 : ℝ)..1, f z := by
  have hi (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : IntervalIntegrable f volume 0 t := by
    apply ContinuousOn.intervalIntegrable_of_Icc ht.1
    exact hf.mono (Icc_subset_Icc le_rfl ht.2)
  let F (e : Fin (n + 2)) := ∫ z in (0 : ℝ)..Q.canonicalCellNode e, f z
  have he (e : Fin (n + 1)) :
      (∫ z in Q.canonicalCellNode e.castSucc..Q.canonicalCellNode e.succ, f z) =
        F e.succ - F e.castSucc :=
    (intervalIntegral.integral_interval_sub_left
      (hi _ (Q.canonicalCellNode_mem _)) (hi _ (Q.canonicalCellNode_mem _))).symm
  simp_rw [he]
  rw [Finset.sum_sub_distrib]
  have hl := Fin.sum_univ_castSucc F
  have hr := Fin.sum_univ_succ F
  have hend : F (Fin.last (n + 1)) = ∫ z in (0 : ℝ)..1, f z := by
    simp only [F, Q.canonicalCellNode_last]
  have hzero : F 0 = 0 := by simp only [F, Q.canonicalCellNode_first, intervalIntegral.integral_same]
  linarith

theorem ClosedPartition.assignedGridCost_self (Q : ClosedPartition n) (W : CellWeight) :
    Q.assignedGridCost Q W = Q.gridCost W := (Q.gridCost_canonical_integral W).symm

theorem ClosedPartition.gridCost_le_assigned (Q P : ClosedPartition n) (W : CellWeight) :
    P.gridCost W ≤ Q.assignedGridCost P W := by
  have hf : ContinuousOn (fun z => W.value z * gridDistance P.point z ^ 2) (Icc (0 : ℝ) 1) :=
    W.continuous.mul ((gridDistance_continuous P.point).continuousOn.pow 2)
  rw [ClosedPartition.gridCost, ← Q.canonical_integral_sum hf]
  apply Finset.sum_le_sum
  intro e _
  have hl := Q.canonicalCellNode_mem e.castSucc
  have hr := Q.canonicalCellNode_mem e.succ
  have hord := (Q.canonicalCell_order e).1.trans (Q.canonicalCell_order e).2
  apply intervalIntegral.integral_mono_on hord
  · apply ContinuousOn.intervalIntegrable_of_Icc hord
    exact hf.mono (Icc_subset_Icc hl.1 hr.2)
  · exact weightedCDF_integrable W _ hl hr
  · intro z hz
    have hz' : z ∈ Icc (0 : ℝ) 1 := ⟨hl.1.trans hz.1, hz.2.trans hr.2⟩
    apply mul_le_mul_of_nonneg_left _ (W.positive z hz').le
    have hd := gridDistance_le P.point z e
    have hs := pow_le_pow_left₀ (gridDistance_nonneg P.point z) hd 2
    simpa only [sq_abs, sub_sq_comm] using hs

theorem ClosedPartition.assignedGridCost_move_difference (Q : ClosedPartition (n + 1))
    (W : CellWeight) (i : Fin n) (c : ℝ)
    (hc : c ∈ Icc (Q.point i.castSucc.castSucc) (Q.point i.succ.succ)) :
    Q.assignedGridCost (Q.move i c hc) W - Q.gridCost W =
      (∫ z in Q.canonicalCellNode i.castSucc.succ.castSucc..
        Q.canonicalCellNode i.castSucc.succ.succ, W.value z * (c - z) ^ 2) -
      ∫ z in Q.canonicalCellNode i.castSucc.succ.castSucc..
        Q.canonicalCellNode i.castSucc.succ.succ, W.value z * (Q.point i.castSucc.succ - z) ^ 2 := by
  rw [← Q.assignedGridCost_self W]
  unfold assignedGridCost
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i.castSucc.succ]
  · rw [Q.move_middle]
  · intro e _ he
    rw [Q.move_other i c hc e he, sub_self]
  · simp

end TimeTraps.Interval
