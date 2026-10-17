module

public import TimeTraps.Interval.WeightedGridCompact
public import TimeTraps.Interval.PartitionMove

@[expose] public section

/-! A redundant interior copy of a grid node can be moved inside its adjacent
positive gap. All old distinct nodes remain available, and the new node
strictly lowers the true weighted distance integral. -/

namespace TimeTraps.Interval

open Set MeasureTheory

variable {n : ℕ}

theorem ClosedPartition.move_preserves_grid (Q : ClosedPartition (n + 1)) (i : Fin n)
    (hm : Q.point i.castSucc.succ = Q.point i.castSucc.castSucc ∨
      Q.point i.castSucc.succ = Q.point i.succ.succ) {c : ℝ}
    (hc : c ∈ Icc (Q.point i.castSucc.castSucc) (Q.point i.succ.succ)) :
    ∀ j, ∃ k, (Q.move i c hc).point k = Q.point j := by
  intro j
  by_cases hj : j = i.castSucc.succ
  · subst j
    rcases hm with hm | hm
    · exact ⟨i.castSucc.castSucc, (Q.move_left i c hc).trans hm.symm⟩
    · exact ⟨i.succ.succ, (Q.move_right i c hc).trans hm.symm⟩
  · exact ⟨j, Q.move_other i c hc j hj⟩

theorem ClosedPartition.move_gridDistance_le (Q : ClosedPartition (n + 1)) (i : Fin n)
    (hm : Q.point i.castSucc.succ = Q.point i.castSucc.castSucc ∨
      Q.point i.castSucc.succ = Q.point i.succ.succ) {c : ℝ}
    (hc : c ∈ Icc (Q.point i.castSucc.castSucc) (Q.point i.succ.succ)) (x : ℝ) :
    gridDistance (Q.move i c hc).point x ≤ gridDistance Q.point x := by
  obtain ⟨j, hj⟩ := gridDistance_attained Q.point x
  obtain ⟨k, hk⟩ := Q.move_preserves_grid i hm hc j
  calc
    _ ≤ |x - (Q.move i c hc).point k| := gridDistance_le _ x k
    _ = gridDistance Q.point x := by rw [hk, hj]

theorem ClosedPartition.moved_point_not_in_grid (Q : ClosedPartition (n + 1)) (i : Fin n)
    (hm : Q.point i.castSucc.succ = Q.point i.castSucc.castSucc ∨
      Q.point i.castSucc.succ = Q.point i.succ.succ) {c : ℝ}
    (hc : c ∈ Ioo (Q.point i.castSucc.castSucc) (Q.point i.succ.succ)) :
    ∀ j, c ≠ Q.point j := by
  intro j
  by_cases hj : j = i.castSucc.succ
  · subst j
    rcases hm with hm | hm
    · rw [hm]; exact ne_of_gt hc.1
    · rw [hm]; exact ne_of_lt hc.2
  · rcases lt_or_gt_of_ne hj with hlt | hgt
    · have hj' : j ≤ i.castSucc.castSucc := by
        change j.val ≤ i.val
        change j.val < i.val + 1 at hlt
        omega
      exact ne_of_gt ((Q.monotone hj').trans_lt hc.1)
    · have hj' : i.succ.succ ≤ j := by
        change i.val + 1 + 1 ≤ j.val
        change i.val + 1 < j.val at hgt
        omega
      exact ne_of_lt (hc.2.trans_le (Q.monotone hj'))

theorem ClosedPartition.move_gridCost_lt (Q : ClosedPartition (n + 1)) (W : CellWeight)
    (i : Fin n)
    (hm : Q.point i.castSucc.succ = Q.point i.castSucc.castSucc ∨
      Q.point i.castSucc.succ = Q.point i.succ.succ) {c : ℝ}
    (hc : c ∈ Ioo (Q.point i.castSucc.castSucc) (Q.point i.succ.succ)) :
    (Q.move i c (Ioo_subset_Icc_self hc)).gridCost W < Q.gridCost W := by
  let P := Q.move i c (Ioo_subset_Icc_self hc)
  have hcont (R : ClosedPartition (n + 1)) :
      ContinuousOn (fun x => W.value x * gridDistance R.point x ^ 2) (Icc 0 1) := by
    intro x hx
    exact (W.continuous x hx).mul
      ((gridDistance_continuous R.point).continuousAt.continuousWithinAt.pow 2)
  have hcunit : c ∈ Icc (0 : ℝ) 1 :=
    ⟨(Q.point_mem _).1.trans hc.1.le, hc.2.le.trans (Q.point_mem _).2⟩
  have hz : gridDistance P.point c = 0 := by
    have he := gridDistance_at_node P.point i.castSucc.succ
    simpa only [P, Q.move_middle] using he
  have hp : 0 < gridDistance Q.point c := by
    obtain ⟨j, hj⟩ := gridDistance_attained Q.point c
    rw [hj]
    exact abs_pos.mpr (sub_ne_zero.mpr (Q.moved_point_not_in_grid i hm hc j))
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    zero_lt_one (hcont P) (hcont Q)
  · intro x hx
    have hd := Q.move_gridDistance_le i hm (Ioo_subset_Icc_self hc) x
    exact mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (gridDistance_nonneg P.point x) (gridDistance_nonneg Q.point x)).mpr hd)
      (W.positive x ⟨hx.1.le, hx.2⟩).le
  · refine ⟨c, hcunit, ?_⟩
    rw [hz, zero_pow (by decide : 2 ≠ 0), mul_zero]
    exact mul_pos (W.positive c hcunit) (sq_pos_of_pos hp)

end TimeTraps.Interval
