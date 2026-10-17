module

public import TimeTraps.Interval.WeightedGridCompact
public import TimeTraps.Interval.WeightedCDFPosition

@[expose] public section

/-! The actual nearest-node cells of an ordered grid. Their boundaries are
consecutive grid midpoints, with fixed exterior boundaries 0 and 1. -/

namespace TimeTraps.Interval

open Set MeasureTheory
open scoped BigOperators

variable {n : ℕ}

noncomputable def ClosedPartition.canonicalMidpoint (Q : ClosedPartition n) (i : Fin n) : ℝ :=
  (Q.point i.castSucc + Q.point i.succ) / 2

noncomputable def ClosedPartition.canonicalCellNode (Q : ClosedPartition n) : Fin (n + 2) → ℝ :=
  cdfNode Q.canonicalMidpoint

theorem ClosedPartition.canonicalMidpoint_mem (Q : ClosedPartition n) (i : Fin n) :
    Q.canonicalMidpoint i ∈ Icc (0 : ℝ) 1 := by
  have hl := Q.point_mem i.castSucc
  have hr := Q.point_mem i.succ
  unfold canonicalMidpoint
  constructor <;> linarith [hl.1, hl.2, hr.1, hr.2]

theorem ClosedPartition.canonicalCellNode_mem (Q : ClosedPartition n) (e : Fin (n + 2)) :
    Q.canonicalCellNode e ∈ Icc (0 : ℝ) 1 :=
  cdfNode_mem Q.canonicalMidpoint Q.canonicalMidpoint_mem e

theorem ClosedPartition.canonicalCellNode_first (Q : ClosedPartition n) :
    Q.canonicalCellNode 0 = 0 := cdfNode_first _

theorem ClosedPartition.canonicalCellNode_last (Q : ClosedPartition n) :
    Q.canonicalCellNode (Fin.last (n + 1)) = 1 := cdfNode_last _

theorem ClosedPartition.canonicalCellNode_site (Q : ClosedPartition n) (i : Fin n) :
    Q.canonicalCellNode i.castSucc.succ = Q.canonicalMidpoint i := cdfNode_site _ i

theorem grid_midpoint_left_distance {a b z : ℝ} (hab : a ≤ b) (hz : z ≤ (a + b) / 2) :
    |z - a| ≤ |z - b| := by
  apply sq_le_sq.mp
  have hm := mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ a + b - 2 * z by linarith)
  nlinarith

theorem grid_midpoint_right_distance {a b z : ℝ} (hab : a ≤ b) (hz : (a + b) / 2 ≤ z) :
    |z - b| ≤ |z - a| := by
  apply sq_le_sq.mp
  have hm := mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ 2 * z - a - b by linarith)
  nlinarith

theorem ClosedPartition.canonicalCell_left_compare (Q : ClosedPartition n)
    (e k : Fin (n + 1)) {z : ℝ} (hk : k < e)
    (hz : Q.canonicalCellNode e.castSucc ≤ z) : |z - Q.point e| ≤ |z - Q.point k| := by
  revert k hz
  refine Fin.cases ?_ (fun i => ?_) e
  · intro k hk hz
    exact False.elim (not_lt_of_ge (Fin.zero_le k) hk)
  · intro k hk hz
    have hki : k ≤ i.castSucc := by change k.val ≤ i.val; change k.val < i.val + 1 at hk; omega
    have hq := Q.monotone hki
    have hqe := Q.monotone (Fin.castSucc_le_succ i)
    change Q.canonicalCellNode i.succ.castSucc ≤ z at hz
    rw [Fin.castSucc_succ, Q.canonicalCellNode_site] at hz
    unfold canonicalMidpoint at hz
    apply grid_midpoint_right_distance (hq.trans hqe)
    linarith

theorem ClosedPartition.canonicalCell_right_compare (Q : ClosedPartition n)
    (e k : Fin (n + 1)) {z : ℝ} (hk : e < k)
    (hz : z ≤ Q.canonicalCellNode e.succ) : |z - Q.point e| ≤ |z - Q.point k| := by
  revert k hz
  refine Fin.lastCases ?_ (fun i => ?_) e
  · intro k hk hz
    exact False.elim (not_lt_of_ge (Fin.le_last k) hk)
  · intro k hk hz
    have hik : i.succ ≤ k := by change i.val + 1 ≤ k.val; change i.val < k.val at hk; omega
    have hq := Q.monotone hik
    have hqe := Q.monotone (Fin.castSucc_le_succ i)
    rw [Q.canonicalCellNode_site] at hz
    unfold canonicalMidpoint at hz
    apply grid_midpoint_left_distance (hqe.trans hq)
    linarith

theorem ClosedPartition.gridDistance_on_canonicalCell (Q : ClosedPartition n)
    (e : Fin (n + 1)) {z : ℝ}
    (hz : z ∈ Icc (Q.canonicalCellNode e.castSucc) (Q.canonicalCellNode e.succ)) :
    gridDistance Q.point z = |z - Q.point e| := by
  apply le_antisymm (gridDistance_le Q.point z e)
  apply Finset.le_inf'
  intro k _
  rcases lt_trichotomy k e with hk | rfl | hk
  · exact Q.canonicalCell_left_compare e k hk hz.1
  · exact le_rfl
  · exact Q.canonicalCell_right_compare e k hk hz.2

theorem ClosedPartition.canonicalCell_order (Q : ClosedPartition n) (e : Fin (n + 1)) :
    Q.canonicalCellNode e.castSucc ≤ Q.point e ∧
      Q.point e ≤ Q.canonicalCellNode e.succ := by
  constructor
  · refine Fin.cases ?_ (fun i => ?_) e
    · simp [Q.canonicalCellNode_first, Q.first]
    · rw [Fin.castSucc_succ, Q.canonicalCellNode_site]
      unfold canonicalMidpoint
      have h := Q.monotone (Fin.castSucc_le_succ i)
      linarith
  · refine Fin.lastCases ?_ (fun i => ?_) e
    · change Q.point (Fin.last n) ≤ Q.canonicalCellNode (Fin.last (n + 1))
      rw [Q.last, Q.canonicalCellNode_last]
    · rw [Q.canonicalCellNode_site]
      unfold canonicalMidpoint
      have h := Q.monotone (Fin.castSucc_le_succ i)
      linarith

theorem ClosedPartition.gridCost_canonical_integral (Q : ClosedPartition n) (W : CellWeight) :
    Q.gridCost W = ∑ e : Fin (n + 1),
      ∫ z in Q.canonicalCellNode e.castSucc..Q.canonicalCellNode e.succ,
        W.value z * (Q.point e - z) ^ 2 := by
  let f : ℝ → ℝ := fun z => W.value z * gridDistance Q.point z ^ 2
  have hf : ContinuousOn f (Icc (0 : ℝ) 1) :=
    W.continuous.mul ((gridDistance_continuous Q.point).continuousOn.pow 2)
  have hi (a b : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
      IntervalIntegrable f volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply hf.mono
    intro t ht
    exact ⟨(le_min ha.1 hb.1).trans ht.1, ht.2.trans (max_le ha.2 hb.2)⟩
  let P (j : Fin (n + 2)) := ∫ z in (0 : ℝ)..Q.canonicalCellNode j, f z
  have ht (e : Fin (n + 1)) : P e.succ - P e.castSucc =
      ∫ z in Q.canonicalCellNode e.castSucc..Q.canonicalCellNode e.succ,
        W.value z * (Q.point e - z) ^ 2 := by
    rw [show P e.succ - P e.castSucc = ∫ z in Q.canonicalCellNode e.castSucc..
        Q.canonicalCellNode e.succ, f z from
      intervalIntegral.integral_interval_sub_left
        (hi _ _ ⟨le_rfl, zero_le_one⟩ (Q.canonicalCellNode_mem _))
        (hi _ _ ⟨le_rfl, zero_le_one⟩ (Q.canonicalCellNode_mem _))]
    apply intervalIntegral.integral_congr
    intro z hz
    have horder := Q.canonicalCell_order e
    have hz' : z ∈ Icc (Q.canonicalCellNode e.castSucc) (Q.canonicalCellNode e.succ) := by
      simpa only [uIcc_of_le (horder.1.trans horder.2)] using hz
    dsimp only [f]
    rw [Q.gridDistance_on_canonicalCell e hz', sq_abs, sub_sq_comm]
  have hs : (∑ e : Fin (n + 1), (P e.succ - P e.castSucc)) =
      P (Fin.last (n + 1)) - P 0 := by
    have hl := Fin.sum_univ_castSucc P
    have hr := Fin.sum_univ_succ P
    rw [Finset.sum_sub_distrib]
    linarith
  simp only [ht] at hs
  simpa only [P, f, ClosedPartition.gridCost, Q.canonicalCellNode_first, Q.canonicalCellNode_last,
    intervalIntegral.integral_same, sub_zero] using hs.symm

theorem StrictPartition.canonicalMidpoint_eq (Q : StrictPartition n) :
    Q.closed.canonicalMidpoint = weightedCDFMidpoint Q.width := by
  funext i
  exact (weightedCDFMidpoint_width Q i).symm

theorem StrictPartition.gridCost_eq_weightedCDFScore (Q : StrictPartition n) (W : CellWeight) :
    Q.closed.gridCost W = weightedCDFScore W Q.width (weightedCDFMidpoint Q.width) := by
  rw [Q.closed.gridCost_canonical_integral]
  simp only [weightedCDFScore, ClosedPartition.canonicalCellNode,
    Q.canonicalMidpoint_eq, Q.prefix_width]
  rfl

end TimeTraps.Interval
