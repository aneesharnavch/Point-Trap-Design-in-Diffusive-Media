module

public import TimeTraps.Interval.WeightedGridCells
public import TimeTraps.Interval.CDFDeficit
public import TimeTraps.Interval.UniformPartition

@[expose] public section

/-! Exact constant-weight grid cost, attained minimum, and unique uniform
grid. The formula also includes closed grids with repeated nodes. -/

namespace TimeTraps.Interval

open Set MeasureTheory
open scoped BigOperators

variable {n : ℕ}

theorem ClosedPartition.prefix_width (Q : ClosedPartition n) (e : Fin (n + 1)) :
    absorptionPrefix Q.width e = Q.point e := by
  induction e using Fin.induction with
  | zero => rw [absorptionPrefix_zero, Q.first]
  | succ i ih => rw [absorptionPrefix_succ, ih]; unfold ClosedPartition.width; ring

theorem ClosedPartition.canonicalMidpoint_eq (Q : ClosedPartition n) :
    Q.canonicalMidpoint = weightedCDFMidpoint Q.width := by
  funext i
  simp only [canonicalMidpoint, weightedCDFMidpoint, Q.prefix_width]

theorem ClosedPartition.gridCost_eq_weightedCDFScore (Q : ClosedPartition n) (W : CellWeight) :
    Q.gridCost W = weightedCDFScore W Q.width (weightedCDFMidpoint Q.width) := by
  rw [Q.gridCost_canonical_integral]
  simp only [weightedCDFScore, canonicalCellNode, Q.canonicalMidpoint_eq, Q.prefix_width]

theorem weightedCDFScore_constant (W : CellWeight) {C : ℝ}
    (hW : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) (p x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
    weightedCDFScore W p x = C * cdfSquareScore p x := by
  unfold weightedCDFScore cdfSquareScore
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro z hz
  have hl := cdfNode_mem x hx e.castSucc
  have hr := cdfNode_mem x hx e.succ
  dsimp only
  rw [hW z ⟨(le_min hl.1 hr.1).trans hz.1, hz.2.trans (max_le hl.2 hr.2)⟩]

theorem ClosedPartition.gridCost_constant (Q : ClosedPartition n) (W : CellWeight) {C : ℝ}
    (hW : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) :
    Q.gridCost W = (C / 12) * ∑ i, Q.width i ^ 3 := by
  rw [Q.gridCost_eq_weightedCDFScore, weightedCDFScore_constant W hW Q.width _
    (fun i => by rw [← Q.canonicalMidpoint_eq]; exact Q.canonicalMidpoint_mem i),
    cdfSquareScore_identity Q.width _ Q.width_sum]
  simp only [weightedCDFMidpoint, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero,
    ← Finset.sum_div]
  ring

theorem ClosedPartition.constant_grid_deficit (Q : ClosedPartition n) (W : CellWeight) {C : ℝ}
    (hW : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) :
    Q.gridCost W - C / (12 * (n : ℝ) ^ 2) = (C / 12) * meanShareLoss Q.width := by
  rw [Q.gridCost_constant W hW, meanShareLoss_identity Q.width Q.size_pos Q.width_sum]
  ring

theorem ClosedPartition.constant_grid_lower (Q : ClosedPartition n) (W : CellWeight) {C : ℝ}
    (hC : 0 ≤ C) (hW : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) :
    C / (12 * (n : ℝ) ^ 2) ≤ Q.gridCost W := by
  have h := Q.constant_grid_deficit W hW
  have hp := mul_nonneg (div_nonneg hC (by norm_num : (0 : ℝ) ≤ 12))
    (meanShareLoss_nonneg Q.width Q.width_nonneg)
  linarith

theorem ClosedPartition.constant_grid_eq_iff_width (Q : ClosedPartition n) (W : CellWeight)
    {C : ℝ} (hC : 0 < C) (hW : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) :
    Q.gridCost W = C / (12 * (n : ℝ) ^ 2) ↔ ∀ i, Q.width i = 1 / (n : ℝ) := by
  have hc : C / 12 ≠ 0 := ne_of_gt (div_pos hC (by norm_num))
  rw [← meanShareLoss_eq_zero_iff Q.width Q.size_pos Q.width_nonneg]
  have h := Q.constant_grid_deficit W hW
  constructor
  · intro he
    rw [he, sub_self] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hc
  · intro he
    rw [he, mul_zero] at h
    exact sub_eq_zero.mp h

theorem StrictPartition.uniform_gridCost_constant (W : CellWeight) (hn : 0 < n)
    {C : ℝ} (hC : 0 < C) (hW : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) :
    (StrictPartition.uniform n hn).closed.gridCost W = C / (12 * (n : ℝ) ^ 2) := by
  apply ((StrictPartition.uniform n hn).closed.constant_grid_eq_iff_width W hC hW).mpr
  intro i
  exact StrictPartition.uniform_width hn i

theorem ClosedPartition.constant_grid_minimizer_iff (Q : ClosedPartition n) (W : CellWeight)
    {C : ℝ} (hC : 0 < C) (hW : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) :
    (∀ P : ClosedPartition n, Q.gridCost W ≤ P.gridCost W) ↔
      Q = (StrictPartition.uniform n Q.size_pos).closed := by
  constructor
  · intro hmin
    have hu := hmin (StrictPartition.uniform n Q.size_pos).closed
    rw [StrictPartition.uniform_gridCost_constant W Q.size_pos hC hW] at hu
    have he := le_antisymm hu (Q.constant_grid_lower W hC.le hW)
    exact Q.eq_uniform_of_width Q.size_pos ((Q.constant_grid_eq_iff_width W hC hW).mp he)
  · intro hQ P
    rw [hQ, StrictPartition.uniform_gridCost_constant W Q.size_pos hC hW]
    exact P.constant_grid_lower W hC.le hW

theorem constant_grid_minimum (W : CellWeight) (hn : 0 < n)
    {C : ℝ} (hC : 0 < C) (hW : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) :
    IsLeast (range (fun Q : ClosedPartition n => Q.gridCost W))
      (C / (12 * (n : ℝ) ^ 2)) := by
  refine ⟨⟨(StrictPartition.uniform n hn).closed,
    StrictPartition.uniform_gridCost_constant W hn hC hW⟩, ?_⟩
  rintro M ⟨Q, rfl⟩
  exact Q.constant_grid_lower W hC.le hW

end TimeTraps.Interval
