module

public import TimeTraps.Interval.ConstantCell
public import TimeTraps.Interval.PartitionProfile

@[expose] public section

/-!
The constant-weight attaining profile consists of exact parabolic halves.
Integrating them gives the cell average and the total source-coordinate
average. These are analytical integral identities, valid for every partition.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

theorem parabolic_cap_integral_left (C M α β : ℝ) (hab : α ≤ β) :
    (∫ t in α..β, M - C * (t - α) ^ 2 / 2) = M * (β - α) - C * (β - α) ^ 3 / 6 := by
  have hd (x : ℝ) : HasDerivAt (fun t : ℝ => M * t - C * (t - α) ^ 3 / 6)
      (M - C * (x - α) ^ 2 / 2) x := by
    have ht := ((hasDerivAt_id x).const_mul M).sub
      (((((hasDerivAt_id x).sub_const α).pow 3).const_mul C).div_const 6)
    have he : M * 1 - C * ((3 : ℝ) * (x - α) ^ (3 - 1) * 1) / 6 =
        M - C * (x - α) ^ 2 / 2 := by ring
    change HasDerivAt (fun t : ℝ => M * t - C * (t - α) ^ 3 / 6)
      (M * 1 - C * ((3 : ℝ) * (x - α) ^ (3 - 1) * 1) / 6) x at ht
    rw [he] at ht
    exact ht
  have hi := integral_derivative_to_point
    ((continuous_const.mul continuous_id).sub
      ((continuous_const.mul ((continuous_id.sub continuous_const).pow 3)).div_const 6)).continuousOn
    (continuous_const.sub
      ((continuous_const.mul ((continuous_id.sub continuous_const).pow 2)).div_const 2)).continuousOn
    (fun x _ => hd x) (show β ∈ Icc α β from ⟨hab, le_rfl⟩)
  change (∫ t in α..β, M - C * (t - α) ^ 2 / 2) =
    (M * β - C * (β - α) ^ 3 / 6) - (M * α - C * (α - α) ^ 3 / 6) at hi
  rw [hi]
  ring

theorem parabolic_cap_integral_right (C M α β : ℝ) (hab : α ≤ β) :
    (∫ t in α..β, M - C * (β - t) ^ 2 / 2) = M * (β - α) - C * (β - α) ^ 3 / 6 := by
  have hd (x : ℝ) : HasDerivAt (fun t : ℝ => M * t + C * (β - t) ^ 3 / 6)
      (M - C * (β - x) ^ 2 / 2) x := by
    have ht := ((hasDerivAt_id x).const_mul M).add
      (((((hasDerivAt_id x).const_sub β).pow 3).const_mul C).div_const 6)
    have he : M * 1 + C * ((3 : ℝ) * (β - x) ^ (3 - 1) * (-1)) / 6 =
        M - C * (β - x) ^ 2 / 2 := by ring
    change HasDerivAt (fun t : ℝ => M * t + C * (β - t) ^ 3 / 6)
      (M * 1 + C * ((3 : ℝ) * (β - x) ^ (3 - 1) * (-1)) / 6) x at ht
    rw [he] at ht
    exact ht
  have hi := integral_derivative_to_point
    ((continuous_const.mul continuous_id).add
      ((continuous_const.mul ((continuous_const.sub continuous_id).pow 3)).div_const 6)).continuousOn
    (continuous_const.sub
      ((continuous_const.mul ((continuous_const.sub continuous_id).pow 2)).div_const 2)).continuousOn
    (fun x _ => hd x) (show β ∈ Icc α β from ⟨hab, le_rfl⟩)
  change (∫ t in α..β, M - C * (β - t) ^ 2 / 2) =
    (M * β + C * (β - β) ^ 3 / 6) - (M * α + C * (β - α) ^ 3 / 6) at hi
  rw [hi]
  ring

variable {n : ℕ}

theorem IntervalMedium.constant_profile_left (A : IntervalMedium) (Q : StrictPartition n)
    {C : ℝ} (hC : ∀ z ∈ Icc (0 : ℝ) 1, A.cellWeight.value z = C) (M : ℝ)
    (i : Fin n) {z : ℝ} (hz : z ∈ Icc (Q.point i.castSucc) (Q.center A.cellWeight i)) :
    A.partitionProfile Q M z = M - C * (z - Q.point i.castSucc) ^ 2 / 2 := by
  have h := A.partitionProfile_left Q M i hz
  rw [A.partitionProfile_boundary,
    A.cellWeight.leftRise_constant hC (Q.point_mem i.castSucc).1
      (hz.2.trans (Q.center_interior A.cellWeight i).2.le) hz.1] at h
  linarith

theorem IntervalMedium.constant_profile_right (A : IntervalMedium) (Q : StrictPartition n)
    {C : ℝ} (hC : ∀ z ∈ Icc (0 : ℝ) 1, A.cellWeight.value z = C) (M : ℝ)
    (i : Fin n) {z : ℝ} (hz : z ∈ Icc (Q.center A.cellWeight i) (Q.point i.succ)) :
    A.partitionProfile Q M z = M - C * (Q.point i.succ - z) ^ 2 / 2 := by
  have h := A.partitionProfile_right Q M i hz
  rw [A.partitionProfile_boundary,
    A.cellWeight.rightRise_constant hC ((Q.center_interior A.cellWeight i).1.le.trans hz.1)
      (Q.point_mem i.succ).2 hz.2] at h
  linarith

theorem IntervalMedium.constant_profile_cell_integral (A : IntervalMedium) (Q : StrictPartition n)
    {C : ℝ} (hC : ∀ z ∈ Icc (0 : ℝ) 1, A.cellWeight.value z = C) (M : ℝ) (i : Fin n) :
    (∫ z in Q.point i.castSucc..Q.point i.succ, A.partitionProfile Q M z) =
      M * Q.width i - C * Q.width i ^ 3 / 24 := by
  let α := Q.point i.castSucc
  let β := Q.point i.succ
  let c := Q.center A.cellWeight i
  have hc : c ∈ Ioo α β := Q.center_mem A.cellWeight i
  have he : c = (α + β) / 2 := A.cellWeight.center_constant hC
    (Q.point_mem i.castSucc).1 (Q.point_mem i.succ).2 (Q.strictMono.monotone (Fin.castSucc_le_succ i))
  have hl : (∫ z in α..c, A.partitionProfile Q M z) = M * (c - α) - C * (c - α) ^ 3 / 6 := by
    calc
      _ = ∫ z in α..c, M - C * (z - α) ^ 2 / 2 := by
        apply intervalIntegral.integral_congr_Ioo_of_le hc.1.le
        intro z hz
        exact A.constant_profile_left Q hC M i ⟨hz.1.le, hz.2.le⟩
      _ = _ := parabolic_cap_integral_left C M α c hc.1.le
  have hr : (∫ z in c..β, A.partitionProfile Q M z) = M * (β - c) - C * (β - c) ^ 3 / 6 := by
    calc
      _ = ∫ z in c..β, M - C * (β - z) ^ 2 / 2 := by
        apply intervalIntegral.integral_congr_Ioo_of_le hc.2.le
        intro z hz
        exact A.constant_profile_right Q hC M i ⟨hz.1.le, hz.2.le⟩
      _ = _ := parabolic_cap_integral_right C M c β hc.2.le
  change (∫ z in α..β, A.partitionProfile Q M z) = M * (β - α) - C * (β - α) ^ 3 / 24
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((A.partitionProfile_continuous Q M).intervalIntegrable α c)
    ((A.partitionProfile_continuous Q M).intervalIntegrable c β), hl, hr, he]
  ring

theorem StrictPartition.integral_sum (Q : StrictPartition n) {f : ℝ → ℝ} (hf : Continuous f) :
    (∑ i : Fin n, ∫ z in Q.point i.castSucc..Q.point i.succ, f z) = ∫ z in (0 : ℝ)..1, f z := by
  have he (i : Fin n) : (∫ z in Q.point i.castSucc..Q.point i.succ, f z) =
      (∫ z in 0..Q.point i.succ, f z) - (∫ z in 0..Q.point i.castSucc, f z) :=
    (intervalIntegral.integral_interval_sub_left
      (hf.intervalIntegrable 0 (Q.point i.succ)) (hf.intervalIntegrable 0 (Q.point i.castSucc))).symm
  simp_rw [he]
  rw [Finset.sum_sub_distrib]
  have h₀ := Fin.sum_univ_succ (fun e => ∫ z in 0..Q.point e, f z)
  have h₁ := Fin.sum_univ_castSucc (fun e => ∫ z in 0..Q.point e, f z)
  rw [Q.first, intervalIntegral.integral_same] at h₀
  rw [Q.last] at h₁
  linarith

theorem IntervalMedium.constant_profile_integral (A : IntervalMedium) (Q : StrictPartition n)
    {C : ℝ} (hC : ∀ z ∈ Icc (0 : ℝ) 1, A.cellWeight.value z = C) (M : ℝ) :
    (∫ z in (0 : ℝ)..1, A.partitionProfile Q M z) = M - C / 24 * ∑ i, Q.width i ^ 3 := by
  rw [← Q.integral_sum (A.partitionProfile_continuous Q M)]
  simp_rw [A.constant_profile_cell_integral Q hC M]
  have hs : (∑ i, C * Q.width i ^ 3 / 24) = C / 24 * ∑ i, Q.width i ^ 3 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Q.width_sum, mul_one, hs]

end TimeTraps.Interval
