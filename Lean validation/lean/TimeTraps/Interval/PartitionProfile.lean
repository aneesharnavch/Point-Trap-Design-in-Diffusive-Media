module

public import TimeTraps.Interval.PartitionCDF

@[expose] public section

/-!
The candidate profile is an exact integral of a prescribed slope. Its cell
heights and maximum are consequences of balance, before any weak equation
or optimality assertion is made.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {n : ℕ}

noncomputable def IntervalMedium.partitionProfile (A : IntervalMedium) (Q : StrictPartition n)
    (M z : ℝ) : ℝ := M + ∫ t in 0..z, A.partitionSlope Q t

theorem IntervalMedium.partitionProfile_continuous (A : IntervalMedium) (Q : StrictPartition n)
    (M : ℝ) : Continuous (A.partitionProfile Q M) :=
  continuous_const.add (intervalIntegral.continuous_primitive (A.partitionSlope_integrable Q) 0)

theorem IntervalMedium.partitionProfile_derivative (A : IntervalMedium) (Q : StrictPartition n)
    (M : ℝ) {z : ℝ} (hz : ∀ i, Q.center A.cellWeight i ≠ z) :
    HasDerivAt (A.partitionProfile Q M) (A.partitionSlope Q z) z :=
  (intervalIntegral.integral_hasDerivAt_right (A.partitionSlope_integrable Q 0 z)
    (A.partitionSlope_measurable Q).stronglyMeasurable.stronglyMeasurableAtFilter
    (A.partitionSlope_continuousAt Q hz)).const_add M

theorem IntervalMedium.partitionProfile_difference (A : IntervalMedium) (Q : StrictPartition n)
    (M a b : ℝ) :
    A.partitionProfile Q M b - A.partitionProfile Q M a = ∫ t in a..b, A.partitionSlope Q t := by
  unfold IntervalMedium.partitionProfile
  rw [add_sub_add_left_eq_sub]
  exact intervalIntegral.integral_interval_sub_left
    (A.partitionSlope_integrable Q 0 b) (A.partitionSlope_integrable Q 0 a)

theorem IntervalMedium.partitionProfile_zero (A : IntervalMedium) (Q : StrictPartition n) (M : ℝ) :
    A.partitionProfile Q M 0 = M := by simp [IntervalMedium.partitionProfile]

theorem IntervalMedium.partitionProfile_left (A : IntervalMedium) (Q : StrictPartition n) (M : ℝ)
    (i : Fin n) {z : ℝ} (hz : z ∈ Icc (Q.point i.castSucc) (Q.center A.cellWeight i)) :
    A.partitionProfile Q M z - A.partitionProfile Q M (Q.point i.castSucc) =
      -A.cellWeight.leftRise (Q.point i.castSucc) z := by
  rw [A.partitionProfile_difference]
  change (∫ t in Q.point i.castSucc..z, A.partitionSlope Q t) =
    -(∫ t in Q.point i.castSucc..z, A.source.weight A.conductance t * (t - Q.point i.castSucc))
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr_Ioo_of_le hz.1
  intro t ht
  dsimp only [IntervalMedium.partitionSlope]
  rw [A.partitionCDF_left Q i ⟨ht.1, ht.2.trans_le hz.2⟩]
  ring

theorem IntervalMedium.partitionProfile_right (A : IntervalMedium) (Q : StrictPartition n) (M : ℝ)
    (i : Fin n) {z : ℝ} (hz : z ∈ Icc (Q.center A.cellWeight i) (Q.point i.succ)) :
    A.partitionProfile Q M (Q.point i.succ) - A.partitionProfile Q M z =
      A.cellWeight.rightRise (Q.point i.succ) z := by
  rw [A.partitionProfile_difference]
  apply intervalIntegral.integral_congr_Ioo_of_le hz.2
  intro t ht
  dsimp only [IntervalMedium.partitionSlope]
  rw [A.partitionCDF_right Q i ⟨hz.1.trans_lt ht.1, ht.2⟩]
  rfl

theorem IntervalMedium.partitionProfile_cell_equal (A : IntervalMedium) (Q : StrictPartition n)
    (M : ℝ) (i : Fin n) :
    A.partitionProfile Q M (Q.point i.succ) = A.partitionProfile Q M (Q.point i.castSucc) := by
  have hc := Q.center_mem A.cellWeight i
  have hl := A.partitionProfile_left Q M i ⟨hc.1.le, le_rfl⟩
  have hr := A.partitionProfile_right Q M i ⟨le_rfl, hc.2.le⟩
  rw [Q.balance A.cellWeight i] at hl
  linarith

theorem IntervalMedium.partitionProfile_boundary (A : IntervalMedium) (Q : StrictPartition n)
    (M : ℝ) (e : Fin (n + 1)) : A.partitionProfile Q M (Q.point e) = M := by
  induction e using Fin.induction with
  | zero => rw [Q.first, A.partitionProfile_zero]
  | succ i ih => rw [A.partitionProfile_cell_equal, ih]

theorem IntervalMedium.partitionProfile_trap (A : IntervalMedium) (Q : StrictPartition n)
    (M : ℝ) (i : Fin n) :
    A.partitionProfile Q M (Q.center A.cellWeight i) = M - Q.barrier A.cellWeight i := by
  have h := A.partitionProfile_left Q M i ⟨(Q.center_mem A.cellWeight i).1.le, le_rfl⟩
  rw [A.partitionProfile_boundary] at h
  change A.partitionProfile Q M (Q.center A.cellWeight i) - M = -Q.barrier A.cellWeight i at h
  linarith

theorem IntervalMedium.partitionProfile_le (A : IntervalMedium) (Q : StrictPartition n)
    (M : ℝ) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) : A.partitionProfile Q M z ≤ M := by
  obtain ⟨i, hi⟩ := Q.cover hz
  by_cases hc : z ≤ Q.center A.cellWeight i
  · have he := A.partitionProfile_left Q M i ⟨hi.1, hc⟩
    rw [A.partitionProfile_boundary] at he
    have hn : 0 ≤ A.cellWeight.leftRise (Q.point i.castSucc) z :=
      intervalIntegral.integral_nonneg hi.1 (fun t ht =>
        mul_nonneg (A.source.weight_pos A.conductance_pos t).le (sub_nonneg.mpr ht.1))
    linarith
  · have he := A.partitionProfile_right Q M i ⟨(lt_of_not_ge hc).le, hi.2⟩
    rw [A.partitionProfile_boundary] at he
    have hn : 0 ≤ A.cellWeight.rightRise (Q.point i.succ) z :=
      intervalIntegral.integral_nonneg hi.2 (fun t ht =>
        mul_nonneg (A.source.weight_pos A.conductance_pos t).le (sub_nonneg.mpr ht.2))
    linarith

end TimeTraps.Interval
