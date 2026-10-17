module

public import TimeTraps.Probability.BrownianLocalTimeTimeReconstruction

@[expose] public section

/-! The left grid samples increase to the requested time and are bounded
by every larger integer horizon. These are deterministic properties of
the actual samples used to reconstruct the local-time field. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

theorem brownianLocalTimeSampleTime_le (n : ℕ) (t : ℝ≥0) :
    brownianLocalTimeSampleTime n t ≤ t := by
  have hp : 0 < (1 / 64 : ℝ) ^ n := by positivity
  have hx : 0 ≤ t.val * (64 : ℝ) ^ n := mul_nonneg t.coe_nonneg (by positivity)
  have h := mul_le_mul_of_nonneg_right (Nat.floor_le hx) hp.le
  have he : (64 : ℝ) ^ n * (1 / 64 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  rw [mul_assoc, he, mul_one] at h
  change (brownianDyadicTime (Nat.pair n (brownianDyadicFloor t n))).val ≤ t.val
  rw [brownianDyadicTime_pair]
  exact h

theorem brownianLocalTimeSampleTime_monotone (t : ℝ≥0) :
    Monotone (fun n => brownianLocalTimeSampleTime n t) := by
  apply monotone_nat_of_le_succ
  intro n
  have h := (brownianDyadicFloor_refine t n).1
  change brownianDyadicTime (Nat.pair n (brownianDyadicFloor t n)) ≤
    brownianDyadicTime (Nat.pair (n + 1) (brownianDyadicFloor t (n + 1)))
  rw [← brownianDyadicTime_refine n (brownianDyadicFloor t n),
    brownianDyadicTime_pair, brownianDyadicTime_pair]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h) (by positivity)

theorem brownianLocalTimeSampleTime_le_integer {t : ℝ≥0} {N : ℕ}
    (ht : t ≤ N) (n : ℕ) :
    brownianLocalTimeSampleTime n t ≤ brownianDyadicTime (Nat.pair 0 N) := by
  simpa only [brownianDyadicTime_pair, pow_zero, mul_one] using
    (brownianLocalTimeSampleTime_le n t).trans ht

theorem brownianLocalTimeSampleTime_integer_eventually (N : ℕ) (n : ℕ) :
    brownianLocalTimeSampleTime n N = N := by
  have hf := brownianDyadicFloor_at_grid 0 N n
  simp only [brownianDyadicTime_pair, pow_zero, mul_one, zero_add] at hf
  rw [brownianLocalTimeSampleTime, hf, brownianDyadicTime_pair]
  apply NNReal.eq
  change ((N * 64 ^ n : ℕ) : ℝ) * (1 / 64 : ℝ) ^ n = N
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc, ← mul_pow]
  norm_num

end TimeTraps.Probability
