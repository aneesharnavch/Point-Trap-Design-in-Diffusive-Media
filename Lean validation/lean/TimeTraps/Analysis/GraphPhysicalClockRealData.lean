module

public import TimeTraps.Analysis.GraphPhysicalClockStieltjes

@[expose] public section

/-! The real extension of the original Borel clock remains strictly
increasing. Negative times use the constant rate at zero, solely to
provide an invertible real-time change of variables. -/

namespace TimeTraps.Analysis

open Set MeasureTheory
open scoped NNReal

theorem GraphPhysicalClockSpeed.realClock_increment_lower (v : GraphPhysicalClockSpeed)
    {s t : ℝ} (hst : s ≤ t) :
    (v.lower : ℝ) * (t - s) ≤ v.realClock t - v.realClock s := by
  rw [v.realClock_increment]
  have hh := intervalIntegral.integral_mono_on hst
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (v.lower : ℝ)) volume s t)
    (v.rate_intervalIntegrable s t) (fun r _ => v.lower_le r.toNNReal)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hh

theorem GraphPhysicalClockSpeed.realClock_strictMono (v : GraphPhysicalClockSpeed) :
    StrictMono v.realClock := by
  intro s t hst
  have hh := v.realClock_increment_lower hst.le
  have hp : 0 < (v.lower : ℝ) * (t - s) := mul_pos v.lower_pos (sub_pos.mpr hst)
  linarith

theorem GraphPhysicalClockSpeed.realClock_nonpositive (v : GraphPhysicalClockSpeed)
    {t : ℝ} (ht : t ≤ 0) : v.realClock t = t * v.rate 0 := by
  unfold realClock
  calc
    _ = ∫ _r in (0 : ℝ)..t, v.rate 0 := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_ge ht] at hr
      dsimp only
      rw [Real.toNNReal_eq_zero.mpr hr.2]
    _ = _ := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]

end TimeTraps.Analysis
