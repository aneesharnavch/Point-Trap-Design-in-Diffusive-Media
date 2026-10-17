module

public import TimeTraps.Analysis.PositiveTimeChange

@[expose] public section

/-! A bounded positive Borel time speed gives an absolutely continuous
integral clock. Continuity of the time speed is not required. -/

namespace TimeTraps.Analysis

open MeasureTheory Set Filter
open scoped NNReal Topology

structure GraphPhysicalClockSpeed where
  rate : ℝ≥0 → ℝ
  measurable_rate : Measurable rate
  lower : ℝ≥0
  upper : ℝ≥0
  lower_pos : 0 < lower
  lower_le : ∀ s, (lower : ℝ) ≤ rate s
  le_upper : ∀ s, rate s ≤ (upper : ℝ)

theorem GraphPhysicalClockSpeed.rate_pos (v : GraphPhysicalClockSpeed) (s : ℝ≥0) :
    0 < v.rate s := lt_of_lt_of_le (show (0 : ℝ) < v.lower from v.lower_pos) (v.lower_le s)

theorem GraphPhysicalClockSpeed.rate_intervalIntegrable (v : GraphPhysicalClockSpeed) (a b : ℝ) :
    IntervalIntegrable (fun r => v.rate r.toNNReal) volume a b := by
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (v.upper : ℝ)) volume a b).mono_fun'
    (v.measurable_rate.comp continuous_real_toNNReal.measurable).aestronglyMeasurable
  exact Eventually.of_forall (fun r => by
    change ‖v.rate r.toNNReal‖ ≤ (v.upper : ℝ)
    rw [Real.norm_eq_abs, abs_of_pos (v.rate_pos r.toNNReal)]
    exact v.le_upper r.toNNReal)

noncomputable def GraphPhysicalClockSpeed.clock (v : GraphPhysicalClockSpeed) (s : ℝ≥0) : ℝ≥0 :=
  ⟨∫ r in (0 : ℝ)..s.val, v.rate r.toNNReal,
    intervalIntegral.integral_nonneg_of_forall s.coe_nonneg (fun r => (v.rate_pos r.toNNReal).le)⟩

theorem GraphPhysicalClockSpeed.clock_coe (v : GraphPhysicalClockSpeed) (s : ℝ≥0) :
    (v.clock s : ℝ) = ∫ r in (0 : ℝ)..s.val, v.rate r.toNNReal := rfl

theorem GraphPhysicalClockSpeed.clock_zero (v : GraphPhysicalClockSpeed) : v.clock 0 = 0 := by
  apply NNReal.eq
  exact intervalIntegral.integral_same

theorem GraphPhysicalClockSpeed.clock_increment (v : GraphPhysicalClockSpeed) (s t : ℝ≥0) :
    (v.clock t : ℝ) - (v.clock s : ℝ) = ∫ r in s.val..t.val, v.rate r.toNNReal :=
  intervalIntegral.integral_interval_sub_left (v.rate_intervalIntegrable 0 t.val)
    (v.rate_intervalIntegrable 0 s.val)

theorem GraphPhysicalClockSpeed.clock_increment_bounds (v : GraphPhysicalClockSpeed)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (v.lower : ℝ) * (t.val - s.val) ≤ (v.clock t : ℝ) - (v.clock s : ℝ) ∧
      (v.clock t : ℝ) - (v.clock s : ℝ) ≤ (v.upper : ℝ) * (t.val - s.val) := by
  rw [v.clock_increment]
  constructor
  · have h := intervalIntegral.integral_mono_on (show s.val ≤ t.val from hst)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (v.lower : ℝ)) volume s.val t.val)
      (v.rate_intervalIntegrable s.val t.val) (fun r _ => v.lower_le r.toNNReal)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h
  · have h := intervalIntegral.integral_mono_on (show s.val ≤ t.val from hst)
      (v.rate_intervalIntegrable s.val t.val)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (v.upper : ℝ)) volume s.val t.val)
      (fun r _ => v.le_upper r.toNNReal)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h

end TimeTraps.Analysis
