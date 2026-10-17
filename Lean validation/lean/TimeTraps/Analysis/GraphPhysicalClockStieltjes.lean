module

public import TimeTraps.Analysis.GraphPhysicalClockDerivative
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

/-! The real integral primitive extends the actual positive-time clock.
Its Stieltjes measure is exactly the original Borel speed times Lebesgue
measure, proved by interval increments rather than pointwise derivatives. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped NNReal ENNReal

noncomputable def GraphPhysicalClockSpeed.realClock (v : GraphPhysicalClockSpeed) (t : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..t, v.rate r.toNNReal

theorem GraphPhysicalClockSpeed.realClock_increment (v : GraphPhysicalClockSpeed) (s t : ℝ) :
    v.realClock t - v.realClock s = ∫ r in s..t, v.rate r.toNNReal :=
  intervalIntegral.integral_interval_sub_left (v.rate_intervalIntegrable 0 t) (v.rate_intervalIntegrable 0 s)

theorem GraphPhysicalClockSpeed.realClock_monotone (v : GraphPhysicalClockSpeed) : Monotone v.realClock := by
  intro s t hst
  rw [← sub_nonneg, v.realClock_increment]
  exact intervalIntegral.integral_nonneg_of_forall hst (fun r => (v.rate_pos r.toNNReal).le)

theorem GraphPhysicalClockSpeed.realClock_lipschitz (v : GraphPhysicalClockSpeed) :
    LipschitzWith v.upper v.realClock := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [Real.dist_eq, ← Real.norm_eq_abs, v.realClock_increment, Real.dist_eq]
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun r _ => by
    rw [Real.norm_eq_abs, abs_of_pos (v.rate_pos r.toNNReal)]
    exact v.le_upper r.toNNReal)

noncomputable def GraphPhysicalClockSpeed.stieltjes (v : GraphPhysicalClockSpeed) : StieltjesFunction ℝ where
  toFun := v.realClock
  mono' := v.realClock_monotone
  right_continuous' _ := v.realClock_lipschitz.continuous.continuousAt.continuousWithinAt

theorem GraphPhysicalClockSpeed.stieltjes_clock (v : GraphPhysicalClockSpeed) (t : ℝ≥0) :
    v.stieltjes (t : ℝ) = (v.clock t : ℝ) := rfl

theorem GraphPhysicalClockSpeed.stieltjes_continuous (v : GraphPhysicalClockSpeed) :
    Continuous v.stieltjes := v.realClock_lipschitz.continuous

theorem GraphPhysicalClockSpeed.stieltjes_measure (v : GraphPhysicalClockSpeed) :
    v.stieltjes.measure = volume.withDensity (fun r : ℝ => ENNReal.ofReal (v.rate r.toNNReal)) := by
  apply Measure.ext_of_Ioc
  intro a b hab
  rw [StieltjesFunction.measure_Ioc]
  change ENNReal.ofReal (v.realClock b - v.realClock a) = _
  rw [v.realClock_increment, withDensity_apply _ measurableSet_Ioc,
    intervalIntegral.integral_of_le hab.le]
  exact ofReal_integral_eq_lintegral_ofReal (v.rate_intervalIntegrable a b).1
    (Eventually.of_forall (fun r => (v.rate_pos r.toNNReal).le))

end TimeTraps.Analysis
