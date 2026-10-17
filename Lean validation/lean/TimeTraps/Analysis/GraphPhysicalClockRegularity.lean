module

public import TimeTraps.Analysis.GraphPhysicalClockInverse
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

@[expose] public section

/-! The measurable-speed clock is absolutely continuous on each finite
real interval. Its inverse also satisfies a genuine Lipschitz estimate,
so both directions have quantitative continuity without rate continuity. -/

namespace TimeTraps.Analysis

open Set MeasureTheory
open scoped NNReal

theorem GraphPhysicalClockSpeed.clock_absolutelyContinuous (v : GraphPhysicalClockSpeed) (T : ℝ≥0) :
    AbsolutelyContinuousOnInterval (fun t : ℝ => ∫ r in (0 : ℝ)..t, v.rate r.toNNReal) 0 T.val :=
  (v.rate_intervalIntegrable 0 T.val).absolutelyContinuousOnInterval_intervalIntegral
    left_mem_uIcc

theorem GraphPhysicalClockSpeed.inverse_lipschitz (v : GraphPhysicalClockSpeed) :
    LipschitzWith v.lower⁻¹ v.inverse := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  wlog hst : s ≤ t generalizing s t
  · simpa only [dist_comm] using this t s (le_of_not_ge hst)
  have hb := (v.inverse_increment_bounds hst).2
  have hm := v.inverse_strictMono.monotone hst
  change dist (v.inverse s : ℝ) (v.inverse t : ℝ) ≤ ((v.lower : ℝ)⁻¹) * dist (s : ℝ) (t : ℝ)
  rw [Real.dist_eq, Real.dist_eq,
    abs_of_nonpos (sub_nonpos.mpr (show (v.inverse s : ℝ) ≤ (v.inverse t : ℝ) from hm)),
    abs_of_nonpos (sub_nonpos.mpr (show (s : ℝ) ≤ (t : ℝ) from hst))]
  simp only [neg_sub]
  convert! hb using 1
  ring_nf
  rfl

end TimeTraps.Analysis
