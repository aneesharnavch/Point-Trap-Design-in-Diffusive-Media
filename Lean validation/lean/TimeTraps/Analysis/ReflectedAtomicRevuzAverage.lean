module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-! One-sided short-time averages of an actual continuous real function.
This is the fundamental-theorem-of-calculus step in the atomic test
normalization, independent of stochastic additive-functional properties. -/

namespace TimeTraps.Analysis

open MeasureTheory Filter Set
open scoped Topology

theorem reflectedAtomicRevuz_continuous_average {f : ℝ → ℝ} (hf : Continuous f) :
    Tendsto (fun t : ℝ => t⁻¹ * ∫ s in (0 : ℝ)..t, f s) (𝓝[>] 0) (𝓝 (f 0)) := by
  have hd : HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, f s) (f 0) 0 :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 0)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  simpa only [zero_add, intervalIntegral.integral_same, sub_zero, smul_eq_mul] using
    hd.tendsto_slope_zero_right

end TimeTraps.Analysis
