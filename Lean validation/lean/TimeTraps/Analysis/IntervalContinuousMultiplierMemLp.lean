module

public import TimeTraps.Analysis.IntervalContinuousMultiplier

@[expose] public section

/-! Continuous coefficients preserve actual unbundled L2 functions on a
compact interval, including weak derivatives and physical forcing terms. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter

variable {l r : ℝ}

theorem intervalContinuous_mul_memLp (c : ℝ → ℝ) (hc : ContinuousOn c (Icc l r))
    {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Ioo l r))) :
    MemLp (fun x => c x * f x) 2 (volume.restrict (Ioo l r)) := by
  apply hf.of_le_mul (c := ‖intervalContinuousCoefficient c hc‖)
    ((hc.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo |>.mul
      hf.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (intervalContinuousCoefficient_bound c hc (Ioo_subset_Icc_self hx))
    (norm_nonneg _)

theorem IntervalEnergy.weighted_derivative_memLp {u : ℝ → ℝ}
    (hu : IntervalEnergy u l r) (hlr : l ≤ r)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc l r)) :
    MemLp (fun x => c x * deriv u x) 2 (volume.restrict (Ioo l r)) := by
  apply intervalContinuous_mul_memLp c hc
  apply hu.derivative_memLp.mono_measure
  rw [uIoc_of_le hlr]
  exact Measure.restrict_mono_set volume Ioo_subset_Ioc_self

end TimeTraps.Analysis
