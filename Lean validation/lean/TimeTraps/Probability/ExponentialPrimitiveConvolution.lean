module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-! Exponential convolution with an integral primitive. The source is
only interval integrable; absolute continuity of its primitive provides
integration by parts without a pointwise derivative of the source. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter

theorem exponentialPrimitiveConvolution_intervalIntegrable
    {f : ℝ → ℝ} {T : ℝ} (hf : IntervalIntegrable f volume 0 T) :
    IntervalIntegrable (fun r => Real.exp r *
      (∫ s in (0 : ℝ)..r, Real.exp (-s) * f s)) volume 0 T := by
  have hw : IntervalIntegrable (fun s => Real.exp (-s) * f s) volume 0 T :=
    hf.continuousOn_mul (Real.continuous_exp.comp continuous_neg).continuousOn
  have hA := hw.absolutelyContinuousOnInterval_intervalIntegral
    (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 T)
  exact (Real.continuous_exp.continuousOn.mul hA.continuousOn).intervalIntegrable

theorem exponentialPrimitiveConvolution_eq
    {f : ℝ → ℝ} {T : ℝ} (hf : IntervalIntegrable f volume 0 T) :
    (∫ r in (0 : ℝ)..T, Real.exp r *
      (∫ s in (0 : ℝ)..r, Real.exp (-s) * f s)) =
      Real.exp T * (∫ s in (0 : ℝ)..T, Real.exp (-s) * f s) -
        (∫ s in (0 : ℝ)..T, f s) := by
  let A := fun r => ∫ s in (0 : ℝ)..r, Real.exp (-s) * f s
  have hw : IntervalIntegrable (fun s => Real.exp (-s) * f s) volume 0 T :=
    hf.continuousOn_mul (Real.continuous_exp.comp continuous_neg).continuousOn
  have hA : AbsolutelyContinuousOnInterval A 0 T :=
    hw.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have he : AbsolutelyContinuousOnInterval Real.exp 0 T :=
    (Real.contDiff_exp.contDiffOn : ContDiffOn ℝ 1 Real.exp (uIcc 0 T)).absolutelyContinuousOnInterval
  have hd : (∫ r in (0 : ℝ)..T, deriv A r * Real.exp r) =
      (∫ r in (0 : ℝ)..T, f r) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hw.ae_hasDerivAt_integral] with r hr hrmem
    have hder : deriv A r = Real.exp (-r) * f r :=
      (hr (uIoc_subset_uIcc hrmem) 0 left_mem_uIcc).deriv
    rw [hder]
    calc
      _ = (Real.exp (-r) * Real.exp r) * f r := by ring
      _ = f r := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have hp := hA.integral_mul_deriv_eq_deriv_mul he
  rw [Real.deriv_exp, hd] at hp
  calc
    _ = ∫ r in (0 : ℝ)..T, A r * Real.exp r := by
      apply intervalIntegral.integral_congr
      intro r _
      exact mul_comm _ _
    _ = _ := by
      simpa only [A, intervalIntegral.integral_same, zero_mul, sub_zero, mul_comm] using hp

end TimeTraps.Probability
