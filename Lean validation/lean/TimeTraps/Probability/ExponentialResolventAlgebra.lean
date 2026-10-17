module

public import TimeTraps.Probability.ExponentialPrimitiveConvolution

@[expose] public section

/-! Exact exponential unweighting of an integrable occupation source.
This is deterministic and applies to Borel sources without differentiating them. -/

namespace TimeTraps.Probability

open Set MeasureTheory
open scoped NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exponentialResolvent_unweight_real {f u : ℝ → ℝ} {T : ℝ}
    (hf : IntervalIntegrable f volume 0 T) (hu : IntervalIntegrable u volume 0 T) :
    Real.exp T * ((∫ s in (0 : ℝ)..T, Real.exp (-s) * f s) + Real.exp (-T) * u T) -
      (∫ r in (0 : ℝ)..T, Real.exp r *
        ((∫ s in (0 : ℝ)..r, Real.exp (-s) * f s) + Real.exp (-r) * u r)) =
      u T - (∫ r in (0 : ℝ)..T, u r) + (∫ r in (0 : ℝ)..T, f r) := by
  have hm (r : ℝ) : Real.exp r *
      ((∫ s in (0 : ℝ)..r, Real.exp (-s) * f s) + Real.exp (-r) * u r) =
      Real.exp r * (∫ s in (0 : ℝ)..r, Real.exp (-s) * f s) + u r := by
    rw [mul_add, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  simp_rw [hm]
  rw [intervalIntegral.integral_add (exponentialPrimitiveConvolution_intervalIntegrable hf) hu,
    exponentialPrimitiveConvolution_eq hf]
  ring

theorem exponentialResolvent_unweight_nnreal (f u : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hf : IntervalIntegrable (fun r => f r.toNNReal) volume 0 (T : ℝ))
    (hu : IntervalIntegrable (fun r => u r.toNNReal) volume 0 (T : ℝ)) :
    Real.exp (T : ℝ) * ((∫ s in (0 : ℝ)..(T : ℝ), Real.exp (-s) * f s.toNNReal) +
      Real.exp (-(T : ℝ)) * u T) -
      (∫ r in (0 : ℝ)..(T : ℝ), Real.exp r *
        ((∫ s in (0 : ℝ)..(r.toNNReal : ℝ), Real.exp (-s) * f s.toNNReal) +
          Real.exp (-(r.toNNReal : ℝ)) * u r.toNNReal)) =
      u T - (∫ r in (0 : ℝ)..(T : ℝ), u r.toNNReal) +
        (∫ r in (0 : ℝ)..(T : ℝ), f r.toNNReal) := by
  have hh := exponentialResolvent_unweight_real hf hu
  simp only [Real.toNNReal_coe] at hh
  rw [← hh]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le T.coe_nonneg] at hr
  dsimp only
  rw [Real.coe_toNNReal r hr.1]

end TimeTraps.Probability
