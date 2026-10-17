module

public import TimeTraps.Probability.ReflectedAtomicRevuzKernel
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Actual time-space Fubini for the fixed-atom occupation mean. Positive
time slices have kernel mass one. Their norm integrals are bounded by
the continuous test norm, so no uniform density bound at time zero is
needed. The resulting spatial identity uses the actual Feller operator. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

theorem reflectedAtomicRevuzKernel_joint_integrable (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (a : Icc (0 : ℝ) L) (h : C(Icc (0 : ℝ) L, ℝ)) (T : ℝ≥0) :
    Integrable (fun p : ℝ × ℝ => reflectedFellerExtension L hL h p.2 *
      reflectedGaussianDensity L p.2 (2 * D * p.1).toNNReal a.val)
      ((volume.restrict (Ioc (0 : ℝ) T.val)).prod (volume.restrict (Ioo (0 : ℝ) L))) := by
  have hm := (reflectedAtomicRevuzKernel_jointlyMeasurable L hL D a.val h).aestronglyMeasurable
    (μ := (volume.restrict (Ioc (0 : ℝ) T.val)).prod (volume.restrict (Ioo (0 : ℝ) L)))
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact reflectedAtomicRevuzKernel_integrable L hL a h
      (Real.toNNReal_pos.mpr (mul_pos (mul_pos (by norm_num) hD) hr.1))
  · apply (integrable_const ‖h‖).mono' hm.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact reflectedAtomicRevuzKernel_integral_norm_le L hL a h
      (Real.toNNReal_pos.mpr (mul_pos (mul_pos (by norm_num) hD) hr.1))

theorem reflectedAtomicRevuzKernel_spatial_integrable (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (a : Icc (0 : ℝ) L) (h : C(Icc (0 : ℝ) L, ℝ)) (T : ℝ≥0) :
    IntegrableOn (fun x => reflectedFellerExtension L hL h x *
      ∫ r in (0 : ℝ)..T.val, reflectedGaussianDensity L x (2 * D * r).toNNReal a.val)
      (Ioo (0 : ℝ) L) volume := by
  apply (reflectedAtomicRevuzKernel_joint_integrable L hL D hD a h T).integral_prod_right.congr
  filter_upwards [] with x
  change (∫ r in Ioc (0 : ℝ) T.val,
    reflectedFellerExtension L hL h x * reflectedGaussianDensity L x (2 * D * r).toNNReal a.val) = _
  rw [integral_const_mul]
  exact congrArg (fun z : ℝ => reflectedFellerExtension L hL h x * z)
    (intervalIntegral.integral_of_le (f := fun r =>
      reflectedGaussianDensity L x (2 * D * r).toNNReal a.val) T.coe_nonneg).symm

theorem reflectedAtomicRevuzKernel_spatial_identity (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (a : Icc (0 : ℝ) L) (h : C(Icc (0 : ℝ) L, ℝ)) (T : ℝ≥0) :
    (∫ x in Ioo (0 : ℝ) L, reflectedFellerExtension L hL h x *
      ∫ r in (0 : ℝ)..T.val, reflectedGaussianDensity L x (2 * D * r).toNNReal a.val) =
      ∫ r in (0 : ℝ)..T.val, reflectedFellerTimeOperator L hL D r h a := by
  calc
    _ = ∫ x in Ioo (0 : ℝ) L, ∫ r in Ioc (0 : ℝ) T.val,
        reflectedFellerExtension L hL h x * reflectedGaussianDensity L x (2 * D * r).toNNReal a.val := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [integral_const_mul]
      exact congrArg (fun z : ℝ => reflectedFellerExtension L hL h x * z)
        (intervalIntegral.integral_of_le (f := fun r =>
          reflectedGaussianDensity L x (2 * D * r).toNNReal a.val) T.coe_nonneg)
    _ = ∫ r in Ioc (0 : ℝ) T.val, ∫ x in Ioo (0 : ℝ) L,
        reflectedFellerExtension L hL h x * reflectedGaussianDensity L x (2 * D * r).toNNReal a.val :=
      (integral_integral_swap (reflectedAtomicRevuzKernel_joint_integrable L hL D hD a h T)).symm
    _ = ∫ r in Ioc (0 : ℝ) T.val, reflectedFellerTimeOperator L hL D r h a := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact reflectedAtomicRevuzKernel_integral L hL a h
        (Real.toNNReal_pos.mpr (mul_pos (mul_pos (by norm_num) hD) hr.1))
    _ = _ := (intervalIntegral.integral_of_le T.coe_nonneg).symm

end TimeTraps.Probability
