module

public import TimeTraps.Probability.StieltjesProduct
public import TimeTraps.Probability.StieltjesExponentialSubstitution
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-! Ordinary exponential integration by parts against a continuous
Stieltjes local-time measure. The time compensator is identified using
the genuine Lebesgue Stieltjes measure, including discount zero. -/

namespace TimeTraps.Probability

open Set MeasureTheory TimeTraps.Analysis
open scoped NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem graphPointDiscount_stieltjes_parts (Q : StieltjesFunction ℝ) (hQ : Continuous Q)
    {α : ℝ} (hα : 0 ≤ α) (T : ℝ≥0) :
    (∫ r in Ioc (0 : ℝ) (T : ℝ), Real.exp (-(α * r)) ∂Q.measure) =
      Real.exp (-(α * (T : ℝ))) * Q (T : ℝ) - Q 0 +
        α * ∫ r in (0 : ℝ)..(T : ℝ), Real.exp (-(α * r)) * Q r := by
  let c : ℝ≥0 := NNReal.mk α hα
  let K : StieltjesFunction ℝ := c • StieltjesFunction.id
  have hK : Continuous K := by
    change Continuous (fun r : ℝ => α * r)
    fun_prop
  have he (r : ℝ) : K r = α * r := rfl
  have hmeasure : K.measure = c • volume := by
    change (c • StieltjesFunction.id).measure = c • volume
    rw [StieltjesFunction.measure_smul, ← Real.volume_eq_stieltjes_id]
  have hsub := stieltjesExponential_integral K hK (fun r => Q r) hQ T
  simp only [NNReal.val_eq_coe] at hsub
  rw [hmeasure, Measure.restrict_smul, integral_smul_nnreal_measure] at hsub
  have hprod := stieltjes_product (stieltjesExponential K hK) Q
    (stieltjesExponential_continuous K hK) hQ 1 T
  simp only [NNReal.val_eq_coe] at hprod
  have hs (r : ℝ) : 1 - stieltjesExponential K hK r = Real.exp (-(α * r)) := by
    rw [stieltjesExponential_apply, he]
    ring
  simp only [hs, mul_zero, neg_zero, Real.exp_zero, one_mul] at hprod
  have hi : (∫ r in Ioc (0 : ℝ) (T : ℝ), Q r ∂(stieltjesExponential K hK).measure) =
      α * ∫ r in (0 : ℝ)..(T : ℝ), Real.exp (-(α * r)) * Q r := by
    rw [hsub]
    change α * (∫ r in Ioc (0 : ℝ) (T : ℝ), Q r * Real.exp (-(α * r))) = _
    congr 1
    rw [intervalIntegral.integral_of_le T.coe_nonneg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun r => mul_comm _ _)
  rw [hi] at hprod
  linarith

end TimeTraps.Probability
