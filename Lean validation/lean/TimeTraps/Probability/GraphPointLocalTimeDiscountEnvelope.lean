module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

/-! Genuine integrability of the exponentially weighted growth envelope
for graph point potentials and local-time means. -/

namespace TimeTraps.Probability

open Set MeasureTheory

theorem graphPointDiscount_linear_integrable {α : ℝ} (hα : 0 < α) :
    IntegrableOn (fun t : ℝ => Real.exp (-(α * t)) * t) (Ioi (0 : ℝ)) volume := by
  simpa only [Real.rpow_one, neg_mul, mul_neg, mul_comm] using
    integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := α)
      (by norm_num) (by norm_num) hα

theorem graphPointDiscount_sqrt_integrable {α : ℝ} (hα : 0 < α) :
    IntegrableOn (fun t : ℝ => Real.exp (-(α * t)) * Real.sqrt t) (Ioi (0 : ℝ)) volume := by
  simpa only [Real.rpow_one, neg_mul, mul_neg, Real.sqrt_eq_rpow, mul_comm] using
    integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1 / 2) (b := α)
      (by norm_num) (by norm_num) hα

theorem graphPointDiscount_envelope_integrable {α : ℝ} (hα : 0 < α) :
    IntegrableOn (fun t : ℝ => Real.exp (-(α * t)) * (t + 2 * Real.sqrt t))
      (Ioi (0 : ℝ)) volume := by
  apply ((graphPointDiscount_linear_integrable hα).add
    ((graphPointDiscount_sqrt_integrable hα).const_mul 2)).congr
  apply Filter.Eventually.of_forall
  intro t
  simp only [Pi.add_apply]
  ring

end TimeTraps.Probability
