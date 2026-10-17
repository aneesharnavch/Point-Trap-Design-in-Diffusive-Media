module

public import TimeTraps.Probability.GraphPointLocalTimeDiscountEnvelope
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! A genuine product-integrability criterion for the exponential
local-time envelope. The proof first bounds the integral of the norm
of each section and then applies the product-integrability theorem. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter

theorem graphPointDiscount_product_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {α C : ℝ} (hα : 0 < α)
    (F : ℝ × Ω → ℝ) (hFm : StronglyMeasurable F)
    (hFi : ∀ t, Integrable (fun ω => F (t, ω)) μ)
    (hFb : ∀ t, 0 < t → (∫ ω, ‖F (t, ω)‖ ∂μ) ≤ C * (t + 2 * Real.sqrt t)) :
    Integrable (fun q : ℝ × Ω => Real.exp (-(α * q.1)) * F q)
      ((volume.restrict (Ioi (0 : ℝ))).prod μ) := by
  let G : ℝ × Ω → ℝ := fun q => Real.exp (-(α * q.1)) * F q
  have hGm : StronglyMeasurable G :=
    (((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).stronglyMeasurable).comp_measurable
      measurable_fst).mul hFm
  apply (integrable_prod_iff hGm.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (fun t => (hFi t).const_mul (Real.exp (-(α * t)))), ?_⟩
  apply ((graphPointDiscount_envelope_integrable hα).const_mul C).mono'
    hGm.norm.integral_prod_right'.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have he : (∫ ω, ‖G (t, ω)‖ ∂μ) = Real.exp (-(α * t)) * ∫ ω, ‖F (t, ω)‖ ∂μ := by
    simp only [G, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, integral_const_mul]
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)), he]
  calc
    _ ≤ Real.exp (-(α * t)) * (C * (t + 2 * Real.sqrt t)) :=
      mul_le_mul_of_nonneg_left (hFb t ht) (Real.exp_pos _).le
    _ = _ := by ring

end TimeTraps.Probability
