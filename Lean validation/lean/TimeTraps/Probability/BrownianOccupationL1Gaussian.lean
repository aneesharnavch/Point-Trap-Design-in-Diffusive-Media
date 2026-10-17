module

public import TimeTraps.Probability.BrownianOccupationTimeBound
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-! Actual scalar L1 functions are integrable against every positive-time
Brownian marginal. The estimate uses the Gaussian density peak. The
pre-Brownian hypothesis fixes the marginal to N(0,t), including the
zero initial law; no transition law or arbitrary-start premise is used. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

theorem gaussianPDFReal_le_peak (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal m v x ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
  unfold gaussianPDFReal
  have he : Real.exp (-(x - m) ^ 2 / (2 * v)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
      (mul_nonneg (by norm_num) v.coe_nonneg))
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (Real.sqrt_nonneg _))

theorem gaussian_L1_weight_integrable {g : ℝ → ℝ} (hg : Integrable g)
    (m : ℝ) (v : ℝ≥0) : Integrable (fun x => g x * gaussianPDFReal m v x) := by
  apply hg.mul_bdd (stronglyMeasurable_gaussianPDFReal m v).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg m v x)]
    exact gaussianPDFReal_le_peak m v x

theorem gaussian_L1_integrable {g : ℝ → ℝ} (hg : Integrable g)
    (m : ℝ) {v : ℝ≥0} (hv : 0 < v) : Integrable g (gaussianReal m v) := by
  rw [gaussianReal_of_var_ne_zero m hv.ne']
  apply (integrable_withDensity_iff (measurable_gaussianPDF m v)
    (Eventually.of_forall fun _ => gaussianPDF_lt_top)).mpr
  simpa only [toReal_gaussianPDF] using gaussian_L1_weight_integrable hg m v

theorem gaussian_L1_integral_abs_bound {g : ℝ → ℝ} (hg : Integrable g)
    (m : ℝ) {v : ℝ≥0} (hv : 0 < v) :
    (∫ x, |g x| ∂gaussianReal m v) ≤
      (Real.sqrt (2 * Real.pi * v))⁻¹ * ∫ x, |g x| := by
  rw [integral_gaussianReal_eq_integral_smul hv.ne']
  calc
    _ ≤ ∫ x, (Real.sqrt (2 * Real.pi * v))⁻¹ * |g x| := by
      apply integral_mono
        (by simpa only [Real.norm_eq_abs, smul_eq_mul, mul_comm] using
          gaussian_L1_weight_integrable hg.norm m v)
        (hg.norm.const_mul _)
      intro x
      exact mul_le_mul_of_nonneg_right (gaussianPDFReal_le_peak m v x) (abs_nonneg _)
    _ = _ := integral_const_mul _ _

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownian_eval_L1_integrable (hB : IsPreBrownianReal B P)
    {g : ℝ → ℝ} (hg : Integrable g) {t : ℝ≥0} (ht : 0 < t) :
    Integrable (fun ω => g (B t ω)) P := by
  have hi : Integrable g (P.map (B t)) := by
    rw [(hB.hasLaw_eval t).map_eq]
    exact gaussian_L1_integrable hg 0 ht
  exact hi.comp_aemeasurable (hB.hasLaw_eval t).aemeasurable

theorem brownian_eval_L1_abs_bound (hB : IsPreBrownianReal B P)
    {g : ℝ → ℝ} (hg : Integrable g) {t : ℝ≥0} (ht : 0 < t) :
    (∫ ω, |g (B t ω)| ∂P) ≤ (Real.sqrt (2 * Real.pi * t))⁻¹ * ∫ x, |g x| := by
  calc
    _ = ∫ x, |g x| ∂gaussianReal 0 t :=
      (hB.hasLaw_eval t).integral_comp (gaussian_L1_integrable hg 0 ht).norm.aestronglyMeasurable
    _ ≤ _ := gaussian_L1_integral_abs_bound hg 0 ht

end TimeTraps.Probability
