module

public import TimeTraps.Probability.BrownianLocalTimeGaussianMean
public import TimeTraps.Probability.BrownianAffineLocalTimeData

@[expose] public section

/-! Affine scaling of the actual local-time mean. The occupation density
for x + sigma B has mean equal to the time integral of N(x,sigma² s)'s
density, with an extended nonnegative version for subsequent Tonelli sums. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

theorem gaussianPDFReal_affine_scale (x a : ℝ) {σ : ℝ} (hσ : 0 < σ) (v : ℝ≥0) :
    σ⁻¹ * gaussianPDFReal 0 v ((a - x) / σ) =
      gaussianPDFReal x (NNReal.mk (σ ^ 2) (sq_nonneg σ) * v) a := by
  rw [div_eq_mul_inv, mul_comm (a - x) σ⁻¹, gaussianPDFReal_inv_mul hσ.ne',
    abs_of_pos hσ, mul_zero, ← mul_assoc, inv_mul_cancel₀ hσ.ne', one_mul,
    gaussianPDFReal_sub, zero_add]

theorem gaussianPDFReal_affine_time_intervalIntegrable (x a : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => gaussianPDFReal x (σ ^ 2 * s).toNNReal a) volume 0 T.val := by
  have he (s : ℝ) : σ⁻¹ * gaussianPDFReal 0 s.toNNReal ((a - x) / σ) =
      gaussianPDFReal x (σ ^ 2 * s).toNNReal a := by
    rw [gaussianPDFReal_affine_scale x a hσ, Real.toNNReal_mul (sq_nonneg σ),
      Real.toNNReal_of_nonneg (sq_nonneg σ)]
  simpa only [he] using
    (gaussianPDFReal_time_intervalIntegrable 0 ((a - x) / σ) T).const_mul σ⁻¹

theorem affineBrownianOccupationDensity_gaussian_mean (x a : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    (∫ ω, affineBrownianOccupationDensity x σ a T ω ∂brownianDyadicMeasure) =
      ∫ s in (0 : ℝ)..T.val, gaussianPDFReal x (σ ^ 2 * s).toNNReal a := by
  unfold affineBrownianOccupationDensity
  rw [integral_const_mul, brownianLocalTimeTimeField_gaussian_mean,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  change σ⁻¹ * gaussianPDFReal 0 s.toNNReal ((a - x) / σ) =
    gaussianPDFReal x (σ ^ 2 * s).toNNReal a
  rw [gaussianPDFReal_affine_scale x a hσ, Real.toNNReal_mul (sq_nonneg σ),
    Real.toNNReal_of_nonneg (sq_nonneg σ)]

theorem affineBrownianOccupationDensity_gaussian_lintegral (x a : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    (∫⁻ ω, ENNReal.ofReal (affineBrownianOccupationDensity x σ a T ω) ∂brownianDyadicMeasure) =
      ∫⁻ s in Ioc (0 : ℝ) T.val, gaussianPDF x (σ ^ 2 * s).toNNReal a := by
  have hi : Integrable (affineBrownianOccupationDensity x σ a T) brownianDyadicMeasure :=
    ((brownianLocalTimeTimeField_memLp ((a - x) / σ) T).const_mul σ⁻¹).integrable (by norm_num)
  have hk := (intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mp
    (gaussianPDFReal_affine_time_intervalIntegrable x a hσ T)
  calc
    _ = ENNReal.ofReal (∫ ω, affineBrownianOccupationDensity x σ a T ω ∂brownianDyadicMeasure) :=
      (ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall (fun ω => affineBrownianOccupationDensity_nonneg x hσ a T ω))).symm
    _ = ENNReal.ofReal (∫ s in (0 : ℝ)..T.val, gaussianPDFReal x (σ ^ 2 * s).toNNReal a) :=
      congrArg ENNReal.ofReal (affineBrownianOccupationDensity_gaussian_mean x a hσ T)
    _ = ENNReal.ofReal (∫ s in Ioc (0 : ℝ) T.val, gaussianPDFReal x (σ ^ 2 * s).toNNReal a) :=
      congrArg ENNReal.ofReal (intervalIntegral.integral_of_le T.coe_nonneg)
    _ = _ := ofReal_integral_eq_lintegral_ofReal hk
      (Eventually.of_forall (fun s => gaussianPDFReal_nonneg x (σ ^ 2 * s).toNNReal a))

end TimeTraps.Probability
