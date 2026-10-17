module

public import TimeTraps.Probability.ReflectedInteriorOccupationMeanSeries

@[expose] public section

/-! The fixed-interior-level occupation density has the time-integrated
actual reflected Gaussian density as its expectation. Existing L²
moments of the actual correction prove finiteness of this time integral;
the zero horizon is included. This is a mean identity, not a PCAF or Revuz
characterization. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

theorem reflectedGaussianDensity_time_intervalIntegrable (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x a : ℝ) (T : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => reflectedGaussianDensity L x (2 * D * s).toNNReal a)
      volume 0 T.val := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  have hi := (reflectedInteriorOccupationCoefficient_memLp L hL D hD x a T).integrable (by norm_num)
  have hnon : ∀ ω, 0 ≤ reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a T ω :=
    fun ω => div_nonneg (reflectedInteriorCorrection_nonneg x hσ L a T ω) (sq_nonneg _)
  have he := (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hnon)).trans
    (reflectedInteriorOccupationCoefficient_gaussian_lintegral L hL x a hσ T)
  rw [Real.sq_sqrt (show 0 ≤ 2 * D by positivity)] at he
  have hf : (∫⁻ s in Ioc (0 : ℝ) T.val, reflectedGaussianKernel L x (2 * D * s).toNNReal a) ≠ ∞ := by
    rw [← he]
    exact ENNReal.ofReal_ne_top
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mpr
  exact integrable_toReal_of_lintegral_ne_top
    (reflectedGaussianKernel_time_measurable L x (2 * D) a).aemeasurable hf

theorem reflectedInteriorOccupationCoefficient_gaussian_mean (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x a : ℝ) (T : ℝ≥0) :
    (∫ ω, reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a T ω ∂brownianDyadicMeasure) =
      ∫ s in (0 : ℝ)..T.val, reflectedGaussianDensity L x (2 * D * s).toNNReal a := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  have hi := (reflectedInteriorOccupationCoefficient_memLp L hL D hD x a T).integrable (by norm_num)
  have hnon : ∀ ω, 0 ≤ reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a T ω :=
    fun ω => div_nonneg (reflectedInteriorCorrection_nonneg x hσ L a T ω) (sq_nonneg _)
  have he := (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hnon)).trans
    (reflectedInteriorOccupationCoefficient_gaussian_lintegral L hL x a hσ T)
  rw [Real.sq_sqrt (show 0 ≤ 2 * D by positivity)] at he
  have hf : ∀ᵐ s ∂(volume : Measure ℝ).restrict (Ioc (0 : ℝ) T.val),
      reflectedGaussianKernel L x (2 * D * s).toNNReal a < ∞ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact lt_top_iff_ne_top.mpr (reflectedGaussianKernel_ne_top hL x
      (Real.toNNReal_pos.mpr (mul_pos (by positivity : 0 < 2 * D) hs.1)) a)
  calc
    _ = (ENNReal.ofReal (∫ ω, reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a T ω
        ∂brownianDyadicMeasure)).toReal := (ENNReal.toReal_ofReal (integral_nonneg hnon)).symm
    _ = (∫⁻ s in Ioc (0 : ℝ) T.val, reflectedGaussianKernel L x (2 * D * s).toNNReal a).toReal :=
      congrArg ENNReal.toReal he
    _ = ∫ s in Ioc (0 : ℝ) T.val, reflectedGaussianDensity L x (2 * D * s).toNNReal a :=
      (integral_toReal (reflectedGaussianKernel_time_measurable L x (2 * D) a).aemeasurable hf).symm
    _ = _ := (intervalIntegral.integral_of_le T.coe_nonneg).symm

theorem foldedOccupationDensity_level_gaussian_mean (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x a : ℝ) (ha : a ∈ Ioo 0 L) (T : ℝ≥0) :
    (∫ ω, foldedOccupationDensity L D x T ω a ∂brownianDyadicMeasure) =
      ∫ s in (0 : ℝ)..T.val, reflectedGaussianDensity L x (2 * D * s).toNNReal a := by
  have he := (reflectedInteriorOccupationCoefficient_density_all_times_ae L hL D hD x a ha).mono
    (fun _ hω => hω T)
  exact (integral_congr_ae he).symm.trans
    (reflectedInteriorOccupationCoefficient_gaussian_mean L hL D hD x a T)

theorem reflectedInteriorCorrection_normalized_gaussian_mean (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x a : ℝ) (T : ℝ≥0) :
    (∫ ω, reflectedInteriorCorrection x (Real.sqrt (2 * D)) L a T ω / (2 * D) ∂brownianDyadicMeasure) =
      ∫ s in (0 : ℝ)..T.val, reflectedGaussianDensity L x (2 * D * s).toNNReal a := by
  have he := reflectedInteriorOccupationCoefficient_gaussian_mean L hL D hD x a T
  unfold reflectedInteriorOccupationCoefficient at he
  simpa only [Real.sq_sqrt (show 0 ≤ 2 * D by positivity)] using he

end TimeTraps.Probability
