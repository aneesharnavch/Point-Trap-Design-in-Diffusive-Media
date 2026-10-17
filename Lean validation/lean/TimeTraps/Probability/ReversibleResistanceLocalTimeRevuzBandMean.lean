module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeRevuzBound
public import TimeTraps.Probability.ReversibleResistancePhysicalBandLimit
public import TimeTraps.Analysis.IntegralCauchySchwarz

@[expose] public section

/-! Genuine physical occupation-band expectations converge to the actual
fixed-site local-time expectation. Square-integrability and Cauchy--Schwarz
justify passage from the proved mean-square limit to ordinary expectations. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

theorem reversibleResistancePhysicalOccupationBand_memLp_two (A : IntervalMedium) (x a h : ℝ) (T : ℝ≥0) :
    MemLp (reversibleResistancePhysicalOccupationBand A x a h T) 2 brownianDyadicMeasure := by
  change MemLp (fun ω => brownianItoDrift (reversibleResistancePath A x)
    (brownianBandIndicator a h) T ω / resistancePhysicalBandMass A a h) 2 brownianDyadicMeasure
  simpa only [div_eq_mul_inv] using
    (brownianItoDrift_bounded_memLp (brownianBandIndicator_measurable a h)
      (reversibleResistancePath_jointlyMeasurable A x) (brownianBandIndicator_abs_le_one a h) T).mul_const
        (resistancePhysicalBandMass A a h)⁻¹

theorem brownian_integral_sq_le_integral_sq {f : (ℕ → ℝ) → ℝ} (hf : MemLp f 2 brownianDyadicMeasure) :
    (∫ ω, f ω ∂brownianDyadicMeasure) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂brownianDyadicMeasure := by
  simpa using memLp_integral_mul_sq_le hf (memLp_const (μ := brownianDyadicMeasure) (p := 2) (1 : ℝ))

theorem reversibleResistancePhysicalOccupationBand_mean_tendsto (A : IntervalMedium) (x : ℝ)
    (a : Ioo A.source.left A.source.right) (T : ℝ≥0) :
    Tendsto (fun h : ℝ => ∫ ω, reversibleResistancePhysicalOccupationBand A x a.val h T ω ∂brownianDyadicMeasure)
      (𝓝[>] 0) (𝓝 (∫ ω, reversibleResistanceLocalTime A x a.val T ω ∂brownianDyadicMeasure)) := by
  have hs : Tendsto (fun h : ℝ =>
      ((∫ ω, reversibleResistancePhysicalOccupationBand A x a.val h T ω ∂brownianDyadicMeasure) -
        ∫ ω, reversibleResistanceLocalTime A x a.val T ω ∂brownianDyadicMeasure) ^ 2) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun h => sq_nonneg _)) ?_
      (reversibleResistancePhysicalOccupationBand_square_tendsto A x a T)
    apply Eventually.of_forall
    intro h
    have hB := reversibleResistancePhysicalOccupationBand_memLp_two A x a.val h T
    have hL := reversibleResistanceLocalTime_memLp_two A x a.val T
    have he := brownian_integral_sq_le_integral_sq (hB.sub hL)
    simp only [Pi.sub_apply] at he
    rw [integral_sub (hB.integrable (by norm_num)) (hL.integrable (by norm_num))] at he
    exact he
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.norm_eq_abs, Real.sqrt_zero] using ht

end TimeTraps.Probability
