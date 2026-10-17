module

public import TimeTraps.Probability.BrownianItoTaylorSum
public import TimeTraps.Probability.BrownianQuadraticVariation

@[expose] public section

/-! The accumulated Taylor error tends to zero in actual L1 on dyadic
partitions, at an explicit constant times the square root of the mesh. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory TimeTraps.Analysis Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {F : ℝ → ℝ}

theorem brownianItoTaylorDyadic_mean_abs_le (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hF : ContDiff ℝ 3 F)
    {M : ℝ} (hb : ∀ z, |iteratedDeriv 3 F z| ≤ M) (T : ℝ≥0) (n : ℕ) :
    (∫ ω, |brownianItoTaylorSum B F (brownianDyadicGrid T n) ω| ∂P) ≤
      (M / 6) * Real.sqrt 3 * T.val * Real.sqrt (T.val / (2 : ℝ) ^ n) := by
  have h := brownianItoTaylorSum_mean_abs_le hB hBm hF hb (brownianDyadicGrid T n)
  simp only [brownianDyadicGrid_gap, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  apply h.trans_eq
  field_simp

theorem brownianItoTaylorDyadic_mean_abs_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hF : ContDiff ℝ 3 F)
    {M : ℝ} (hb : ∀ z, |iteratedDeriv 3 F z| ≤ M) (T : ℝ≥0) :
    Tendsto (fun n => ∫ ω, |brownianItoTaylorSum B F (brownianDyadicGrid T n) ω| ∂P)
      atTop (𝓝 0) := by
  have hmesh : Tendsto (fun n => T.val / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, one_mul, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul T.val
  have hrate : Tendsto (fun n => (M / 6) * Real.sqrt 3 * T.val *
      Real.sqrt (T.val / (2 : ℝ) ^ n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero, mul_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hmesh).const_mul
        ((M / 6) * Real.sqrt 3 * T.val)
  exact squeeze_zero (fun n => integral_nonneg (fun ω => abs_nonneg _))
    (fun n => brownianItoTaylorDyadic_mean_abs_le hB hBm hF hb T n) hrate

theorem brownianItoTaylorDyadic_L1_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hF : ContDiff ℝ 3 F)
    {M : ℝ} (hb : ∀ z, |iteratedDeriv 3 F z| ≤ M) (T : ℝ≥0) :
    Tendsto (fun n => brownianItoTaylorSumL1 B F (brownianDyadicGrid T n)
      (brownianItoTaylorSum_integrable hB hBm hF hb _)) atTop (𝓝 (0 : Lp ℝ 1 P)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero, brownianItoTaylorSumL1_norm]
  exact brownianItoTaylorDyadic_mean_abs_tendsto hB hBm hF hb T

theorem brownianDyadicPath_taylor_L1_tendsto (hF : ContDiff ℝ 3 F)
    {M : ℝ} (hb : ∀ z, |iteratedDeriv 3 F z| ≤ M) (T : ℝ≥0) :
    Tendsto (fun n => brownianItoTaylorSumL1 brownianDyadicPath F (brownianDyadicGrid T n)
      (brownianItoTaylorSum_integrable brownianDyadicPath_isPreBrownianReal
        brownianDyadicPath_measurable hF hb _)) atTop (𝓝 (0 : Lp ℝ 1 brownianDyadicMeasure)) :=
  brownianItoTaylorDyadic_L1_tendsto brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable hF hb T

end TimeTraps.Probability
