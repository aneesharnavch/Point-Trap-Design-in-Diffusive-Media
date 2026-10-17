module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-! A genuine Banach-valued Laplace transform of a time primitive.
All infinite integrals follow from a bound on the original curve; the
identity is proved by the improper fundamental theorem of calculus. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem boundedContinuousLaplaceOne_integrable {f : ℝ → F} (hf : Continuous f)
    {C : ℝ} (hC : ∀ t, 0 ≤ t → ‖f t‖ ≤ C) :
    IntegrableOn (fun t => Real.exp (-t) • f t) (Ioi (0 : ℝ)) := by
  have he : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
    simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0
  apply (he.mul_const C).mono'
    ((Real.continuous_exp.comp continuous_neg).smul hf).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := ht.le
  change ‖Real.exp (-t) • f t‖ ≤ Real.exp (-t) * C
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hC t ht0) (Real.exp_pos _).le

theorem boundedContinuousLaplacePrimitive_integrable {f : ℝ → F} (hf : Continuous f)
    {C : ℝ} (hC : ∀ t, 0 ≤ t → ‖f t‖ ≤ C) :
    IntegrableOn (fun t => Real.exp (-t) • ∫ s in (0 : ℝ)..t, f s) (Ioi (0 : ℝ)) := by
  have he : IntegrableOn (fun t : ℝ => Real.exp (-t) * t) (Ioi 0) := by
    simpa only [Real.rpow_one, one_mul, neg_one_mul, mul_neg_one, mul_comm] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := 1)
        (by norm_num) (by norm_num) (by norm_num)
  have hc : Continuous (fun t => ∫ s in (0 : ℝ)..t, f s) :=
    continuous_iff_continuousAt.mpr (fun t => (hf.integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt)
  apply (he.mul_const C).mono'
    ((Real.continuous_exp.comp continuous_neg).smul hc).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := ht.le
  change ‖Real.exp (-t) • ∫ s in (0 : ℝ)..t, f s‖ ≤ Real.exp (-t) * t * C
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hb : ‖∫ s in (0 : ℝ)..t, f s‖ ≤ t * C := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := t) (fun s hs => hC s (by
        rw [uIoc_of_le ht0] at hs
        exact hs.1.le))
    simpa only [sub_zero, abs_of_nonneg ht0, mul_comm] using hh
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le

omit [CompleteSpace F] in
theorem boundedContinuousLaplacePrimitive_tendsto {f : ℝ → F}
    {C : ℝ} (hC : ∀ t, 0 ≤ t → ‖f t‖ ≤ C) :
    Tendsto (fun t => Real.exp (-t) • ∫ s in (0 : ℝ)..t, f s) atTop (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ => Real.exp (-t) * (t * C)) atTop (𝓝 0) := by
    simpa only [pow_one, zero_mul, mul_comm, mul_left_comm, mul_assoc, mul_zero] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).mul_const C
  apply squeeze_zero_norm' _ hlim
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hb : ‖∫ s in (0 : ℝ)..t, f s‖ ≤ t * C := by
      have hh := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := t) (fun s hs => hC s (by
          rw [uIoc_of_le ht] at hs
          exact hs.1.le))
      simpa only [sub_zero, abs_of_nonneg ht, mul_comm] using hh
    exact mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le

theorem boundedContinuousLaplacePrimitive_eq {f : ℝ → F} (hf : Continuous f)
    {C : ℝ} (hC : ∀ t, 0 ≤ t → ‖f t‖ ≤ C) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-t) • ∫ s in (0 : ℝ)..t, f s) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-t) • f t := by
  have hd : ∀ t ∈ Ici (0 : ℝ), HasDerivAt
      (fun r => Real.exp (-r) • ∫ s in (0 : ℝ)..r, f s)
      (Real.exp (-t) • f t - Real.exp (-t) • ∫ s in (0 : ℝ)..t, f s) t := by
    intro t _
    simpa only [Pi.smul_def', Pi.neg_apply, id_eq, mul_neg_one, neg_smul, sub_eq_add_neg, add_comm] using
      (((hasDerivAt_id t).neg.exp).smul (hf.integral_hasStrictDerivAt 0 t).hasDerivAt)
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto' hd
    ((boundedContinuousLaplaceOne_integrable hf hC).sub
      (boundedContinuousLaplacePrimitive_integrable hf hC))
    (boundedContinuousLaplacePrimitive_tendsto hC)
  rw [integral_sub (boundedContinuousLaplaceOne_integrable hf hC)
    (boundedContinuousLaplacePrimitive_integrable hf hC)] at hi
  simp only [intervalIntegral.integral_same, smul_zero, sub_zero] at hi
  exact (sub_eq_zero.mp hi).symm

end TimeTraps.Analysis
