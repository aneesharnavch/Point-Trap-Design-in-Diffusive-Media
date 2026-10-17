module

public import TimeTraps.Probability.BrownianLocalTimeLevelCompensation

@[expose] public section

/-! Uniform actual L² bounds in the spatial level. Absolute displacement
is bounded by the Brownian increment, while the sign integral has squared
L² norm exactly T, using the derived product-a.e. level exclusion. The
Tanaka compensation therefore has norm at most 2 sqrt T. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianTanakaDifference_increment_bound (B : ℝ≥0 → Ω → ℝ)
    (a : ℝ) (T : ℝ≥0) (ω : Ω) :
    |brownianTanakaDifference B a T ω| ≤ |B T ω - B 0 ω| := by
  have h := abs_abs_sub_abs_le_abs_sub (B T ω - a) (B 0 ω - a)
  simpa only [brownianTanakaDifference, sub_sub_sub_cancel_right] using h

theorem brownianTanakaDifferenceL2_norm_le (hB : IsPreBrownianReal B P) (a : ℝ) (T : ℝ≥0) :
    ‖brownianTanakaDifferenceL2 B a T (brownianTanakaDifference_memLp hB a T)‖ ≤ Real.sqrt T.val := by
  have hs : ‖brownianTanakaDifferenceL2 B a T (brownianTanakaDifference_memLp hB a T)‖ ^ 2 ≤ T.val := by
    calc
      _ = ∫ ω, brownianTanakaDifference B a T ω ^ 2 ∂P :=
        TimeTraps.Analysis.memLp_norm_toLp_sq (brownianTanakaDifference_memLp hB a T)
      _ ≤ ∫ ω, (B T ω - B 0 ω) ^ 2 ∂P := by
        apply integral_mono (brownianTanakaDifference_memLp hB a T).integrable_sq
          (brownian_increment_integrable_sq hB 0 T)
        intro ω
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr
          (brownianTanakaDifference_increment_bound B a T ω)
      _ = T.val := by
        simpa using brownian_increment_second_moment hB 0 T
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  exact hs.trans_eq (Real.sq_sqrt T.coe_nonneg).symm

theorem brownianSignIntegral_norm_sq (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    ‖brownianSignIntegral hB hBm hjoint a T‖ ^ 2 = T.val := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  calc
    _ = ∫ ω, brownianSignIntegral hB hBm hjoint a T ω ^ 2 ∂P := by
      simpa only [Lp.toLp_coeFn] using
        TimeTraps.Analysis.memLp_norm_toLp_sq (Lp.memLp (brownianSignIntegral hB hBm hjoint a T))
    _ = ∫ p, brownianSignProcess B a T p ^ 2 ∂(volume : Measure ℝ).prod P :=
      brownianSignIntegral_isometry hB hBm hjoint a T
    _ = ∫ p : ℝ × Ω, brownianIntervalIndicator 0 T p.1 * (1 : ℝ) ∂volume.prod P := by
      apply integral_congr_ae
      filter_upwards [brownian_positive_time_ne_level_prod_ae hB hjoint a T] with p hp
      change ((Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 *
          Real.sign (B p.1.toNNReal p.2 - a)) ^ 2 =
        (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 * 1
      by_cases ht : p.1 ∈ Ioc (0 : ℝ) T.val
      · simp only [indicator_of_mem ht, one_mul, mul_one]
        rcases Real.sign_apply_eq_of_ne_zero _ (sub_ne_zero.mpr (hp ht)) with hn | hn <;>
          rw [hn] <;> norm_num
      · simp only [indicator_of_notMem ht, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    _ = (∫ s, brownianIntervalIndicator 0 T s) * ∫ _ : Ω, (1 : ℝ) ∂P :=
      integral_prod_mul (μ := volume) (ν := P) (L := ℝ) (brownianIntervalIndicator 0 T) (fun _ => 1)
    _ = T.val := by
      rw [brownianIntervalIndicator_integral]
      simp

theorem brownianSignIntegral_norm (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    ‖brownianSignIntegral hB hBm hjoint a T‖ = Real.sqrt T.val := by
  have h := congrArg Real.sqrt (brownianSignIntegral_norm_sq hB hBm hjoint a T)
  simpa only [Real.sqrt_sq (norm_nonneg _)] using h

theorem brownianTanakaCompensation_norm_le (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    ‖brownianTanakaCompensation hB hBm hjoint a T‖ ≤ 2 * Real.sqrt T.val := by
  calc
    _ ≤ ‖brownianTanakaDifferenceL2 B a T (brownianTanakaDifference_memLp hB a T)‖ +
        ‖brownianSignIntegral hB hBm hjoint a T‖ := norm_sub_le _ _
    _ ≤ Real.sqrt T.val + Real.sqrt T.val :=
      add_le_add (brownianTanakaDifferenceL2_norm_le hB a T)
        (brownianSignIntegral_norm hB hBm hjoint a T).le
    _ = _ := by ring

theorem brownianDyadicTanakaCompensation_norm_le (a : ℝ) (T : ℝ≥0) :
    ‖brownianTanakaCompensation brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
      brownianDyadicPath_jointly_measurable a T‖ ≤ 2 * Real.sqrt T.val :=
  brownianTanakaCompensation_norm_le brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable a T

end TimeTraps.Probability
