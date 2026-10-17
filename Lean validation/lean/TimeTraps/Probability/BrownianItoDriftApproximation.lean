module

public import TimeTraps.Probability.BrownianItoDriftStep

@[expose] public section

/-! The actual left dyadic time sums converge in L² to the actual
ordinary Brownian time integral. The squared error is at most K²T³/2ⁿ. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {g : ℝ → ℝ} {K : ℝ≥0}

theorem brownianItoDrift_error_integral_ae (hB : IsPreBrownianReal B P)
    (hg : LipschitzWith K g) (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (T : ℝ≥0) (n : ℕ) :
    (fun ω => ∫ s in (0 : ℝ)..T.val,
      brownianLipschitzStepProcess B g T n (s, ω) - brownianLipschitzProcess B g T (s, ω)) =ᵐ[P]
      (fun ω => brownianItoDriftSum B g T n ω - brownianItoDrift B g T ω) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  filter_upwards [brownian_timeIntegral_sections (brownianLipschitzProcess_memLp hB hg hjoint T) T.val]
    with ω hω
  have ht := (intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mpr hω
  calc
    _ = (∫ s in (0 : ℝ)..T.val, brownianLipschitzStepProcess B g T n (s, ω)) -
        ∫ s in (0 : ℝ)..T.val, brownianLipschitzProcess B g T (s, ω) :=
      intervalIntegral.integral_sub (brownianItoDriftSum_step_integrable B g T n ω).intervalIntegrable ht
    _ = _ := congrArg₂ (fun x y : ℝ => x - y)
      (brownianItoDriftSum_step_integral B g T n ω) (brownianItoDrift_process_integral B g T ω)

theorem brownianItoDrift_error_secondMoment_le (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : LipschitzWith K g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) (n : ℕ) :
    (∫ ω, (brownianItoDriftSum B g T n ω - brownianItoDrift B g T ω) ^ 2 ∂P) ≤
      K.val ^ 2 * T.val ^ 3 / (2 : ℝ) ^ n := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let E : Lp ℝ 2 ((volume : Measure ℝ).prod P) :=
    (brownianLipschitzStepIntegrand hB hBm hg T n : Lp ℝ 2 ((volume : Measure ℝ).prod P)) -
      brownianLipschitzProcessL2 hB hg hjoint T
  have hE : E =ᵐ[volume.prod P]
      (fun p => brownianLipschitzStepProcess B g T n p - brownianLipschitzProcess B g T p) := by
    filter_upwards [Lp.coeFn_sub
        (brownianLipschitzStepIntegrand hB hBm hg T n : Lp ℝ 2 ((volume : Measure ℝ).prod P))
        (brownianLipschitzProcessL2 hB hg hjoint T),
      brownianLipschitzStepIntegrand_coe hB hBm hg T n, brownianLipschitzProcessL2_coe hB hg hjoint T]
      with p hd hs ht
    rw [hd, Pi.sub_apply, hs, ht]
  have he := (memLp_congr_ae hE).mp (Lp.memLp E)
  have hn : ‖E‖ ^ 2 = ∫ p,
      (brownianLipschitzStepProcess B g T n p - brownianLipschitzProcess B g T p) ^ 2 ∂volume.prod P := by
    calc
      _ = ∫ p, E p ^ 2 ∂volume.prod P := by
        simpa only [Lp.toLp_coeFn] using TimeTraps.Analysis.memLp_norm_toLp_sq (Lp.memLp E)
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hE] with p hp
        rw [hp]
  calc
    _ = ∫ ω, (∫ s in (0 : ℝ)..T.val,
        brownianLipschitzStepProcess B g T n (s, ω) - brownianLipschitzProcess B g T (s, ω)) ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [brownianItoDrift_error_integral_ae hB hg hjoint T n] with ω hω
      rw [hω]
    _ ≤ T.val * ∫ p,
        (brownianLipschitzStepProcess B g T n p - brownianLipschitzProcess B g T p) ^ 2 ∂volume.prod P :=
      brownian_timeIntegral_secondMoment_le he T.val T.coe_nonneg
    _ = T.val * ‖E‖ ^ 2 := congrArg (fun r => T.val * r) hn.symm
    _ ≤ T.val * (K.val ^ 2 * T.val ^ 2 / (2 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left (brownianLipschitzStep_process_error_le hB hBm hg hjoint T n) T.coe_nonneg
    _ = _ := by ring

theorem brownianItoDriftL2_error_le (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : LipschitzWith K g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) (n : ℕ)
    (hSum : MemLp (brownianItoDriftSum B g T n) 2 P) (hDrift : MemLp (brownianItoDrift B g T) 2 P) :
    ‖brownianItoDriftSumL2 B g T n hSum - brownianItoDriftL2 B g T hDrift‖ ^ 2 ≤
      K.val ^ 2 * T.val ^ 3 / (2 : ℝ) ^ n := by
  let D : Lp ℝ 2 P := brownianItoDriftSumL2 B g T n hSum - brownianItoDriftL2 B g T hDrift
  have hD : D =ᵐ[P] (fun ω => brownianItoDriftSum B g T n ω - brownianItoDrift B g T ω) := by
    filter_upwards [Lp.coeFn_sub (brownianItoDriftSumL2 B g T n hSum) (brownianItoDriftL2 B g T hDrift),
      brownianItoDriftSumL2_coe B g T n hSum, brownianItoDriftL2_coe B g T hDrift] with ω hd hs ht
    rw [hd, Pi.sub_apply, hs, ht]
  calc
    _ = ∫ ω, D ω ^ 2 ∂P := by
      simpa only [Lp.toLp_coeFn] using TimeTraps.Analysis.memLp_norm_toLp_sq (Lp.memLp D)
    _ = ∫ ω, (brownianItoDriftSum B g T n ω - brownianItoDrift B g T ω) ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [hD] with ω hω
      rw [hω]
    _ ≤ _ := brownianItoDrift_error_secondMoment_le hB hBm hg hjoint T n

theorem brownianItoDriftL2_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : LipschitzWith K g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    Tendsto (fun n => brownianItoDriftSumL2 B g T n (brownianItoDriftSum_memLp hB hg T n))
      atTop (𝓝 (brownianItoDriftL2 B g T (brownianItoDrift_memLp hB hg hjoint T))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb : Tendsto (fun n => K.val ^ 2 * T.val ^ 3 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, one_mul, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (K.val ^ 2 * T.val ^ 3)
  have hs := squeeze_zero (fun n => sq_nonneg
    ‖brownianItoDriftSumL2 B g T n (brownianItoDriftSum_memLp hB hg T n) -
      brownianItoDriftL2 B g T (brownianItoDrift_memLp hB hg hjoint T)‖)
    (fun n => brownianItoDriftL2_error_le hB hBm hg hjoint T n _ _) hb
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hr

theorem brownianDyadicPath_itoDrift_converges (hg : LipschitzWith K g) (T : ℝ≥0) :
    Tendsto (fun n => brownianItoDriftSumL2 brownianDyadicPath g T n
      (brownianItoDriftSum_memLp brownianDyadicPath_isPreBrownianReal hg T n)) atTop
      (𝓝 (brownianItoDriftL2 brownianDyadicPath g T
        (brownianItoDrift_memLp brownianDyadicPath_isPreBrownianReal hg brownianDyadicPath_jointly_measurable T))) :=
  brownianItoDriftL2_tendsto brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    hg brownianDyadicPath_jointly_measurable T

end TimeTraps.Probability
