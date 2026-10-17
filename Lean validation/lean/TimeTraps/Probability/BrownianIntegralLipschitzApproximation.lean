module

public import TimeTraps.Probability.BrownianIntegralLipschitzStep

@[expose] public section

/-! The product-L² error of the left dyadic approximation is at most
K² T² / 2ⁿ. The proof transfers the checked Brownian increment-moment
estimate through the pointwise Lipschitz inequality. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {g : ℝ → ℝ} {K : ℝ≥0}

theorem brownianLipschitzStep_process_error_le (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : LipschitzWith K g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) (n : ℕ) :
    ‖(brownianLipschitzStepIntegrand hB hBm hg T n : Lp ℝ 2 ((volume : Measure ℝ).prod P)) -
      brownianLipschitzProcessL2 hB hg hjoint T‖ ^ 2 ≤ K.val ^ 2 * T.val ^ 2 / (2 : ℝ) ^ n := by
  have hn : ‖(brownianLipschitzStepIntegrand hB hBm hg T n : Lp ℝ 2 ((volume : Measure ℝ).prod P)) -
      brownianLipschitzProcessL2 hB hg hjoint T‖ ≤ K.val *
      ‖(brownianSquareStepIntegrand hB hBm T n : Lp ℝ 2 ((volume : Measure ℝ).prod P)) -
        brownianSquareProcessL2 hB hjoint T‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub
      (brownianLipschitzStepIntegrand hB hBm hg T n : Lp ℝ 2 ((volume : Measure ℝ).prod P))
      (brownianLipschitzProcessL2 hB hg hjoint T),
      Lp.coeFn_sub (brownianSquareStepIntegrand hB hBm T n : Lp ℝ 2 ((volume : Measure ℝ).prod P))
        (brownianSquareProcessL2 hB hjoint T),
      brownianLipschitzStepIntegrand_coe hB hBm hg T n, brownianLipschitzProcessL2_coe hB hg hjoint T,
      brownianSquareStepIntegrand_coe hB hBm T n, brownianSquareProcessL2_coe hB hjoint T]
      with p hdg hdb hsg htg hsb htb
    rw [hdg, hdb]
    simp only [Pi.sub_apply]
    rw [hsg, htg, hsb, htb, brownianLipschitzStep_error_identity]
    exact hg.norm_sub_le _ _
  calc
    _ ≤ (K.val * ‖(brownianSquareStepIntegrand hB hBm T n : Lp ℝ 2 ((volume : Measure ℝ).prod P)) -
        brownianSquareProcessL2 hB hjoint T‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg K.coe_nonneg (norm_nonneg _))).mpr hn
    _ = K.val ^ 2 * ‖(brownianSquareStepIntegrand hB hBm T n : Lp ℝ 2 ((volume : Measure ℝ).prod P)) -
        brownianSquareProcessL2 hB hjoint T‖ ^ 2 := mul_pow _ _ _
    _ ≤ K.val ^ 2 * (T.val ^ 2 / (2 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left (brownianSquareStep_process_error_le hB hBm hjoint T n) (sq_nonneg _)
    _ = _ := by ring

theorem brownianLipschitzStep_process_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : LipschitzWith K g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    Tendsto (fun n => (brownianLipschitzStepIntegrand hB hBm hg T n : Lp ℝ 2 ((volume : Measure ℝ).prod P)))
      atTop (𝓝 (brownianLipschitzProcessL2 hB hg hjoint T)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb : Tendsto (fun n => K.val ^ 2 * T.val ^ 2 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, one_mul, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (K.val ^ 2 * T.val ^ 2)
  have hs := squeeze_zero (fun n => sq_nonneg
    ‖(brownianLipschitzStepIntegrand hB hBm hg T n : Lp ℝ 2 ((volume : Measure ℝ).prod P)) -
      brownianLipschitzProcessL2 hB hg hjoint T‖)
    (brownianLipschitzStep_process_error_le hB hBm hg hjoint T) hb
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hr

end TimeTraps.Probability
