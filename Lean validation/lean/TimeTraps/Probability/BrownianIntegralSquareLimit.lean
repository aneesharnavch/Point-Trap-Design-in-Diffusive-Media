module

public import TimeTraps.Probability.BrownianIntegralSquareFinite

@[expose] public section

/-! Exact L2 convergence of the dyadic stochastic sums in the quadratic
Ito calculation. The target is the actual random variable (B_T^2-T)/2. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianSquareTarget_memLp (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    MemLp (fun ω => (B T ω ^ 2 - T.val) / 2) 2 P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hs : MemLp (fun ω => B T ω ^ 2) 2 P := by
    apply (brownian_increment_square_memLp hB 0 T).ae_eq
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
    rw [hω, sub_zero]
  convert (hs.sub (memLp_const T.val)).const_smul (1 / 2 : ℝ) using 1
  funext ω
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  ring

noncomputable def brownianSquareTarget (hB : IsPreBrownianReal B P) (T : ℝ≥0) : Lp ℝ 2 P :=
  (brownianSquareTarget_memLp hB T).toLp (fun ω => (B T ω ^ 2 - T.val) / 2)

theorem brownianSquareTarget_coe (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    brownianSquareTarget hB T =ᵐ[P] fun ω => (B T ω ^ 2 - T.val) / 2 :=
  (brownianSquareTarget_memLp hB T).coeFn_toLp

theorem brownianSquareStep_integral_error (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (T : ℝ≥0) (n : ℕ) :
    ‖brownianIntegral hB (brownianSquareStepIntegrand hB hBm T n) - brownianSquareTarget hB T‖ ^ 2 =
      T.val ^ 2 / (2 * (2 : ℝ) ^ n) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    _ = ∫ ω, (brownianDyadicQV B T n ω - T.val) ^ 2 / 4 ∂P := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub
        (brownianIntegral hB (brownianSquareStepIntegrand hB hBm T n)) (brownianSquareTarget hB T),
        brownianSquareStep_integral_ae hB hBm T n, brownianSquareTarget_coe hB T] with ω hd hi ht
      rw [Real.inner_apply, hd]
      simp only [Pi.sub_apply]
      rw [hi, ht]
      ring
    _ = (∫ ω, (brownianDyadicQV B T n ω - T.val) ^ 2 ∂P) / 4 := integral_div _ _
    _ = _ := by rw [brownianDyadicQV_l2_error hB T n]; ring

theorem brownianSquareStep_integral_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (T : ℝ≥0) :
    Tendsto (fun n => brownianIntegral hB (brownianSquareStepIntegrand hB hBm T n))
      atTop (𝓝 (brownianSquareTarget hB T)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs : Tendsto (fun n =>
      ‖brownianIntegral hB (brownianSquareStepIntegrand hB hBm T n) - brownianSquareTarget hB T‖ ^ 2)
      atTop (𝓝 0) := by
    simp only [brownianSquareStep_integral_error]
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (T.val ^ 2 / 2)
    convert hp using 1
    · funext n
      simp only [div_eq_mul_inv, inv_pow, one_mul, mul_inv_rev]
      ring
    · simp
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hr

end TimeTraps.Probability
