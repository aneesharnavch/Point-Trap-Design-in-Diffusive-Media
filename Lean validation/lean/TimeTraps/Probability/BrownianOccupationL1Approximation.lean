module

public import TimeTraps.Probability.BrownianLocalTimeLevelIntegral
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

@[expose] public section

/-! Compactly supported continuous scalar approximations and continuity
of the actual spatial compensation integral in the scalar L¹ norm.
The initial scalar weight may be unbounded and only almost everywhere
measurable. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem real_integrable_compact_approximation {g : ℝ → ℝ} (hg : Integrable g volume) :
    ∃ u : ℕ → ℝ → ℝ, (∀ n, Continuous (u n)) ∧ (∀ n, HasCompactSupport (u n)) ∧
      (∀ n, Integrable (u n) volume) ∧
      Tendsto (fun n => ∫ x, |u n x - g x|) atTop (𝓝 0) := by
  have he (n : ℕ) := hg.exists_hasCompactSupport_integral_sub_le
    (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ n)
  choose u hc hb hu hi using he
  refine ⟨u, hu, hc, hi, ?_⟩
  apply squeeze_zero (fun n => integral_nonneg (fun _ => abs_nonneg _))
    (fun n => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1))
  calc
    _ = ∫ x, ‖g x - u n x‖ := by simp only [Real.norm_eq_abs, abs_sub_comm]
    _ ≤ _ := hb n

theorem brownianTanakaLevelIntegral_difference_bound (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g k : ℝ → ℝ} (hg : Integrable g volume) (hk : Integrable k volume) :
    ‖brownianTanakaLevelIntegral hB hBm hjoint T g -
      brownianTanakaLevelIntegral hB hBm hjoint T k‖ ≤
        2 * Real.sqrt T.val * ∫ x, |g x - k x| := by
  have he : brownianTanakaLevelIntegral hB hBm hjoint T g -
      brownianTanakaLevelIntegral hB hBm hjoint T k =
        brownianTanakaLevelIntegral hB hBm hjoint T (g - k) := by
    simp only [brownianTanakaLevelIntegral, Pi.sub_apply, sub_smul]
    exact (integral_sub (brownianTanakaCompensation_weight_integrable hB hBm hjoint T hg)
      (brownianTanakaCompensation_weight_integrable hB hBm hjoint T hk)).symm
  rw [he]
  exact brownianTanakaLevelIntegral_norm_le hB hBm hjoint T (hg.sub hk)

theorem brownianTanakaLevelIntegral_tendsto_of_L1 (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {u : ℕ → ℝ → ℝ} {g : ℝ → ℝ} (hu : ∀ n, Integrable (u n) volume)
    (hg : Integrable g volume)
    (hlim : Tendsto (fun n => ∫ x, |u n x - g x|) atTop (𝓝 0)) :
    Tendsto (fun n => brownianTanakaLevelIntegral hB hBm hjoint T (u n)) atTop
      (𝓝 (brownianTanakaLevelIntegral hB hBm hjoint T g)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => brownianTanakaLevelIntegral_difference_bound hB hBm hjoint T (hu n) hg)
    (by simpa only [mul_zero] using hlim.const_mul (2 * Real.sqrt T.val))

end TimeTraps.Probability
