module

public import TimeTraps.Probability.ReflectedGaussianReversible
public import TimeTraps.Probability.ReflectedFellerSemigroup

@[expose] public section

/-! Detailed balance as equality of the actual two-time joint measures,
and as symmetry of bounded Borel test integrals. The continuous-function
specialization uses the previously constructed Feller operator itself.
All variance parameters include zero. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal ProbabilityTheory

theorem reflectedGaussianTransition_joint_swap (L : ℝ) (hL : 0 < L) (v : ℝ≥0) :
    ((reflectedUniformLaw L hL) ⊗ₘ (reflectedGaussianTransition L v)).map Prod.swap =
      (reflectedUniformLaw L hL) ⊗ₘ (reflectedGaussianTransition L v) := by
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply measurable_swap (hA.prod hB), preimage_swap_prod,
    Measure.compProd_apply_prod hB hA, Measure.compProd_apply_prod hA hB]
  exact reflectedGaussianTransition_reversible L hL v hB hA

theorem reflectedGaussianLaw_integral_balance (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) {M N : ℝ}
    (hfb : ∀ x, |f x| ≤ M) (hgb : ∀ x, |g x| ≤ N) :
    (∫ x, f x * (∫ y, g y ∂reflectedGaussianLaw L x v) ∂reflectedUniformLaw L hL) =
      ∫ x, g x * (∫ y, f y ∂reflectedGaussianLaw L x v) ∂reflectedUniformLaw L hL := by
  let J := (reflectedUniformLaw L hL) ⊗ₘ (reflectedGaussianTransition L v)
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hfb 0)
  have hN : 0 ≤ N := (abs_nonneg (g 0)).trans (hgb 0)
  have hfg : Integrable (fun p : ℝ × ℝ => f p.1 * g p.2) J := by
    apply (integrable_const (M * N)).mono' ((hf.comp measurable_fst).mul
      (hg.comp measurable_snd)).aestronglyMeasurable
    filter_upwards [] with p
    change ‖f p.1 * g p.2‖ ≤ M * N
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hfb p.1) (hgb p.2) (abs_nonneg _) hM
  have hgf : Integrable (fun p : ℝ × ℝ => g p.1 * f p.2) J := by
    apply (integrable_const (N * M)).mono' ((hg.comp measurable_fst).mul
      (hf.comp measurable_snd)).aestronglyMeasurable
    filter_upwards [] with p
    change ‖g p.1 * f p.2‖ ≤ N * M
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hgb p.1) (hfb p.2) (abs_nonneg _) hN
  have he : (∫ p : ℝ × ℝ, f p.1 * g p.2 ∂J) =
      ∫ p : ℝ × ℝ, g p.1 * f p.2 ∂J := by
    calc
      _ = ∫ p : ℝ × ℝ, f p.1 * g p.2 ∂J.map Prod.swap := by
        rw [show J.map Prod.swap = J from reflectedGaussianTransition_joint_swap L hL v]
      _ = ∫ p : ℝ × ℝ, f p.2 * g p.1 ∂J :=
        integral_map measurable_swap.aemeasurable
          ((hf.comp measurable_fst).mul (hg.comp measurable_snd)).aestronglyMeasurable
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with p
        exact mul_comm _ _
  rw [Measure.integral_compProd hfg, Measure.integral_compProd hgf] at he
  simp only [integral_const_mul, reflectedGaussianTransition_apply] at he
  exact he

theorem reflectedGaussianLaw_uniform_integral (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hgb : ∀ x, |g x| ≤ M) :
    (∫ x, (∫ y, g y ∂reflectedGaussianLaw L x v) ∂reflectedUniformLaw L hL) =
      ∫ x, g x ∂reflectedUniformLaw L hL := by
  have h := reflectedGaussianLaw_integral_balance L hL v
    (f := fun _ => (1 : ℝ)) (M := 1) measurable_const hg (fun _ => by simp) hgb
  simpa only [one_mul, integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, smul_eq_mul, mul_one] using h

theorem reflectedFellerOperator_uniform_balance (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    (f g : C(Icc (0 : ℝ) L, ℝ)) :
    (∫ x, reflectedFellerExtension L hL f x *
      reflectedFellerExtension L hL (reflectedFellerOperator L hL v g) x
      ∂reflectedUniformLaw L hL) =
    ∫ x, reflectedFellerExtension L hL g x *
      reflectedFellerExtension L hL (reflectedFellerOperator L hL v f) x
      ∂reflectedUniformLaw L hL := by
  simp_rw [reflectedFellerOperator_extension_kernel]
  exact reflectedGaussianLaw_integral_balance L hL v
    (reflectedFellerExtension L hL f).continuous.measurable
    (reflectedFellerExtension L hL g).continuous.measurable
    (reflectedFellerExtension_bound L hL f) (reflectedFellerExtension_bound L hL g)

theorem reflectedFellerOperator_uniform_integral (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    (f : C(Icc (0 : ℝ) L, ℝ)) :
    (∫ x, reflectedFellerExtension L hL (reflectedFellerOperator L hL v f) x
      ∂reflectedUniformLaw L hL) =
      ∫ x, reflectedFellerExtension L hL f x ∂reflectedUniformLaw L hL := by
  simp_rw [reflectedFellerOperator_extension_kernel]
  exact reflectedGaussianLaw_uniform_integral L hL v
    (reflectedFellerExtension L hL f).continuous.measurable (reflectedFellerExtension_bound L hL f)

end TimeTraps.Probability
