module

public import TimeTraps.Probability.BrownianAdaptedContinuousMultiplierAmbient

@[expose] public section

/-! Strong convergence of uniformly bounded multiplication operators on
each actual product-L² input. The majorant is a constant times the square
of that input; no finite-time support or finite underlying measure is
required in this analytic lemma. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {K : ℝ × Ω → ℝ} {Kseq : ℕ → ℝ × Ω → ℝ} {M : ℝ≥0}

theorem brownianAdaptedContinuousMultiplier_tendsto
    (hK : Measurable K) (hseq : ∀ n, Measurable (Kseq n))
    (hb : ∀ p, |K p| ≤ M.val) (hbs : ∀ n p, |Kseq n p| ≤ M.val)
    (hlim : ∀ᵐ p ∂(volume : Measure ℝ).prod P,
      Tendsto (fun n => Kseq n p) atTop (𝓝 (K p)))
    (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) :
    Tendsto (fun n => brownianAdaptedContinuousMultiplierAmbient (hseq n) (hbs n) f)
      atTop (𝓝 (brownianAdaptedContinuousMultiplierAmbient hK hb f)) := by
  let A := fun n => brownianAdaptedContinuousMultiplierAmbient (hseq n) (hbs n) f
  let S := brownianAdaptedContinuousMultiplierAmbient hK hb f
  have he (n : ℕ) : ‖A n - S‖ ^ 2 =
      ∫ p, ((Kseq n p - K p) * f p) ^ 2 ∂(volume : Measure ℝ).prod P := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (A n) S,
      brownianAdaptedContinuousMultiplierAmbient_coe (hseq n) (hbs n) f,
      brownianAdaptedContinuousMultiplierAmbient_coe hK hb f] with p hd ha hs
    rw [Real.inner_apply, hd, Pi.sub_apply, ha, hs]
    ring
  have hdom : Integrable (fun p : ℝ × Ω => (2 * M.val) ^ 2 * f p ^ 2)
      (volume.prod P) := (Lp.memLp f).integrable_sq.const_mul _
  have hbound (n : ℕ) (p : ℝ × Ω) :
      ‖((Kseq n p - K p) * f p) ^ 2‖ ≤ (2 * M.val) ^ 2 * f p ^ 2 := by
    have hd : |Kseq n p - K p| ≤ 2 * M.val :=
      (abs_sub _ _).trans (by linarith [hbs n p, hb p])
    have hsq : (Kseq n p - K p) ^ 2 ≤ (2 * M.val) ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) M.property)).mpr hd
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg (f p))
  have hzero : ∀ᵐ p ∂(volume : Measure ℝ).prod P,
      Tendsto (fun n => ((Kseq n p - K p) * f p) ^ 2) atTop (𝓝 0) := by
    filter_upwards [hlim] with p hp
    simpa only [sub_self, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      ((hp.sub_const (K p)).mul_const (f p)).pow 2
  have hd := tendsto_integral_of_dominated_convergence
    (fun p : ℝ × Ω => (2 * M.val) ^ 2 * f p ^ 2)
    (fun n => ((((hseq n).sub hK).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f)).pow 2)) hdom
    (fun n => Eventually.of_forall (hbound n)) hzero
  have hs : Tendsto (fun n => ‖A n - S‖ ^ 2) atTop (𝓝 0) := by
    simpa only [he, integral_zero, Pi.pow_apply, Pi.mul_apply, Pi.sub_apply] using hd
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hr

end TimeTraps.Probability
