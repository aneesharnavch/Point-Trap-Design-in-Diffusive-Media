module

public import TimeTraps.Probability.BrownianItoTaylorMoments

@[expose] public section

/-! The actual Brownian Taylor increment has an integrable absolute
remainder bounded by its exact Gaussian moment estimates. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory TimeTraps.Analysis
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {F : ℝ → ℝ}

noncomputable def brownianItoTaylorIncrement (B : ℝ≥0 → Ω → ℝ) (F : ℝ → ℝ)
    (s t : ℝ≥0) (ω : Ω) : ℝ := itoTaylorRemainder F (B s ω) (B t ω)

theorem brownianItoTaylorIncrement_measurable (hBm : ∀ t, Measurable (B t))
    (hF : ContDiff ℝ 3 F) (s t : ℝ≥0) : Measurable (brownianItoTaylorIncrement B F s t) := by
  have h₁ : Continuous (deriv F) := hF.continuous_deriv (by norm_num)
  have h₂ : Continuous (deriv (deriv F)) :=
    (hF.deriv' (n := 2)).continuous_deriv (by norm_num)
  unfold brownianItoTaylorIncrement itoTaylorRemainder
  exact (((hF.continuous.measurable.comp (hBm t)).sub
    (hF.continuous.measurable.comp (hBm s))).sub
    ((h₁.measurable.comp (hBm s)).mul ((hBm t).sub (hBm s)))).sub
      (((h₂.measurable.comp (hBm s)).mul (((hBm t).sub (hBm s)).pow_const 2)).div_const 2)

theorem brownianItoTaylorIncrement_abs_bound (hF : ContDiff ℝ 3 F)
    {M : ℝ} (hb : ∀ z, |iteratedDeriv 3 F z| ≤ M) (s t : ℝ≥0) (ω : Ω) :
    |brownianItoTaylorIncrement B F s t ω| ≤ (M / 6) * |B t ω - B s ω| ^ 3 := by
  exact (itoTaylorRemainder_abs_le hF hb (B s ω) (B t ω)).trans_eq (by ring)

theorem brownianItoTaylorIncrement_integrable (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hF : ContDiff ℝ 3 F)
    {M : ℝ} (hb : ∀ z, |iteratedDeriv 3 F z| ≤ M) (s t : ℝ≥0) :
    Integrable (brownianItoTaylorIncrement B F s t) P := by
  apply ((brownian_increment_abs_cube_integrable hB s t).const_mul (M / 6)).mono'
    (brownianItoTaylorIncrement_measurable hBm hF s t).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs]
    exact brownianItoTaylorIncrement_abs_bound hF hb s t ω)

theorem brownianItoTaylorIncrement_mean_abs_le (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hF : ContDiff ℝ 3 F)
    {M : ℝ} (hb : ∀ z, |iteratedDeriv 3 F z| ≤ M) (s t : ℝ≥0) :
    (∫ ω, |brownianItoTaylorIncrement B F s t ω| ∂P) ≤
      (M / 6) * (Real.sqrt 3 * |t.val - s.val| * Real.sqrt |t.val - s.val|) := by
  have hM : 0 ≤ M := (abs_nonneg (iteratedDeriv 3 F 0)).trans (hb 0)
  calc
    _ ≤ ∫ ω, (M / 6) * |B t ω - B s ω| ^ 3 ∂P :=
      integral_mono_ae (brownianItoTaylorIncrement_integrable hB hBm hF hb s t).abs
        ((brownian_increment_abs_cube_integrable hB s t).const_mul (M / 6))
        (Filter.Eventually.of_forall (brownianItoTaylorIncrement_abs_bound hF hb s t))
    _ = (M / 6) * ∫ ω, |B t ω - B s ω| ^ 3 ∂P := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (brownian_increment_abs_cube_le hB s t)
      (div_nonneg hM (by norm_num))

end TimeTraps.Probability
