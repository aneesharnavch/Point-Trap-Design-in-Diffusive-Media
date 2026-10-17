module

public import TimeTraps.Probability.ReflectedFoldLaw
public import Mathlib.MeasureTheory.Group.IntegralConvolution

@[expose] public section

/-! Measurability and the exact Chapman--Kolmogorov identity for the
folded Gaussian transition law. Its composition is proved by removing
the intermediate fold, adding two independent centered Gaussians, and
Fubini. Both variance parameters may be zero. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

theorem reflectedGaussianLaw_integral_centered (L x : ℝ) (v : ℝ≥0)
    {g : ℝ → ℝ} (hg : Measurable g) :
    (∫ y, g y ∂reflectedGaussianLaw L x v) =
      ∫ z, g (reflectedFold L (x + z)) ∂gaussianReal 0 v := by
  rw [reflectedGaussianLaw_centered]
  exact integral_map
    ((reflectedFold_measurable L).comp (show Measurable (fun z : ℝ => x + z) from
      measurable_const.add measurable_id)).aemeasurable hg.aestronglyMeasurable

theorem reflectedGaussianLaw_integral_measurable (L : ℝ) (v : ℝ≥0)
    {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable (fun x => ∫ y, g y ∂reflectedGaussianLaw L x v) := by
  simp_rw [reflectedGaussianLaw_integral_centered L _ v hg]
  have hf : Measurable (fun p : ℝ × ℝ => g (reflectedFold L (p.1 + p.2))) :=
    hg.comp ((reflectedFold_measurable L).comp (measurable_fst.add measurable_snd))
  exact hf.stronglyMeasurable.integral_prod_right'.measurable

theorem reflectedGaussianLaw_integral_bound (L x : ℝ) (v : ℝ≥0)
    {g : ℝ → ℝ} {M : ℝ} (hb : ∀ y, |g y| ≤ M) :
    |∫ y, g y ∂reflectedGaussianLaw L x v| ≤ M := by
  have h := norm_integral_le_of_norm_le_const
    (μ := reflectedGaussianLaw L x v) (f := g) (C := M)
    (Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hb y)
  simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using h

theorem reflectedGaussianLaw_integral_zero (L : ℝ) (hL : 0 < L) {x : ℝ}
    (hx : x ∈ Icc 0 L) {g : ℝ → ℝ} (hg : Measurable g) :
    (∫ y, g y ∂reflectedGaussianLaw L x 0) = g x := by
  rw [reflectedGaussianLaw_zero, integral_dirac' g (reflectedFold L x) hg.stronglyMeasurable,
    reflectedFold_eq_self L hL x hx]

theorem reflectedGaussianLaw_integral_comp (L : ℝ) (hL : 0 < L) (x : ℝ)
    (v₁ v₂ : ℝ≥0) {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ}
    (hb : ∀ y, |g y| ≤ M) :
    (∫ y, (∫ z, g z ∂reflectedGaussianLaw L y v₂) ∂reflectedGaussianLaw L x v₁) =
      ∫ z, g z ∂reflectedGaussianLaw L x (v₁ + v₂) := by
  have hgi : Integrable (fun z => g (reflectedFold L (x + z)))
      ((gaussianReal 0 v₁) ∗ (gaussianReal 0 v₂)) := by
    rw [gaussianReal_conv_gaussianReal, zero_add]
    exact (integrable_const M).mono'
      (hg.comp ((reflectedFold_measurable L).comp
        (show Measurable (fun z : ℝ => x + z) from measurable_const.add measurable_id))).aestronglyMeasurable
      (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hb (reflectedFold L (x + z)))
  calc
    _ = ∫ a, ∫ b, g (reflectedFold L (x + (a + b))) ∂gaussianReal 0 v₂ ∂gaussianReal 0 v₁ := by
      rw [reflectedGaussianLaw_integral_centered L x v₁
        (reflectedGaussianLaw_integral_measurable L v₂ hg)]
      apply integral_congr_ae
      filter_upwards [] with a
      rw [← reflectedGaussianLaw_fold_start L hL (x + a) v₂,
        reflectedGaussianLaw_integral_centered L (x + a) v₂ hg]
      simp only [add_assoc]
    _ = ∫ z, g (reflectedFold L (x + z)) ∂((gaussianReal 0 v₁) ∗ (gaussianReal 0 v₂)) :=
      (integral_conv hgi).symm
    _ = ∫ z, g (reflectedFold L (x + z)) ∂gaussianReal 0 (v₁ + v₂) := by
      rw [gaussianReal_conv_gaussianReal, zero_add]
    _ = _ := (reflectedGaussianLaw_integral_centered L x (v₁ + v₂) hg).symm

end TimeTraps.Probability
