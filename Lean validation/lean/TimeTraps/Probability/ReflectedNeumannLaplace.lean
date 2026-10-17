module

public import TimeTraps.Probability.ReflectedNeumannSobolev
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-! The genuine vector-valued Laplace integral of the actual reflected
L2 transition family. Exponential decay and contraction establish
Bochner integrability and the bound 1/alpha for every alpha>0. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory Set TimeTraps.Analysis

def reflectedNeumannLaplace (L : ℝ) (hL : 0 < L) (D α : ℝ)
    (f : ReflectedUniformL2 L hL) : ReflectedUniformL2 L hL :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-α * t) • reflectedGaussianPhysicalL2Curve L hL D f t

theorem reflectedGaussianPhysicalL2Curve_continuous (L : ℝ) (hL : 0 < L) (D : ℝ)
    (f : ReflectedUniformL2 L hL) : Continuous (reflectedGaussianPhysicalL2Curve L hL D f) := by
  have ht : Continuous (fun t : ℝ => (2 * D * t).toNNReal) := by fun_prop
  exact (reflectedGaussianL2Operator_continuous L hL f).comp ht

theorem reflectedLaplace_exponential_integral {α : ℝ} (hα : 0 < α) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-α * t)) = α⁻¹ := by
  simpa only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div] using
    integral_exp_mul_Ioi (a := -α) (neg_neg_iff_pos.mpr hα) 0

theorem reflectedNeumannLaplace_integrable (L : ℝ) (hL : 0 < L) (D : ℝ)
    {α : ℝ} (hα : 0 < α) (f : ReflectedUniformL2 L hL) :
    IntegrableOn (fun t : ℝ => Real.exp (-α * t) • reflectedGaussianPhysicalL2Curve L hL D f t)
      (Ioi 0) := by
  have hc : Continuous (fun t : ℝ =>
      Real.exp (-α * t) • reflectedGaussianPhysicalL2Curve L hL D f t) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      (reflectedGaussianPhysicalL2Curve_continuous L hL D f)
  apply ((exp_neg_integrableOn_Ioi 0 hα).mul_const ‖f‖).mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left
    (reflectedGaussianL2Operator_contraction L hL (2 * D * t).toNNReal f) (Real.exp_pos _).le

theorem reflectedNeumannLaplace_norm_le (L : ℝ) (hL : 0 < L) (D : ℝ)
    {α : ℝ} (hα : 0 < α) (f : ReflectedUniformL2 L hL) :
    ‖reflectedNeumannLaplace L hL D α f‖ ≤ ‖f‖ / α := by
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ),
        ‖Real.exp (-α * t) • reflectedGaussianPhysicalL2Curve L hL D f t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-α * t) * ‖f‖ := by
      apply integral_mono_ae (reflectedNeumannLaplace_integrable L hL D hα f).norm
        ((exp_neg_integrableOn_Ioi 0 hα).mul_const ‖f‖)
      apply Filter.Eventually.of_forall
      intro t
      dsimp only
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left
        (reflectedGaussianL2Operator_contraction L hL (2 * D * t).toNNReal f) (Real.exp_pos _).le
    _ = _ := by
      rw [integral_mul_const, reflectedLaplace_exponential_integral hα, div_eq_mul_inv, mul_comm]

end TimeTraps.Probability

end
