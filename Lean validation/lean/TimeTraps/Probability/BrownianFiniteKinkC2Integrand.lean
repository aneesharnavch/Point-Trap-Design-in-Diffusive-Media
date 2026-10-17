module

public import TimeTraps.Analysis.FiniteKinkCalculus
public import TimeTraps.Probability.BrownianItoC2Integrand
public import TimeTraps.Probability.BrownianSignIntegralContinuous

@[expose] public section

/-! The midpoint slope of a C² base plus finite-kink potential belongs to the actual
closed Brownian integrand space. Its integral is the canonical linear
combination of the smooth derivative and actual sign integrals. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

variable {ι : Type*} {F : ℝ → ℝ}

noncomputable def brownianFiniteKinkC2Integrand (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val)
    (s : Finset ι) (a c : ι → ℝ) (T : ℝ≥0) : BrownianIntegrand :=
  brownianDyadicLipschitzIntegrand (brownianItoC2_firstDerivative_lipschitz hF h₂) T +
    ∑ i ∈ s, c i • brownianDyadicSignIntegrand (a i) T

theorem brownianFiniteKinkC2Integrand_coe (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val)
    (s : Finset ι) (a c : ι → ℝ) (T : ℝ≥0) :
    (brownianFiniteKinkC2Integrand hF h₂ s a c T :
      Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure)) =ᵐ[volume.prod brownianDyadicMeasure]
      (fun p => (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 *
        finiteKinkSlope F s a c (brownianDyadicPath p.1.toNNReal p.2)) := by
  let f₀ : Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure) :=
    brownianDyadicLipschitzIntegrand (brownianItoC2_firstDerivative_lipschitz hF h₂) T
  let V (i : ι) : Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure) :=
    c i • (brownianDyadicSignIntegrand (a i) T : Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure))
  have hrep : (brownianFiniteKinkC2Integrand hF h₂ s a c T :
      Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure)) = f₀ + ∑ i ∈ s, V i := by
    simp only [brownianFiniteKinkC2Integrand, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul]
    rfl
  rw [hrep]
  have hall : ∀ᵐ p ∂(volume : Measure ℝ).prod brownianDyadicMeasure, ∀ i ∈ s,
      V i p = c i * ((Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 *
        Real.sign (brownianDyadicPath p.1.toNNReal p.2 - a i)) := by
    apply (eventually_all_finset s).mpr
    intro i _
    filter_upwards [Lp.coeFn_smul (c i)
      (brownianDyadicSignIntegrand (a i) T : Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure)),
      brownianDyadicSignIntegrand_coe (a i) T] with p hc hi
    dsimp only [V]
    rw [hc, Pi.smul_apply, smul_eq_mul, hi]
  filter_upwards [Lp.coeFn_add f₀ (∑ i ∈ s, V i), Lp.coeFn_fun_finsetSum s V,
    brownianDyadicLipschitzIntegrand_coe (brownianItoC2_firstDerivative_lipschitz hF h₂) T,
    hall] with p ha hs h₀ hv
  rw [ha, Pi.add_apply, hs]
  change f₀ p + ∑ i ∈ s, V i p = _
  rw [show f₀ p = (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 *
    deriv F (brownianDyadicPath p.1.toNNReal p.2) from h₀]
  simp only [finiteKinkSlope, mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hv i hi]
  ring

theorem brownianFiniteKinkC2Integrand_integral (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val)
    (s : Finset ι) (a c : ι → ℝ) (T : ℝ≥0) :
    brownianStochasticIntegral (brownianFiniteKinkC2Integrand hF h₂ s a c T) =
      brownianStochasticIntegral
        (brownianDyadicLipschitzIntegrand (brownianItoC2_firstDerivative_lipschitz hF h₂) T) +
      ∑ i ∈ s, c i • brownianDyadicSignIntegral (a i) T := by
  simp only [brownianFiniteKinkC2Integrand, map_add, map_sum, map_smul]
  rfl

end TimeTraps.Probability
