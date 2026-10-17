module

public import TimeTraps.Analysis.AffineItoC2Calculus
public import TimeTraps.Probability.BrownianFiniteKinkC2Integrand
public import TimeTraps.Probability.BrownianAffineLocalTimeTanaka

@[expose] public section

/-! The actual closed stochastic integrand for a C² finite-kink potential
along x + sigma B. Its product-space representative is sigma times the
physical midpoint slope, and its smooth drift scales by sigma squared. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

variable {ι : Type*} {F : ℝ → ℝ}

noncomputable def brownianAffineFiniteKinkC2Integrand (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ y, |deriv (deriv F) y| ≤ M₂.val)
    (s : Finset ι) (a c : ι → ℝ) (x σ : ℝ) (T : ℝ≥0) : BrownianIntegrand :=
  brownianFiniteKinkC2Integrand (affineItoBase_contDiff_two hF x σ)
    (affineItoBase_bound_two_c2 hF h₂ x σ) s (fun i => (a i - x) / σ) (fun i => σ * c i) T

theorem brownianAffineFiniteKinkC2Integrand_coe (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ y, |deriv (deriv F) y| ≤ M₂.val)
    (s : Finset ι) (a c : ι → ℝ) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    (brownianAffineFiniteKinkC2Integrand hF h₂ s a c x σ T :
      Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure)) =ᵐ[volume.prod brownianDyadicMeasure]
      (fun p => (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 *
        (σ * finiteKinkSlope F s a c (affineBrownianInput x σ p.1.toNNReal p.2))) := by
  filter_upwards [brownianFiniteKinkC2Integrand_coe (affineItoBase_contDiff_two hF x σ)
    (affineItoBase_bound_two_c2 hF h₂ x σ) s (fun i => (a i - x) / σ) (fun i => σ * c i) T]
    with p hp
  rw [finiteKinkSlope_affine (hF.differentiable (by norm_num)) s a c x hσ] at hp
  exact hp

theorem brownianAffineFiniteKinkC2Integrand_integral (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ y, |deriv (deriv F) y| ≤ M₂.val)
    (s : Finset ι) (a c : ι → ℝ) (x σ : ℝ) (T : ℝ≥0) :
    brownianStochasticIntegral (brownianAffineFiniteKinkC2Integrand hF h₂ s a c x σ T) =
      brownianStochasticIntegral
        (brownianDyadicLipschitzIntegrand (brownianItoC2_firstDerivative_lipschitz
          (affineItoBase_contDiff_two hF x σ) (affineItoBase_bound_two_c2 hF h₂ x σ)) T) +
      ∑ i ∈ s, (σ * c i) • brownianDyadicSignIntegral ((a i - x) / σ) T :=
  brownianFiniteKinkC2Integrand_integral (affineItoBase_contDiff_two hF x σ)
    (affineItoBase_bound_two_c2 hF h₂ x σ) s (fun i => (a i - x) / σ) (fun i => σ * c i) T

theorem brownianAffineItoC2Drift (hF : ContDiff ℝ 2 F) (x σ : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    brownianItoDrift brownianDyadicPath (deriv (deriv (affineItoBase F x σ))) t ω =
      σ ^ 2 * brownianItoDrift (affineBrownianInput x σ) (deriv (deriv F)) t ω := by
  rw [affineItoBase_deriv_two_c2 hF x σ]
  change (∫ r in (0 : ℝ)..t.val, σ ^ 2 * deriv (deriv F) (x + σ * brownianDyadicPath r.toNNReal ω)) =
    σ ^ 2 * ∫ r in (0 : ℝ)..t.val, deriv (deriv F) (x + σ * brownianDyadicPath r.toNNReal ω)
  exact intervalIntegral.integral_const_mul _ _

end TimeTraps.Probability
