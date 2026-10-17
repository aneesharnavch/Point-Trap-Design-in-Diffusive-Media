module

public import TimeTraps.Probability.BrownianAffineFiniteKinkC2Integrand
public import TimeTraps.Probability.BrownianItoTanakaC2Finite

@[expose] public section

/-! C² Itô–Tanaka along the actual affine Brownian input, with its actual
closed stochastic integral and occupation local times. The physical
diffusion normalization is D for curvature and 2D for each kink coefficient. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

variable {ι : Type*} {F : ℝ → ℝ}

theorem brownianAffineItoTanakaC2_continuous_ae (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ y, |deriv (deriv F) y| ≤ M₂.val)
    (s : Finset ι) (a c : ι → ℝ) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t ≤ T,
      finiteKinkPotential F s a c (affineBrownianInput x σ t ω) - finiteKinkPotential F s a c x =
      brownianIntegralGlobalPath (brownianAffineFiniteKinkC2Integrand hF h₂ s a c x σ T) t ω +
        (σ ^ 2 / 2) * brownianItoDrift (affineBrownianInput x σ) (deriv (deriv F)) t ω +
        ∑ i ∈ s, c i * affineBrownianTanakaCorrection x σ (a i) t ω := by
  filter_upwards [brownianItoTanakaC2_finite_continuous_ae (affineItoBase_contDiff_two hF x σ)
    (affineItoBase_bound_two_c2 hF h₂ x σ)
    s (fun i => (a i - x) / σ) (fun i => σ * c i) T,
    affineBrownianInput_start x σ] with ω he hzero
  intro t ht
  have hp (r : ℝ≥0) : finiteKinkPotential F s a c (affineBrownianInput x σ r ω) =
      finiteKinkPotential (affineItoBase F x σ) s
        (fun i => (a i - x) / σ) (fun i => σ * c i) (brownianDyadicPath r ω) :=
    finiteKinkPotential_affine F s a c x hσ (brownianDyadicPath r ω)
  have hsum : (∑ i ∈ s, (σ * c i) * brownianLocalTimeTimeField ((a i - x) / σ) t ω) =
      ∑ i ∈ s, c i * affineBrownianTanakaCorrection x σ (a i) t ω := by
    apply Finset.sum_congr rfl
    intro i _
    unfold affineBrownianTanakaCorrection
    ring
  have h := he t ht
  rw [← hp t, ← hp 0, hzero, brownianAffineItoC2Drift hF x σ t ω, hsum] at h
  change _ = brownianIntegralGlobalPath (brownianAffineFiniteKinkC2Integrand hF h₂ s a c x σ T) t ω +
    (1 / 2 : ℝ) * (σ ^ 2 * brownianItoDrift (affineBrownianInput x σ) (deriv (deriv F)) t ω) +
      ∑ i ∈ s, c i * affineBrownianTanakaCorrection x σ (a i) t ω at h
  rw [h]
  ring

theorem brownianAffineItoTanakaC2_occupation_ae (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ y, |deriv (deriv F) y| ≤ M₂.val)
    (s : Finset ι) (a c : ι → ℝ) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t ≤ T,
      finiteKinkPotential F s a c (affineBrownianInput x σ t ω) - finiteKinkPotential F s a c x =
      brownianIntegralGlobalPath (brownianAffineFiniteKinkC2Integrand hF h₂ s a c x σ T) t ω +
        (σ ^ 2 / 2) * brownianItoDrift (affineBrownianInput x σ) (deriv (deriv F)) t ω +
        σ ^ 2 * ∑ i ∈ s, c i * affineBrownianOccupationDensity x σ (a i) t ω := by
  filter_upwards [brownianAffineItoTanakaC2_continuous_ae hF h₂ s a c x hσ T] with ω he
  intro t ht
  rw [he t ht, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [affineBrownianTanakaCorrection_eq_density x hσ (a i) t ω]
  ring

theorem brownianDiffusionItoTanakaC2_continuous_ae (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ y, |deriv (deriv F) y| ≤ M₂.val)
    (s : Finset ι) (a c : ι → ℝ) (x : ℝ) {D : ℝ} (hD : 0 < D) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t ≤ T,
      finiteKinkPotential F s a c (affineBrownianInput x (Real.sqrt (2 * D)) t ω) -
        finiteKinkPotential F s a c x =
      brownianIntegralGlobalPath
        (brownianAffineFiniteKinkC2Integrand hF h₂ s a c x (Real.sqrt (2 * D)) T) t ω +
        D * brownianItoDrift (affineBrownianInput x (Real.sqrt (2 * D))) (deriv (deriv F)) t ω +
        (2 * D) * ∑ i ∈ s, c i * affineBrownianOccupationDensity x (Real.sqrt (2 * D)) (a i) t ω := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  filter_upwards [brownianAffineItoTanakaC2_occupation_ae hF h₂ s a c x hσ T] with ω he
  intro t ht
  have h := he t ht
  rw [Real.sq_sqrt (by positivity), mul_div_cancel_left₀ D (by norm_num : (2 : ℝ) ≠ 0)] at h
  exact h

end TimeTraps.Probability
