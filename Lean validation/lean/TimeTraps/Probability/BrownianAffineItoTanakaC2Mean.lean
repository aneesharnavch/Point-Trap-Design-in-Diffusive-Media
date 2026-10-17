module

public import TimeTraps.Probability.BrownianAffineItoTanakaC2
public import TimeTraps.Probability.BrownianItoTanakaC2Mean

@[expose] public section

/-! Square integrability and expectation identities for the C² affine
finite-kink formula. All drift and local-time terms are actual random
variables, and the canonical stochastic integral has mean zero. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

variable {ι : Type*} {F : ℝ → ℝ}

theorem brownianAffineItoC2_drift_memLp (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ y, |deriv (deriv F) y| ≤ M₂.val)
    (x σ : ℝ) (T : ℝ≥0) :
    MemLp (brownianItoDrift (affineBrownianInput x σ) (deriv (deriv F)) T) 2
      brownianDyadicMeasure := by
  apply brownianItoC2_drift_memLp (P := brownianDyadicMeasure) hF h₂
  change Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => x + σ * brownianDyadicPath p.1 p.2)
  exact measurable_const.add (measurable_const.mul brownianDyadicPath_jointly_measurable)

theorem brownianAffineItoTanakaC2_difference_memLp (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ y, |deriv (deriv F) y| ≤ M₂.val)
    (s : Finset ι) (a c : ι → ℝ) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    MemLp (fun ω => finiteKinkPotential F s a c (affineBrownianInput x σ T ω) -
      finiteKinkPotential F s a c x) 2 brownianDyadicMeasure := by
  have h := brownianItoTanakaC2_finite_difference_memLp (affineItoBase_contDiff_two hF x σ)
    (affineItoBase_bound_two_c2 hF h₂ x σ)
    s (fun i => (a i - x) / σ) (fun i => σ * c i) T
  apply h.ae_eq
  filter_upwards [affineBrownianInput_start x σ] with ω hzero
  have hp (r : ℝ≥0) : finiteKinkPotential F s a c (affineBrownianInput x σ r ω) =
      finiteKinkPotential (affineItoBase F x σ) s
        (fun i => (a i - x) / σ) (fun i => σ * c i) (brownianDyadicPath r ω) :=
    finiteKinkPotential_affine F s a c x hσ (brownianDyadicPath r ω)
  rw [← hp T, ← hp 0, hzero]

theorem brownianAffineItoTanakaC2_mean (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ y, |deriv (deriv F) y| ≤ M₂.val)
    (s : Finset ι) (a c : ι → ℝ) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    (∫ ω, finiteKinkPotential F s a c (affineBrownianInput x σ T ω) -
      finiteKinkPotential F s a c x ∂brownianDyadicMeasure) =
      (σ ^ 2 / 2) * (∫ ω, brownianItoDrift (affineBrownianInput x σ) (deriv (deriv F)) T ω
        ∂brownianDyadicMeasure) +
        ∑ i ∈ s, c i * ∫ ω, affineBrownianTanakaCorrection x σ (a i) T ω ∂brownianDyadicMeasure := by
  let f := brownianAffineFiniteKinkC2Integrand hF h₂ s a c x σ T
  have hI : Integrable (brownianIntegralGlobalPath f T) brownianDyadicMeasure :=
    ((Lp.memLp (brownianStochasticIntegralUpTo T f)).ae_eq
      (brownianIntegralGlobalPath_integral_ae f T).symm).integrable (by norm_num)
  have hD := (brownianAffineItoC2_drift_memLp hF h₂ x σ T).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hL (i : ι) : Integrable (fun ω => c i * affineBrownianTanakaCorrection x σ (a i) T ω)
      brownianDyadicMeasure :=
    (((brownianLocalTimeTimeField_memLp ((a i - x) / σ) T).const_mul σ).integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)).const_mul (c i)
  have hzero : (∫ ω, brownianIntegralGlobalPath f T ω ∂brownianDyadicMeasure) = 0 := by
    rw [integral_congr_ae (brownianIntegralGlobalPath_integral_ae f T)]
    exact brownianIntegral_mean brownianDyadicPath_isPreBrownianReal
      (brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable brownianDyadicMeasure T f)
  have he := (brownianAffineItoTanakaC2_continuous_ae hF h₂ s a c x hσ T).mono (fun _ h => h T le_rfl)
  rw [integral_congr_ae he]
  change (∫ ω, (brownianIntegralGlobalPath f T ω +
    (σ ^ 2 / 2) * brownianItoDrift (affineBrownianInput x σ) (deriv (deriv F)) T ω) +
      ∑ i ∈ s, c i * affineBrownianTanakaCorrection x σ (a i) T ω ∂brownianDyadicMeasure) = _
  have hID : Integrable (fun ω => brownianIntegralGlobalPath f T ω +
      (σ ^ 2 / 2) * brownianItoDrift (affineBrownianInput x σ) (deriv (deriv F)) T ω)
      brownianDyadicMeasure := hI.add (hD.const_mul (σ ^ 2 / 2))
  rw [integral_add hID (integrable_finsetSum s (fun i _ => hL i)),
    integral_add hI (hD.const_mul (σ ^ 2 / 2)), hzero, zero_add, integral_const_mul,
    integral_finsetSum s (fun i _ => hL i)]
  simp only [integral_const_mul]

theorem brownianDiffusionItoTanakaC2_mean (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ y, |deriv (deriv F) y| ≤ M₂.val)
    (s : Finset ι) (a c : ι → ℝ) (x : ℝ) {D : ℝ} (hD : 0 < D) (T : ℝ≥0) :
    (∫ ω, finiteKinkPotential F s a c (affineBrownianInput x (Real.sqrt (2 * D)) T ω) -
      finiteKinkPotential F s a c x ∂brownianDyadicMeasure) =
      D * (∫ ω, brownianItoDrift (affineBrownianInput x (Real.sqrt (2 * D))) (deriv (deriv F)) T ω
        ∂brownianDyadicMeasure) +
        (2 * D) * ∑ i ∈ s, c i * ∫ ω,
          affineBrownianOccupationDensity x (Real.sqrt (2 * D)) (a i) T ω ∂brownianDyadicMeasure := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  rw [brownianAffineItoTanakaC2_mean hF h₂ s a c x hσ T,
    Real.sq_sqrt (by positivity)]
  have hhalf : (2 * D) / 2 = D := by ring
  rw [hhalf, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun ω => affineBrownianTanakaCorrection x (Real.sqrt (2 * D)) (a i) T ω) =
      (fun ω => (2 * D) * affineBrownianOccupationDensity x (Real.sqrt (2 * D)) (a i) T ω) :=
    funext (fun ω => affineBrownian_diffusion_normalization x hD (a i) T ω)
  rw [he, integral_const_mul]
  ring

end TimeTraps.Probability
