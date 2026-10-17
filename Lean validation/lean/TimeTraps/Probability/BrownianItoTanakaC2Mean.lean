module

public import TimeTraps.Probability.BrownianItoTanakaC2Finite
public import TimeTraps.Probability.BrownianIntegralMean

@[expose] public section

/-! The C² finite-kink Itô–Tanaka formula has integrable actual terms and
therefore yields its expectation identity. The stochastic integral has
mean zero; no integrability of the potential is assumed separately. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

variable {ι : Type*} {F : ℝ → ℝ}

theorem brownianItoTanakaC2_finite_difference_memLp (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val)
    (s : Finset ι) (a c : ι → ℝ) (T : ℝ≥0) :
    MemLp (fun ω => finiteKinkPotential F s a c (brownianDyadicPath T ω) -
      finiteKinkPotential F s a c (brownianDyadicPath 0 ω)) 2 brownianDyadicMeasure := by
  let f := brownianFiniteKinkC2Integrand hF h₂ s a c T
  have hI : MemLp (brownianIntegralGlobalPath f T) 2 brownianDyadicMeasure :=
    (Lp.memLp (brownianStochasticIntegralUpTo T f)).ae_eq (brownianIntegralGlobalPath_integral_ae f T).symm
  have hD := brownianItoC2_drift_memLp (P := brownianDyadicMeasure) hF h₂
    brownianDyadicPath_jointly_measurable T
  have hL : MemLp (fun ω => ∑ i ∈ s, c i * brownianLocalTimeTimeField (a i) T ω) 2
      brownianDyadicMeasure :=
    memLp_finsetSum s (fun i _ => (brownianLocalTimeTimeField_memLp (a i) T).const_mul (c i))
  have he : (fun ω => finiteKinkPotential F s a c (brownianDyadicPath T ω) -
      finiteKinkPotential F s a c (brownianDyadicPath 0 ω)) =ᵐ[brownianDyadicMeasure]
      (fun ω => brownianIntegralGlobalPath f T ω +
        (1 / 2 : ℝ) * brownianItoDrift brownianDyadicPath (deriv (deriv F)) T ω +
        ∑ i ∈ s, c i * brownianLocalTimeTimeField (a i) T ω) :=
    (brownianItoTanakaC2_finite_continuous_ae hF h₂ s a c T).mono (fun _ h => h T le_rfl)
  exact ((hI.add (hD.const_mul (1 / 2 : ℝ))).add hL).ae_eq he.symm

theorem brownianItoTanakaC2_finite_mean (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val)
    (s : Finset ι) (a c : ι → ℝ) (T : ℝ≥0) :
    (∫ ω, finiteKinkPotential F s a c (brownianDyadicPath T ω) -
      finiteKinkPotential F s a c (brownianDyadicPath 0 ω) ∂brownianDyadicMeasure) =
      (1 / 2 : ℝ) * (∫ ω, brownianItoDrift brownianDyadicPath (deriv (deriv F)) T ω ∂brownianDyadicMeasure) +
        ∑ i ∈ s, c i * ∫ ω, brownianLocalTimeTimeField (a i) T ω ∂brownianDyadicMeasure := by
  let f := brownianFiniteKinkC2Integrand hF h₂ s a c T
  have hI : Integrable (brownianIntegralGlobalPath f T) brownianDyadicMeasure :=
    ((Lp.memLp (brownianStochasticIntegralUpTo T f)).ae_eq
      (brownianIntegralGlobalPath_integral_ae f T).symm).integrable (by norm_num)
  have hD := (brownianItoC2_drift_memLp (P := brownianDyadicMeasure) hF h₂
    brownianDyadicPath_jointly_measurable T).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hL (i : ι) : Integrable (fun ω => c i * brownianLocalTimeTimeField (a i) T ω) brownianDyadicMeasure :=
    ((brownianLocalTimeTimeField_memLp (a i) T).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).const_mul (c i)
  have hzero : (∫ ω, brownianIntegralGlobalPath f T ω ∂brownianDyadicMeasure) = 0 := by
    rw [integral_congr_ae (brownianIntegralGlobalPath_integral_ae f T)]
    exact brownianIntegral_mean brownianDyadicPath_isPreBrownianReal
      (brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable brownianDyadicMeasure T f)
  have he := (brownianItoTanakaC2_finite_continuous_ae hF h₂ s a c T).mono (fun _ h => h T le_rfl)
  rw [integral_congr_ae he]
  change (∫ ω, (brownianIntegralGlobalPath f T ω +
    (1 / 2 : ℝ) * brownianItoDrift brownianDyadicPath (deriv (deriv F)) T ω) +
      ∑ i ∈ s, c i * brownianLocalTimeTimeField (a i) T ω ∂brownianDyadicMeasure) = _
  have hID : Integrable (fun ω => brownianIntegralGlobalPath f T ω +
      (1 / 2 : ℝ) * brownianItoDrift brownianDyadicPath (deriv (deriv F)) T ω) brownianDyadicMeasure :=
    hI.add (hD.const_mul (1 / 2 : ℝ))
  rw [integral_add hID (integrable_finsetSum s (fun i _ => hL i)),
    integral_add hI (hD.const_mul (1 / 2 : ℝ)), hzero, zero_add, integral_const_mul,
    integral_finsetSum s (fun i _ => hL i)]
  simp only [integral_const_mul]

end TimeTraps.Probability
