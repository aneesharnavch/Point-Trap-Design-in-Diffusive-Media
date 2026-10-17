module

public import TimeTraps.Probability.BrownianFiniteKinkC2Integrand
public import TimeTraps.Probability.BrownianItoC2Continuous
public import TimeTraps.Probability.BrownianIntegralContinuousLinear
public import TimeTraps.Probability.BrownianLocalTimeGlobalSign
public import TimeTraps.Probability.BrownianLocalTimeTimeRegularity

@[expose] public section

/-! Itô–Tanaka for a C² base with bounded second derivative plus finitely many signed absolute-value
kinks, with the actual closed stochastic integral and actual occupation
local times. The equation holds simultaneously at all times in a compact
horizon, retaining repeated sites and arbitrary signed coefficients. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

variable {ι : Type*} {F : ℝ → ℝ}

theorem brownianItoTanakaC2_finite_continuous_ae (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val)
    (s : Finset ι) (a c : ι → ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t ≤ T,
      finiteKinkPotential F s a c (brownianDyadicPath t ω) -
        finiteKinkPotential F s a c (brownianDyadicPath 0 ω) =
      brownianIntegralGlobalPath (brownianFiniteKinkC2Integrand hF h₂ s a c T) t ω +
        (1 / 2 : ℝ) * brownianItoDrift brownianDyadicPath (deriv (deriv F)) t ω +
        ∑ i ∈ s, c i * brownianLocalTimeTimeField (a i) t ω := by
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ i ∈ s, ∀ t ≤ T,
      |brownianDyadicPath t ω - a i| = |brownianDyadicPath 0 ω - a i| +
        brownianSignIntegralPath (a i) T t ω + brownianLocalTimeTimeField (a i) t ω := by
    apply (eventually_all_finset s).mpr
    intro i _
    filter_upwards [brownianLocalTimeGlobalPath_decomposition_ae (a i),
      brownianLocalTimeTimeField_globalPath_ae (a i),
      brownianSignIntegralGlobalPath_compact_ae (a i) T] with ω he hl hs
    intro t ht
    have h := he t
    rw [← hl t, hs t ht] at h
    exact h
  filter_upwards [brownianItoC2_formula_continuous_ae hF h₂ T,
    brownianIntegralGlobalPath_affine_sum_ae
      (brownianDyadicLipschitzIntegrand (brownianItoC2_firstDerivative_lipschitz hF h₂) T)
      s c (fun i => brownianDyadicSignIntegrand (a i) T), hall] with ω hFω hlin hk
  intro t ht
  have hsum : (∑ i ∈ s, c i * |brownianDyadicPath t ω - a i|) -
      (∑ i ∈ s, c i * |brownianDyadicPath 0 ω - a i|) =
      (∑ i ∈ s, c i * brownianSignIntegralPath (a i) T t ω) +
        ∑ i ∈ s, c i * brownianLocalTimeTimeField (a i) t ω := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hk i hi t ht]
    ring
  have hbase := hFω t ht
  rw [brownianFiniteKinkC2Integrand, hlin t]
  change finiteKinkPotential F s a c (brownianDyadicPath t ω) -
    finiteKinkPotential F s a c (brownianDyadicPath 0 ω) =
    (brownianItoC2IntegralPath hF h₂ T t ω + ∑ i ∈ s, c i * brownianSignIntegralPath (a i) T t ω) +
      (1 / 2 : ℝ) * brownianItoDrift brownianDyadicPath (deriv (deriv F)) t ω +
      ∑ i ∈ s, c i * brownianLocalTimeTimeField (a i) t ω
  unfold finiteKinkPotential
  linarith

end TimeTraps.Probability
