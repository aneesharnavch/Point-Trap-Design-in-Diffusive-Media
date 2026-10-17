module

public import TimeTraps.Probability.ReflectedInteriorTanakaApproximation

@[expose] public section

/-! Exact affine Tanaka identities for the finite folded-kink
approximations, with their actual original-Brownian stochastic integrals
and actual labelled affine local-time sums. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedInteriorFinite_continuous_ae (L a x : ℝ) {σ : ℝ} (hσ : 0 < σ)
    (N : ℕ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t ≤ T,
      reflectedInteriorTanakaApprox L a N (affineBrownianInput x σ t ω) -
        reflectedInteriorTanakaApprox L a N x =
      brownianIntegralGlobalPath (reflectedInteriorFiniteIntegrand L a x σ N T) t ω +
        ∑ i ∈ reflectedInteriorFiniteSet N, reflectedInteriorFiniteCoeff i *
          affineBrownianTanakaCorrection x σ (reflectedInteriorFiniteSite L a i) t ω := by
  filter_upwards [brownianAffineItoTanakaC2_continuous_ae (F := fun _ => (0 : ℝ)) contDiff_const
    (M₂ := 0) (by intro y; simp) (reflectedInteriorFiniteSet N)
    (reflectedInteriorFiniteSite L a) reflectedInteriorFiniteCoeff x hσ T] with ω he
  intro t ht
  have h := he t ht
  rw [reflectedInteriorFinite_difference] at h
  have hd : deriv (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := funext (fun z => deriv_const z 0)
  have hd0 : brownianItoDrift (affineBrownianInput x σ) (deriv (deriv (fun _ : ℝ => (0 : ℝ)))) t ω = 0 := by
    rw [(congrArg deriv hd).trans hd]
    exact intervalIntegral.integral_zero
  rw [hd0, mul_zero, add_zero] at h
  exact h

theorem reflectedInteriorFinite_formula (L a x : ℝ) {σ : ℝ} (hσ : 0 < σ)
    (N : ℕ) (T : ℝ≥0) :
    (fun ω => reflectedInteriorTanakaApprox L a N (affineBrownianInput x σ T ω) -
        reflectedInteriorTanakaApprox L a N x) =ᵐ[brownianDyadicMeasure]
      (fun ω => brownianStochasticIntegralUpTo T (reflectedInteriorFiniteIntegrand L a x σ N T) ω +
        ∑ i ∈ reflectedInteriorFiniteSet N, reflectedInteriorFiniteCoeff i *
          affineBrownianTanakaCorrection x σ (reflectedInteriorFiniteSite L a i) T ω) := by
  filter_upwards [reflectedInteriorFinite_continuous_ae L a x hσ N T,
    brownianIntegralGlobalPath_integral_ae (reflectedInteriorFiniteIntegrand L a x σ N T) T] with ω hf hi
  have h := hf T le_rfl
  rw [hi] at h
  exact h

end TimeTraps.Probability
