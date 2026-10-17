module

public import TimeTraps.Probability.BrownianStepIntegralIsometry

@[expose] public section

/-! The finite step stochastic integral for the constructed Brownian process
on its actual probability space. Coefficients are arbitrary L² functions
measurable in the raw natural filtration at the corresponding left endpoint.
No independent Brownian-existence premise is used. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem brownianDyadicPath_stepIntegral_memLp {N : ℕ} (τ : Fin (N + 1) → ℝ≥0)
    (hτ : Monotone τ) (ξ : Fin N → (ℕ → ℝ) → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianFiltration (τ i.castSucc)] (ξ i))
    (hξ2 : ∀ i, MemLp (ξ i) 2 brownianDyadicMeasure) :
    MemLp (brownianStepIntegral brownianDyadicPath τ ξ) 2 brownianDyadicMeasure :=
  brownianStepIntegral_memLp brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable τ hτ ξ hξ hξ2

theorem brownianDyadicPath_stepIntegral_integrable {N : ℕ} (τ : Fin (N + 1) → ℝ≥0)
    (hτ : Monotone τ) (ξ : Fin N → (ℕ → ℝ) → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianFiltration (τ i.castSucc)] (ξ i))
    (hξ2 : ∀ i, MemLp (ξ i) 2 brownianDyadicMeasure) :
    Integrable (brownianStepIntegral brownianDyadicPath τ ξ) brownianDyadicMeasure :=
  brownianStepIntegral_integrable brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable τ hτ ξ hξ hξ2

theorem brownianDyadicPath_stepIntegral_mean {N : ℕ} (τ : Fin (N + 1) → ℝ≥0)
    (hτ : Monotone τ) (ξ : Fin N → (ℕ → ℝ) → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianFiltration (τ i.castSucc)] (ξ i))
    (hξ2 : ∀ i, MemLp (ξ i) 2 brownianDyadicMeasure) :
    (∫ ω, brownianStepIntegral brownianDyadicPath τ ξ ω ∂brownianDyadicMeasure) = 0 :=
  brownianStepIntegral_mean brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable τ hτ ξ hξ hξ2

theorem brownianDyadicPath_stepIntegral_isometry {N : ℕ} (τ : Fin (N + 1) → ℝ≥0)
    (hτ : Monotone τ) (ξ : Fin N → (ℕ → ℝ) → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianFiltration (τ i.castSucc)] (ξ i))
    (hξ2 : ∀ i, MemLp (ξ i) 2 brownianDyadicMeasure) :
    (∫ ω, brownianStepIntegral brownianDyadicPath τ ξ ω ^ 2 ∂brownianDyadicMeasure) =
      ∑ i : Fin N, ((τ i.succ).val - (τ i.castSucc).val) *
        ∫ ω, ξ i ω ^ 2 ∂brownianDyadicMeasure :=
  brownianStepIntegral_isometry brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable τ hτ ξ hξ hξ2

end TimeTraps.Probability
