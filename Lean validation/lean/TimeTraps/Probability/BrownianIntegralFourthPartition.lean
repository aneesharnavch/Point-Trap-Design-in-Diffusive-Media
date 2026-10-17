module

public import TimeTraps.Probability.BrownianIntegralFourthPartitionData

@[expose] public section

/-! Fourth-energy estimates for the original finite partition stochastic
sum and for that same process in the existing completed Brownian integral. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianStepIntegral_fourth_memLp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ)
    (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hξ4 : ∀ i, MemLp (ξ i) 4 P) : MemLp (brownianStepIntegral B τ ξ) 4 P := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have h := brownianFourthPartialSum_memLp hB hBm (brownianIntegralGridTime τ)
    (brownianIntegralGridTime_monotone hτ) (brownianFourthExtendedCoefficient ξ)
    (brownianFourthExtendedCoefficient_adapted hBm τ ξ hξ)
    (brownianFourthExtendedCoefficient_memLp ξ hξ4) N
  have he : brownianFourthPartialSum B (brownianIntegralGridTime τ) (brownianFourthExtendedCoefficient ξ) N =
      brownianStepIntegral B τ ξ := funext (brownianFourthPartialSum_eq_step B τ ξ)
  rwa [he] at h

theorem brownianStepIntegral_fourth_energy_bound (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ)
    (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hξ4 : ∀ i, MemLp (ξ i) 4 P) :
    (∫ ω, brownianStepIntegral B τ ξ ω ^ 4 ∂P) ≤
      150 * ∫ ω, (∑ i : Fin N, ((τ i.succ).val - (τ i.castSucc).val) * ξ i ω ^ 2) ^ 2 ∂P := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hb := brownianFourthPartialSum_energy_bound hB hBm (brownianIntegralGridTime τ)
    (brownianIntegralGridTime_monotone hτ) (brownianFourthExtendedCoefficient ξ)
    (brownianFourthExtendedCoefficient_adapted hBm τ ξ hξ)
    (brownianFourthExtendedCoefficient_memLp ξ hξ4) N
  simpa only [brownianFourthPartialSum_eq_step, brownianFourthEnergy_eq_partition] using hb

theorem brownianIntegral_fourth_energy_bound_of_step_representation (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ)
    (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hξ4 : ∀ i, MemLp (ξ i) 4 P) (f : brownianIntegralSpace B hBm P)
    (hf : brownianIntegral hB f =ᵐ[P] brownianStepIntegral B τ ξ) :
    (∫ ω, brownianIntegral hB f ω ^ 4 ∂P) ≤
      150 * ∫ ω, (∑ i : Fin N, ((τ i.succ).val - (τ i.castSucc).val) * ξ i ω ^ 2) ^ 2 ∂P := by
  calc
    _ = ∫ ω, brownianStepIntegral B τ ξ ω ^ 4 ∂P := integral_congr_ae (hf.pow_const 4)
    _ ≤ _ := brownianStepIntegral_fourth_energy_bound hB hBm τ hτ ξ hξ hξ4

end TimeTraps.Probability
