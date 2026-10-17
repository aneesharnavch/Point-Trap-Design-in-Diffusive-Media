module

public import TimeTraps.Probability.BrownianStepIntegralIncrement

@[expose] public section

/-! Finite stochastic sums with left-adapted square-integrable coefficients.
The deterministic grid is nondecreasing, so zero-length intervals and the
empty sum are included. This is a finite construction, not a completed
stochastic integration space. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

noncomputable def brownianStepIntegral (B : ℝ≥0 → Ω → ℝ) {N : ℕ}
    (τ : Fin (N + 1) → ℝ≥0) (ξ : Fin N → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin N, ξ i ω * (B (τ i.succ) ω - B (τ i.castSucc) ω)

theorem brownianStepIntegral_memLp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0)
    (hτ : Monotone τ) (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hξ2 : ∀ i, MemLp (ξ i) 2 P) : MemLp (brownianStepIntegral B τ ξ) 2 P :=
  memLp_finsetSum _ (fun i _ => brownian_weighted_increment_memLp hB hBm
    (hτ (Fin.castSucc_le_succ i)) (hξ i) (hξ2 i))

theorem brownianStepIntegral_integrable (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0)
    (hτ : Monotone τ) (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hξ2 : ∀ i, MemLp (ξ i) 2 P) : Integrable (brownianStepIntegral B τ ξ) P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact (brownianStepIntegral_memLp hB hBm τ hτ ξ hξ hξ2).integrable (by norm_num)

theorem brownianStepIntegral_mean (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0)
    (hτ : Monotone τ) (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hξ2 : ∀ i, MemLp (ξ i) 2 P) :
    (∫ ω, brownianStepIntegral B τ ξ ω ∂P) = 0 := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  calc
    _ = ∑ i : Fin N, ∫ ω, ξ i ω * (B (τ i.succ) ω - B (τ i.castSucc) ω) ∂P :=
      integral_finsetSum _ (fun i _ => brownian_weighted_increment_integrable hB hBm
        (hτ (Fin.castSucc_le_succ i)) (hξ i) ((hξ2 i).integrable (by norm_num)))
    _ = ∑ _ : Fin N, (0 : ℝ) := Finset.sum_congr rfl (fun i _ =>
      brownian_weighted_increment_mean hB hBm (hτ (Fin.castSucc_le_succ i))
        (hξ i) ((hξ2 i).integrable (by norm_num)))
    _ = 0 := Finset.sum_const_zero

theorem brownianStepIntegral_stronglyMeasurable (hBm : ∀ t, Measurable (B t))
    {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ) (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i)) :
    StronglyMeasurable[brownianNaturalFiltration B hBm (τ (Fin.last N))]
      (brownianStepIntegral B τ ξ) := by
  change StronglyMeasurable[brownianNaturalFiltration B hBm (τ (Fin.last N))]
    (fun ω => ∑ i : Fin N,
    ξ i ω * (B (τ i.succ) ω - B (τ i.castSucc) ω))
  apply Finset.stronglyMeasurable_fun_sum
  intro i _
  have hl := (brownianNaturalFiltration B hBm).mono (hτ (Fin.le_last i.castSucc))
  have hr := (brownianNaturalFiltration B hBm).mono (hτ (Fin.le_last i.succ))
  exact ((hξ i).mono hl).mul
    (((brownianNaturalFiltration_stronglyAdapted B hBm (τ i.succ)).mono hr).sub
      ((brownianNaturalFiltration_stronglyAdapted B hBm (τ i.castSucc)).mono hl))

end TimeTraps.Probability
