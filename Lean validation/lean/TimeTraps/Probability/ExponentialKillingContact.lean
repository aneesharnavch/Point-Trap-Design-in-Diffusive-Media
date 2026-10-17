module

public import TimeTraps.Probability.ExponentialKillingSurvival

@[expose] public section

/-! Finite nonnegative weighted contact hazards. The contact functions are
measurable inputs; their identification with diffusion local times is a
separate stochastic construction. -/

namespace TimeTraps.Probability

open Set MeasureTheory
open scoped BigOperators

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

noncomputable def weightedContactHazard (κ : ι → ℝ) (ℓ : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i, κ i * ℓ i ω

theorem weightedContactHazard_measurable (κ : ι → ℝ) (ℓ : ι → Ω → ℝ)
    (hℓ : ∀ i, Measurable (ℓ i)) : Measurable (weightedContactHazard κ ℓ) := by
  unfold weightedContactHazard
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.mul (hℓ i)

omit [MeasurableSpace Ω] in
theorem weightedContactHazard_nonneg (κ : ι → ℝ) (ℓ : ι → Ω → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (hℓ : ∀ i ω, 0 ≤ ℓ i ω) (ω : Ω) :
    0 ≤ weightedContactHazard κ ℓ ω :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hκ i) (hℓ i ω))

theorem exponentialKilling_weighted_contact_conditional (μ : Measure Ω)
    (κ : ι → ℝ) (ℓ : ι → Ω → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (hℓ : ∀ i, Measurable (ℓ i)) (hℓnonneg : ∀ i ω, 0 ≤ ℓ i ω)
    (B : Set Ω) (hB : MeasurableSet B) :
    exponentialKillingMeasure μ
      {p : Ω × ℝ | p.1 ∈ B ∧ (∑ i, κ i * ℓ i p.1) < p.2} =
      ∫⁻ ω in B, ENNReal.ofReal (Real.exp (-(∑ i, κ i * ℓ i ω))) ∂μ :=
  exponentialKilling_conditional_survival μ (weightedContactHazard κ ℓ)
    (weightedContactHazard_measurable κ ℓ hℓ) (weightedContactHazard_nonneg κ ℓ hκ hℓnonneg) B hB

theorem exponentialKilling_weighted_contact_survival (μ : Measure Ω)
    (κ : ι → ℝ) (ℓ : ι → Ω → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (hℓ : ∀ i, Measurable (ℓ i)) (hℓnonneg : ∀ i ω, 0 ≤ ℓ i ω) :
    exponentialKillingMeasure μ {p : Ω × ℝ | (∑ i, κ i * ℓ i p.1) < p.2} =
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-(∑ i, κ i * ℓ i ω))) ∂μ :=
  exponentialKilling_survival μ (weightedContactHazard κ ℓ)
    (weightedContactHazard_measurable κ ℓ hℓ) (weightedContactHazard_nonneg κ ℓ hκ hℓnonneg)

end TimeTraps.Probability
