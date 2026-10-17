module

public import TimeTraps.Probability.BrownianIntegralProcess
public import Mathlib.Probability.Process.Predictable

@[expose] public section

/-! The elementary integrands are predictable for Mathlib's predictable
σ-algebra of the raw natural filtration. Real-time representatives vanish
outside their nonnegative half-open intervals. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem brownianElementaryProcess_nnreal (s t r : ℝ≥0) (ξ : Ω → ℝ) (ω : Ω) :
    brownianElementaryProcess s t ξ (r.val, ω) = if r ∈ Ioc s t then ξ ω else 0 := by
  simp only [brownianElementaryProcess, brownianIntervalIndicator, Set.indicator_apply]
  change (if r ∈ Ioc s t then 1 else 0) * ξ ω = _
  split_ifs <;> simp

theorem brownianElementaryProcess_predictable {B : ℝ≥0 → Ω → ℝ}
    (hBm : ∀ t, Measurable (B t)) (s t : ℝ≥0) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ) :
    IsStronglyPredictable (brownianNaturalFiltration B hBm)
      (fun r ω => brownianElementaryProcess s t ξ (r.val, ω)) := by
  apply Measurable.stronglyMeasurable
  intro U hU
  by_cases h0 : (0 : ℝ) ∈ U
  · have he : (Function.uncurry (fun (r : ℝ≥0) ω =>
        brownianElementaryProcess s t ξ (r.val, ω))) ⁻¹' U =
        (Ioc s t ×ˢ (ξ ⁻¹' Uᶜ))ᶜ := by
      ext ⟨r, ω⟩
      change brownianElementaryProcess s t ξ (r.val, ω) ∈ U ↔
        ¬ (r ∈ Ioc s t ∧ ξ ω ∉ U)
      rw [brownianElementaryProcess_nnreal]
      by_cases hr : r ∈ Ioc s t <;> simp [hr, h0]
    rw [he]
    exact (measurableSet_predictable_Ioc_prod s t (hξ.measurable hU.compl)).compl
  · have he : (Function.uncurry (fun (r : ℝ≥0) ω =>
        brownianElementaryProcess s t ξ (r.val, ω))) ⁻¹' U =
        Ioc s t ×ˢ (ξ ⁻¹' U) := by
      ext ⟨r, ω⟩
      change brownianElementaryProcess s t ξ (r.val, ω) ∈ U ↔
        r ∈ Ioc s t ∧ ξ ω ∈ U
      rw [brownianElementaryProcess_nnreal]
      by_cases hr : r ∈ Ioc s t <;> simp [hr, h0]
    rw [he]
    exact measurableSet_predictable_Ioc_prod s t (hξ.measurable hU)

end TimeTraps.Probability
