module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-! A finite extended nonnegative mean implies almost-sure finite values
and an ordinary integrable representative with that same mean. Applied
to a literal lifetime, this derives finiteness rather than assuming
eventual killing. No stopping-time property is needed. -/

namespace TimeTraps.Probability

open MeasureTheory
open scoped ENNReal

theorem extendedLifetime_finite_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ≥0∞) (hf : AEMeasurable f μ)
    {C : ℝ} (hC : 0 ≤ C) (hmean : (∫⁻ ω, f ω ∂μ) = ENNReal.ofReal C) :
    (∀ᵐ ω ∂μ, f ω < ∞) ∧ Integrable (fun ω => (f ω).toReal) μ ∧
      (∫ ω, (f ω).toReal ∂μ) = C := by
  have hfinite : (∫⁻ ω, f ω ∂μ) ≠ ∞ := by
    rw [hmean]
    exact ENNReal.ofReal_ne_top
  have hvalues : ∀ᵐ ω ∂μ, f ω < ∞ := ae_lt_top' hf hfinite
  refine ⟨hvalues, integrable_toReal_of_lintegral_ne_top hf hfinite, ?_⟩
  rw [integral_toReal hf hvalues, hmean, ENNReal.toReal_ofReal hC]

end TimeTraps.Probability
