module

public import TimeTraps.Probability.BrownianIntegralProcess

@[expose] public section

/-! Data of an elementary left-adapted L² process on an ordered deterministic
interval. Zero-width intervals are permitted. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

structure BrownianIntegralElementary (B : ℝ≥0 → Ω → ℝ)
    (hBm : ∀ t, Measurable (B t)) (P : Measure Ω) where
  left : ℝ≥0
  right : ℝ≥0
  ordered : left ≤ right
  coefficient : Ω → ℝ
  adapted : StronglyMeasurable[brownianNaturalFiltration B hBm left] coefficient
  squareIntegrable : MemLp coefficient 2 P

end TimeTraps.Probability
