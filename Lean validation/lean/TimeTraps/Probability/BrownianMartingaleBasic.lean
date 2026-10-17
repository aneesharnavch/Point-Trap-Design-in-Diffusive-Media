module

public import TimeTraps.Probability.BrownianMartingaleFiltration

@[expose] public section

/-! The constructed Brownian process is a martingale in its raw natural
filtration. The conditional equalities hold almost surely. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem brownian_martingale_natural {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) : Martingale B (brownianNaturalFiltration B hBm) P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  refine ⟨brownianNaturalFiltration_stronglyAdapted B hBm, ?_⟩
  intro s t hst
  have h := condExp_add (μ := P)
    ((hB.integrable_eval t).sub (hB.integrable_eval s)) (hB.integrable_eval s)
    (brownianNaturalFiltration B hBm s)
  have he : (B t - B s) + B s = B t := sub_add_cancel _ _
  rw [he, condExp_of_stronglyMeasurable ((brownianNaturalFiltration B hBm).le s)
    (brownianNaturalFiltration_stronglyAdapted B hBm s) (hB.integrable_eval s)] at h
  refine h.trans ?_
  filter_upwards [brownian_increment_condExp hB hBm hst] with ω hω
  change P[B t - B s | brownianNaturalFiltration B hBm s] ω = 0 at hω
  change P[B t - B s | brownianNaturalFiltration B hBm s] ω + B s ω = B s ω
  rw [hω, zero_add]

theorem brownianDyadicPath_martingale :
    Martingale brownianDyadicPath brownianFiltration brownianDyadicMeasure :=
  brownian_martingale_natural brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable

end TimeTraps.Probability
