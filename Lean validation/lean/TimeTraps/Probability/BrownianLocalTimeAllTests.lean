module

public import TimeTraps.Probability.BrownianLocalTimeAllTimes

@[expose] public section

/-! The same full-probability event supports every nonnegative horizon
and every measurable test in the indicated classes. These uncountable
quantifiers follow from pathwise measure equality on that event. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

theorem brownianLocalTimeTimeField_all_times_lintegral_ae :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ T : ℝ≥0, ∀ g : ℝ → ℝ≥0∞, Measurable g →
      (∫⁻ a, g a * ENNReal.ofReal (brownianLocalTimeTimeField a T ω)) =
        ∫⁻ s, g (brownianDyadicPath s.toNNReal ω) ∂volume.restrict (Ioc (0 : ℝ) T.val) := by
  filter_upwards [brownianLocalTimeTimeMeasureRegular_all_times_ae] with ω hω
  intro T g hg
  exact brownianLocalTimeTimeMeasureRegular_lintegral (hω T) hg

theorem brownianLocalTimeTimeField_all_times_bounded_occupation_ae :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ T : ℝ≥0, ∀ g : ℝ → ℝ, Measurable g →
      ∀ M : ℝ, (∀ a, |g a| ≤ M) →
        Integrable (fun a => g a * brownianLocalTimeTimeField a T ω) volume ∧
          IntervalIntegrable (fun s => g (brownianDyadicPath s.toNNReal ω)) volume 0 T.val ∧
          (∫ a, g a * brownianLocalTimeTimeField a T ω) =
            ∫ s in (0 : ℝ)..T.val, g (brownianDyadicPath s.toNNReal ω) := by
  filter_upwards [brownianLocalTimeTimeMeasureRegular_all_times_ae] with ω hω
  intro T g hg M hb
  exact brownianLocalTimeTimeMeasureRegular_bounded_occupation (hω T) hg hb

end TimeTraps.Probability
