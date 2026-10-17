module

public import TimeTraps.Probability.BrownianLocalTimeAllTests
public import TimeTraps.Probability.BrownianAffineLocalTimeMeasure

@[expose] public section

/-! A single Brownian occupation event is valid at every time and for
every starting point and positive affine scale. These occupation
identities do not assert common all-level Tanaka path regularity. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

theorem affineBrownianOccupationDensityMeasure_all_times_ae :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ T : ℝ≥0, ∀ x σ : ℝ, 0 < σ →
      affineBrownianOccupationDensityMeasure x σ T ω =
        brownianOccupationMeasure (affineBrownianInput x σ) T ω := by
  filter_upwards [brownianLocalTimeTimeMeasureRegular_all_times_ae] with ω hω
  intro T x σ hσ
  exact affineBrownianOccupationDensityMeasure_eq x hσ (hω T)

theorem affineBrownianOccupationDensity_all_times_mass_ae :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ T : ℝ≥0, ∀ x σ : ℝ, 0 < σ →
      Integrable (fun a => affineBrownianOccupationDensity x σ a T ω) volume ∧
        (∫ a, affineBrownianOccupationDensity x σ a T ω) = T.val := by
  filter_upwards [brownianLocalTimeTimeMeasureRegular_all_times_ae] with ω hω
  intro T x σ hσ
  exact affineBrownianOccupationDensity_integrable_mass x hσ (hω T)

theorem affineBrownianOccupationDensity_all_times_lintegral_ae :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ T : ℝ≥0, ∀ x σ : ℝ, 0 < σ →
      ∀ g : ℝ → ℝ≥0∞, Measurable g →
        (∫⁻ a, g a * ENNReal.ofReal (affineBrownianOccupationDensity x σ a T ω)) =
          ∫⁻ s, g (affineBrownianInput x σ s.toNNReal ω)
            ∂volume.restrict (Ioc (0 : ℝ) T.val) := by
  filter_upwards [brownianLocalTimeTimeMeasureRegular_all_times_ae] with ω hω
  intro T x σ hσ g hg
  exact affineBrownianOccupationDensity_lintegral x hσ (hω T) hg

theorem affineBrownianOccupationDensity_all_times_bounded_occupation_ae :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ T : ℝ≥0, ∀ x σ : ℝ, 0 < σ →
      ∀ g : ℝ → ℝ, Measurable g → ∀ M : ℝ, (∀ a, |g a| ≤ M) →
        Integrable (fun a => g a * affineBrownianOccupationDensity x σ a T ω) volume ∧
          IntervalIntegrable (fun s => g (affineBrownianInput x σ s.toNNReal ω)) volume 0 T.val ∧
          (∫ a, g a * affineBrownianOccupationDensity x σ a T ω) =
            ∫ s in (0 : ℝ)..T.val, g (affineBrownianInput x σ s.toNNReal ω) := by
  filter_upwards [brownianLocalTimeTimeMeasureRegular_all_times_ae] with ω hω
  intro T x σ hσ g hg M hb
  exact affineBrownianOccupationDensity_bounded_occupation x hσ (hω T) hg hb

end TimeTraps.Probability
