module

public import TimeTraps.Probability.BrownianFoldSlopeGlobalCharacteristic
public import TimeTraps.Probability.CharacteristicSetIndependence

@[expose] public section

/-! Every increment of the actual continuous fold-slope integral is
independent of the original Brownian past. The mixed characteristic
identity is tested against arbitrary integrable past-measurable complex
variables, then characteristic uniqueness gives sigma-algebra independence. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem brownianFoldSlopeGlobalPath_increment_char (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) {s t : ℝ≥0} (hst : s ≤ t) (u : ℝ) :
    (∫ ω, brownianRealChar u (brownianFoldSlopeGlobalPath L hL x hσ t ω -
      brownianFoldSlopeGlobalPath L hL x hσ s ω) ∂brownianDyadicMeasure) =
      Complex.exp (-((t.val - s.val : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2) := by
  have he := brownianFoldSlopeGlobalPath_increment_mixed_char L hL x hσ hst
    (Z := fun _ => (1 : ℂ)) (integrable_const 1) stronglyMeasurable_const u
  simpa only [one_mul, integral_const, probReal_univ, one_smul] using he

theorem brownianFoldSlopeGlobalPath_increment_indep_past (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap
      (fun ω => brownianFoldSlopeGlobalPath L hL x hσ t ω -
        brownianFoldSlopeGlobalPath L hL x hσ s ω) (borel ℝ))
      (brownianFiltration s) brownianDyadicMeasure := by
  apply indep_comap_of_characteristic_multiplier_tests (brownianFiltration.le s)
    (((brownianFoldSlopeGlobalPath_measurable L hL x hσ t).sub
      (brownianFoldSlopeGlobalPath_measurable L hL x hσ s)).aemeasurable)
  intro Z hZ hZi u
  change (∫ ω, Z ω * brownianRealChar u
      (brownianFoldSlopeGlobalPath L hL x hσ t ω - brownianFoldSlopeGlobalPath L hL x hσ s ω)
        ∂brownianDyadicMeasure) =
    (∫ ω, Z ω ∂brownianDyadicMeasure) *
      ∫ ω, brownianRealChar u
        (brownianFoldSlopeGlobalPath L hL x hσ t ω - brownianFoldSlopeGlobalPath L hL x hσ s ω)
          ∂brownianDyadicMeasure
  rw [brownianFoldSlopeGlobalPath_increment_char L hL x hσ hst u]
  exact brownianFoldSlopeGlobalPath_increment_mixed_char L hL x hσ hst hZi hZ u

end TimeTraps.Probability
