module

public import TimeTraps.Probability.BrownianAffineLocalTimeBounded

@[expose] public section

/-! At a fixed horizon, the actual affine occupation measure equals the
measure with the scaled density, on the same event for every measurable
set and test. Nonnegative tests may have infinite integrals. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

def affineBrownianOccupationDensityMeasure (x σ : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) : Measure ℝ :=
  volume.withDensity (fun a => ENNReal.ofReal (affineBrownianOccupationDensity x σ a T ω))

theorem affineBrownianOccupationDensityMeasure_measurable (x σ : ℝ) (T : ℝ≥0) :
    Measurable (affineBrownianOccupationDensityMeasure x σ T) :=
  measurable_withDensity (((affineBrownianOccupationDensity_timeSlice_measurable x σ T).comp
    measurable_swap).ennreal_ofReal)

theorem affineBrownianOccupationDensityMeasure_eq (x : ℝ) {σ : ℝ} (hσ : 0 < σ)
    {T : ℝ≥0} {ω : ℕ → ℝ} (hω : brownianLocalTimeTimeMeasureRegular T ω) :
    affineBrownianOccupationDensityMeasure x σ T ω =
      brownianOccupationMeasure (affineBrownianInput x σ) T ω := by
  apply Measure.ext
  intro s hs
  have hg : Measurable (s.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hs
  have hb : ∀ a, |s.indicator (fun _ => (1 : ℝ)) a| ≤ 1 := by
    intro a
    by_cases ha : a ∈ s <;> simp [ha]
  have ho := affineBrownianOccupationDensity_bounded_occupation x hσ hω hg hb
  rw [affineBrownianOccupationDensityMeasure,
    withDensity_ofReal_apply_indicator (fun a => affineBrownianOccupationDensity_nonneg x hσ a T ω) hs ho.1,
    brownianOccupationMeasure,
    finite_map_apply_ofReal_indicator
      (brownianOccupationMeasure_path_measurable (affineBrownianInput_jointlyMeasurable x σ) ω) hs]
  rw [ho.2.2]
  exact congrArg ENNReal.ofReal (intervalIntegral.integral_of_le T.coe_nonneg
    (f := fun s' => s.indicator (fun _ => (1 : ℝ))
      (affineBrownianInput x σ s'.toNNReal ω)) (μ := volume))

theorem affineBrownianOccupationDensityMeasure_eq_ae (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      affineBrownianOccupationDensityMeasure x σ T ω =
        brownianOccupationMeasure (affineBrownianInput x σ) T ω :=
  (brownianLocalTimeTimeMeasureRegular_ae T).mono
    (fun _ hω => affineBrownianOccupationDensityMeasure_eq x hσ hω)

theorem affineBrownianOccupationDensityMeasure_mass (x : ℝ) {σ : ℝ} (hσ : 0 < σ)
    {T : ℝ≥0} {ω : ℕ → ℝ} (hω : brownianLocalTimeTimeMeasureRegular T ω) :
    affineBrownianOccupationDensityMeasure x σ T ω univ = ENNReal.ofReal T.val := by
  rw [affineBrownianOccupationDensityMeasure_eq x hσ hω]
  exact brownianOccupationMeasure_univ (affineBrownianInput_jointlyMeasurable x σ) T ω

theorem affineBrownianOccupationDensity_lintegral (x : ℝ) {σ : ℝ} (hσ : 0 < σ)
    {T : ℝ≥0} {ω : ℕ → ℝ} (hω : brownianLocalTimeTimeMeasureRegular T ω)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ a, g a * ENNReal.ofReal (affineBrownianOccupationDensity x σ a T ω)) =
      ∫⁻ s, g (affineBrownianInput x σ s.toNNReal ω) ∂volume.restrict (Ioc (0 : ℝ) T.val) := by
  have hw : Measurable (fun a => affineBrownianOccupationDensity x σ a T ω) :=
    Measurable.of_uncurry_right (f := fun a ω => affineBrownianOccupationDensity x σ a T ω) (y := ω)
      (affineBrownianOccupationDensity_timeSlice_measurable x σ T)
  calc
    _ = ∫⁻ a, g a ∂affineBrownianOccupationDensityMeasure x σ T ω := by
      rw [affineBrownianOccupationDensityMeasure,
        lintegral_withDensity_eq_lintegral_mul _ hw.ennreal_ofReal hg]
      simp only [Pi.mul_apply, mul_comm]
    _ = ∫⁻ a, g a ∂brownianOccupationMeasure (affineBrownianInput x σ) T ω := by
      rw [affineBrownianOccupationDensityMeasure_eq x hσ hω]
    _ = _ := lintegral_map hg
      (brownianOccupationMeasure_path_measurable (affineBrownianInput_jointlyMeasurable x σ) ω)

end TimeTraps.Probability

end
