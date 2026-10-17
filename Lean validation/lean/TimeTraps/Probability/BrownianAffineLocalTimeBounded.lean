module

public import TimeTraps.Probability.BrownianAffineLocalTimeOccupation
public import TimeTraps.Probability.BrownianLocalTimeTimeMeasure

@[expose] public section

/-! The affine occupation formula for all bounded Borel tests, on the
single fixed-horizon occupation event. The same event gives integrability
of the actual spatial density and its exact total mass. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

theorem affineBrownianInput_jointlyMeasurable (x σ : ℝ) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => affineBrownianInput x σ p.1 p.2) := by
  change Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => x + σ * brownianDyadicPath p.1 p.2)
  exact measurable_const.add (measurable_const.mul brownianDyadicPath_jointly_measurable)

theorem affineBrownianOccupationDensity_timeSlice_measurable (x σ : ℝ) (T : ℝ≥0) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => affineBrownianOccupationDensity x σ p.1 T p.2) := by
  have ht : Measurable (fun p : ℝ × (ℕ → ℝ) => ((p.1, T), p.2)) :=
    (measurable_fst.prodMk measurable_const).prodMk measurable_snd
  have hm := (affineBrownianOccupationDensity_jointlyMeasurable x σ).comp ht
  exact hm

theorem affineBrownianOccupationDensity_bounded_occupation (x : ℝ) {σ : ℝ} (hσ : 0 < σ)
    {T : ℝ≥0} {ω : ℕ → ℝ} (hω : brownianLocalTimeTimeMeasureRegular T ω)
    {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hb : ∀ a, |g a| ≤ M) :
    Integrable (fun a => g a * affineBrownianOccupationDensity x σ a T ω) volume ∧
      IntervalIntegrable (fun s => g (affineBrownianInput x σ s.toNNReal ω)) volume 0 T.val ∧
      (∫ a, g a * affineBrownianOccupationDensity x σ a T ω) =
        ∫ s in (0 : ℝ)..T.val, g (affineBrownianInput x σ s.toNNReal ω) := by
  have ht : Measurable (fun b => g (x + σ * b)) :=
    hg.comp (measurable_const.add (measurable_const.mul measurable_id))
  have ho := brownianLocalTimeTimeMeasureRegular_bounded_occupation hω ht
    (fun b => hb (x + σ * b))
  refine ⟨affine_density_integrable g (fun a => brownianLocalTimeTimeField a T ω) x hσ.ne' ho.1,
    ho.2.1, ?_⟩
  exact (affine_density_pairing g (fun a => brownianLocalTimeTimeField a T ω) x hσ).trans ho.2.2

theorem affineBrownianOccupationDensity_integrable_mass (x : ℝ) {σ : ℝ} (hσ : 0 < σ)
    {T : ℝ≥0} {ω : ℕ → ℝ} (hω : brownianLocalTimeTimeMeasureRegular T ω) :
    Integrable (fun a => affineBrownianOccupationDensity x σ a T ω) volume ∧
      (∫ a, affineBrownianOccupationDensity x σ a T ω) = T.val := by
  have h := affineBrownianOccupationDensity_bounded_occupation x hσ hω
    (g := fun _ => 1) measurable_const (M := 1) (fun _ => by norm_num)
  simpa only [one_mul, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] using
    And.intro h.1 h.2.2

end TimeTraps.Probability
