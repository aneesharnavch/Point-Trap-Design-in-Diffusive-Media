module

public import TimeTraps.Probability.ReflectedInteriorOccupationSpatial

@[expose] public section

/-! Literal occupation identities for the actual interior local-time
coefficient, with the explicit zero extension in
`reflectedInteriorOccupationDensity`. At each fixed horizon one event
works for every test in the stated class. The proof exchanges spatial
and probability null sets; it does not assert pointwise equality at all
levels on that event. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem reflectedInteriorOccupationDensity_measure_ae
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      volume.withDensity (fun a => ENNReal.ofReal (reflectedInteriorOccupationDensity L D x T ω a)) =
        brownianOccupationMeasure (foldedTrajectory L D x brownianDyadicPath) T ω := by
  filter_upwards [reflectedInteriorOccupationDensity_spatial_ae L hL D hD x T,
    brownianLocalTimeTimeMeasureRegular_ae T] with ω he hω
  calc
    _ = volume.withDensity (fun a => ENNReal.ofReal (foldedOccupationDensity L D x T ω a)) := by
      apply withDensity_congr_ae
      exact he.fun_comp ENNReal.ofReal
    _ = _ := foldedOccupationDensity_measure_eq L hL D hD x hω

theorem reflectedInteriorOccupationDensity_integrable_mass_ae
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      Integrable (reflectedInteriorOccupationDensity L D x T ω) volume ∧
        (∫ a, reflectedInteriorOccupationDensity L D x T ω a) = T.val := by
  filter_upwards [reflectedInteriorOccupationDensity_spatial_ae L hL D hD x T,
    brownianLocalTimeTimeMeasureRegular_ae T] with ω he hω
  have hm := foldedOccupationDensity_integrable_mass L hL D hD x hω
  exact ⟨hm.1.congr he.symm, (integral_congr_ae he).trans hm.2⟩

theorem reflectedInteriorOccupationDensity_lintegral_ae
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ g : ℝ → ℝ≥0∞, Measurable g →
      (∫⁻ a, g a * ENNReal.ofReal (reflectedInteriorOccupationDensity L D x T ω a)) =
        ∫⁻ s, g (foldedTrajectory L D x brownianDyadicPath s.toNNReal ω)
          ∂volume.restrict (Ioc (0 : ℝ) T.val) := by
  filter_upwards [reflectedInteriorOccupationDensity_spatial_ae L hL D hD x T,
    brownianLocalTimeTimeMeasureRegular_ae T] with ω he hω
  intro g hg
  calc
    _ = ∫⁻ a, g a * ENNReal.ofReal (foldedOccupationDensity L D x T ω a) := by
      apply lintegral_congr_ae
      filter_upwards [he] with a ha
      rw [ha]
    _ = _ := foldedOccupationDensity_lintegral L hL D hD x hω hg

theorem reflectedInteriorOccupationDensity_bounded_occupation_ae
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ g : ℝ → ℝ, Measurable g →
      ∀ M : ℝ, (∀ a, |g a| ≤ M) →
        Integrable (fun a => g a * reflectedInteriorOccupationDensity L D x T ω a) volume ∧
          IntervalIntegrable
            (fun s => g (foldedTrajectory L D x brownianDyadicPath s.toNNReal ω)) volume 0 T.val ∧
          (∫ a, g a * reflectedInteriorOccupationDensity L D x T ω a) =
            ∫ s in (0 : ℝ)..T.val, g (foldedTrajectory L D x brownianDyadicPath s.toNNReal ω) := by
  filter_upwards [reflectedInteriorOccupationDensity_spatial_ae L hL D hD x T,
    brownianLocalTimeTimeMeasureRegular_ae T] with ω he hω
  intro g hg M hb
  have hm := foldedOccupationDensity_bounded_occupation L hL D hD x hω hg hb
  have hp : (fun a => g a * reflectedInteriorOccupationDensity L D x T ω a) =ᵐ[volume]
      (fun a => g a * foldedOccupationDensity L D x T ω a) := by
    filter_upwards [he] with a ha
    rw [ha]
  exact ⟨hm.1.congr hp.symm, hm.2.1, (integral_congr_ae hp).trans hm.2.2⟩

end TimeTraps.Probability
