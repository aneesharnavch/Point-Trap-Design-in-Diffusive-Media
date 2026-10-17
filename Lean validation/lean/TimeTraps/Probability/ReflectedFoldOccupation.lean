module

public import TimeTraps.Analysis.ReflectedFoldDensity
public import TimeTraps.Probability.BrownianAffineLocalTimeMeasure
public import TimeTraps.Probability.ReflectedFoldTrajectory

@[expose] public section

/-! The actual folded affine Brownian trajectory has the density obtained
by summing the two lattice preimages of its affine occupation density.
At each fixed horizon the existing occupation event gives total mass T,
almost-everywhere finiteness, and a genuine real integrable density.
No reflected-diffusion or Skorokhod identification is assumed. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

def foldedOccupationDensityENNReal (L D x : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) (y : ℝ) : ℝ≥0∞ :=
  (Ioo 0 L).indicator (reflectedFoldDensity L (fun a =>
    ENNReal.ofReal (affineBrownianOccupationDensity x (Real.sqrt (2 * D)) a T ω))) y

def foldedOccupationDensity (L D x : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) (y : ℝ) : ℝ :=
  (foldedOccupationDensityENNReal L D x T ω y).toReal

theorem foldedOccupationDensityENNReal_measurable (L D x : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) :
    Measurable (foldedOccupationDensityENNReal L D x T ω) := by
  have hf : Measurable (fun a => affineBrownianOccupationDensity x (Real.sqrt (2 * D)) a T ω) :=
    Measurable.of_uncurry_right
      (f := fun a ω => affineBrownianOccupationDensity x (Real.sqrt (2 * D)) a T ω) (y := ω)
      (affineBrownianOccupationDensity_timeSlice_measurable x (Real.sqrt (2 * D)) T)
  exact (reflectedFoldDensity_measurable L hf.ennreal_ofReal).indicator measurableSet_Ioo

theorem foldedOccupationDensityENNReal_measure_eq (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) {T : ℝ≥0} {ω : ℕ → ℝ}
    (hω : brownianLocalTimeTimeMeasureRegular T ω) :
    volume.withDensity (foldedOccupationDensityENNReal L D x T ω) =
      brownianOccupationMeasure (foldedTrajectory L D x brownianDyadicPath) T ω := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  have hf : Measurable (fun a => ENNReal.ofReal
      (affineBrownianOccupationDensity x (Real.sqrt (2 * D)) a T ω)) :=
    (Measurable.of_uncurry_right
      (f := fun a ω => affineBrownianOccupationDensity x (Real.sqrt (2 * D)) a T ω) (y := ω)
      (affineBrownianOccupationDensity_timeSlice_measurable x (Real.sqrt (2 * D)) T)).ennreal_ofReal
  calc
    _ = (affineBrownianOccupationDensityMeasure x (Real.sqrt (2 * D)) T ω).map (reflectedFold L) := by
      change volume.withDensity ((Ioo 0 L).indicator (reflectedFoldDensity L (fun a =>
        ENNReal.ofReal (affineBrownianOccupationDensity x (Real.sqrt (2 * D)) a T ω)))) = _
      rw [withDensity_indicator measurableSet_Ioo]
      exact (reflectedFoldDensity_map L hL hf).symm
    _ = (brownianOccupationMeasure (affineBrownianInput x (Real.sqrt (2 * D))) T ω).map
        (reflectedFold L) := by rw [affineBrownianOccupationDensityMeasure_eq x hσ hω]
    _ = _ := by
      rw [brownianOccupationMeasure, Measure.map_map (reflectedFold_measurable L)
        (brownianOccupationMeasure_path_measurable
          (affineBrownianInput_jointlyMeasurable x (Real.sqrt (2 * D))) ω)]
      rfl

theorem foldedOccupationDensityENNReal_mass (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) {T : ℝ≥0} {ω : ℕ → ℝ}
    (hω : brownianLocalTimeTimeMeasureRegular T ω) :
    (∫⁻ y, foldedOccupationDensityENNReal L D x T ω y) = ENNReal.ofReal T.val := by
  have hm := congrArg (fun μ : Measure ℝ => μ univ)
    (foldedOccupationDensityENNReal_measure_eq L hL D hD x hω)
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hm
  exact hm.trans (brownianOccupationMeasure_univ
    (foldedTrajectory_joint_measurable L D x brownianDyadicPath brownianDyadicPath_jointly_measurable) T ω)

theorem foldedOccupationDensityENNReal_finite_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) {T : ℝ≥0} {ω : ℕ → ℝ}
    (hω : brownianLocalTimeTimeMeasureRegular T ω) :
    ∀ᵐ y ∂volume, foldedOccupationDensityENNReal L D x T ω y < ∞ :=
  ae_lt_top (foldedOccupationDensityENNReal_measurable L D x T ω)
    (by rw [foldedOccupationDensityENNReal_mass L hL D hD x hω]; exact ENNReal.ofReal_ne_top)

theorem foldedOccupationDensity_integrable_mass (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) {T : ℝ≥0} {ω : ℕ → ℝ}
    (hω : brownianLocalTimeTimeMeasureRegular T ω) :
    Integrable (foldedOccupationDensity L D x T ω) volume ∧
      (∫ y, foldedOccupationDensity L D x T ω y) = T.val := by
  refine ⟨integrable_toReal_of_lintegral_ne_top
    (foldedOccupationDensityENNReal_measurable L D x T ω).aemeasurable
    (by rw [foldedOccupationDensityENNReal_mass L hL D hD x hω]; exact ENNReal.ofReal_ne_top), ?_⟩
  change (∫ y, (foldedOccupationDensityENNReal L D x T ω y).toReal) = T.val
  calc
    _ = (∫⁻ y, foldedOccupationDensityENNReal L D x T ω y).toReal :=
      integral_toReal (foldedOccupationDensityENNReal_measurable L D x T ω).aemeasurable
        (foldedOccupationDensityENNReal_finite_ae L hL D hD x hω)
    _ = (ENNReal.ofReal T.val).toReal :=
      congrArg ENNReal.toReal (foldedOccupationDensityENNReal_mass L hL D hD x hω)
    _ = T.val := ENNReal.toReal_ofReal T.coe_nonneg

theorem foldedOccupationDensity_measure_eq (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) {T : ℝ≥0} {ω : ℕ → ℝ}
    (hω : brownianLocalTimeTimeMeasureRegular T ω) :
    volume.withDensity (fun y => ENNReal.ofReal (foldedOccupationDensity L D x T ω y)) =
      brownianOccupationMeasure (foldedTrajectory L D x brownianDyadicPath) T ω := by
  calc
    _ = volume.withDensity (foldedOccupationDensityENNReal L D x T ω) := by
      apply withDensity_congr_ae
      filter_upwards [foldedOccupationDensityENNReal_finite_ae L hL D hD x hω] with y hy
      exact ENNReal.ofReal_toReal hy.ne
    _ = _ := foldedOccupationDensityENNReal_measure_eq L hL D hD x hω

theorem foldedOccupationDensity_measure_eq_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      volume.withDensity (fun y => ENNReal.ofReal (foldedOccupationDensity L D x T ω y)) =
        brownianOccupationMeasure (foldedTrajectory L D x brownianDyadicPath) T ω :=
  (brownianLocalTimeTimeMeasureRegular_ae T).mono
    (fun _ hω => foldedOccupationDensity_measure_eq L hL D hD x hω)

end TimeTraps.Probability

end
