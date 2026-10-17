module

public import TimeTraps.Probability.ReflectedFoldOccupation
public import TimeTraps.Probability.BrownianLocalTimeAllTimes

@[expose] public section

/-! Literal occupation identities for the actual folded trajectory.
One full-probability event works for every horizon, every positive interval
length and diffusion scale, every affine starting point, and every test
in the stated classes. Boundary density values are chosen zero; no
boundary-local-time or reflected-diffusion identification is used. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

theorem foldedOccupationDensity_lintegral (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) {T : ℝ≥0} {ω : ℕ → ℝ}
    (hω : brownianLocalTimeTimeMeasureRegular T ω) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ y, g y * ENNReal.ofReal (foldedOccupationDensity L D x T ω y)) =
      ∫⁻ s, g (foldedTrajectory L D x brownianDyadicPath s.toNNReal ω)
        ∂volume.restrict (Ioc (0 : ℝ) T.val) := by
  have hw : Measurable (foldedOccupationDensity L D x T ω) :=
    (foldedOccupationDensityENNReal_measurable L D x T ω).ennreal_toReal
  calc
    _ = ∫⁻ y, g y ∂volume.withDensity
        (fun y => ENNReal.ofReal (foldedOccupationDensity L D x T ω y)) := by
      rw [lintegral_withDensity_eq_lintegral_mul _ hw.ennreal_ofReal hg]
      simp only [Pi.mul_apply, mul_comm]
    _ = ∫⁻ y, g y ∂brownianOccupationMeasure (foldedTrajectory L D x brownianDyadicPath) T ω := by
      rw [foldedOccupationDensity_measure_eq L hL D hD x hω]
    _ = _ := lintegral_map hg (brownianOccupationMeasure_path_measurable
      (foldedTrajectory_joint_measurable L D x brownianDyadicPath brownianDyadicPath_jointly_measurable) ω)

theorem foldedOccupationDensity_bounded_occupation (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) {T : ℝ≥0} {ω : ℕ → ℝ}
    (hω : brownianLocalTimeTimeMeasureRegular T ω) {g : ℝ → ℝ}
    (hg : Measurable g) {M : ℝ} (hb : ∀ y, |g y| ≤ M) :
    Integrable (fun y => g y * foldedOccupationDensity L D x T ω y) volume ∧
      IntervalIntegrable (fun s => g (foldedTrajectory L D x brownianDyadicPath s.toNNReal ω)) volume 0 T.val ∧
      (∫ y, g y * foldedOccupationDensity L D x T ω y) =
        ∫ s in (0 : ℝ)..T.val, g (foldedTrajectory L D x brownianDyadicPath s.toNNReal ω) := by
  have hj : Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => foldedTrajectory L D x brownianDyadicPath p.1 p.2) :=
    foldedTrajectory_joint_measurable L D x brownianDyadicPath brownianDyadicPath_jointly_measurable
  refine ⟨(foldedOccupationDensity_integrable_mass L hL D hD x hω).1.bdd_mul hg.aestronglyMeasurable
    (Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using hb y)),
    brownianItoDrift_bounded_intervalIntegrable hg hj hb T ω, ?_⟩
  have hw : Measurable (foldedOccupationDensity L D x T ω) :=
    (foldedOccupationDensityENNReal_measurable L D x T ω).ennreal_toReal
  calc
    _ = ∫ y, g y ∂volume.withDensity
        (fun y => ENNReal.ofReal (foldedOccupationDensity L D x T ω y)) := by
      rw [integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
        (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [ENNReal.toReal_ofReal (show 0 ≤ foldedOccupationDensity L D x T ω y from ENNReal.toReal_nonneg),
        smul_eq_mul]
      exact mul_comm _ _
    _ = ∫ y, g y ∂brownianOccupationMeasure (foldedTrajectory L D x brownianDyadicPath) T ω := by
      rw [foldedOccupationDensity_measure_eq L hL D hD x hω]
    _ = ∫ s, g (foldedTrajectory L D x brownianDyadicPath s.toNNReal ω)
        ∂volume.restrict (Ioc (0 : ℝ) T.val) :=
      integral_map (brownianOccupationMeasure_path_measurable hj ω).aemeasurable hg.aestronglyMeasurable
    _ = _ := (intervalIntegral.integral_of_le T.coe_nonneg).symm

theorem foldedOccupationDensity_measure_eq_all_times_ae :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ T : ℝ≥0, ∀ L : ℝ, 0 < L →
      ∀ D : ℝ, 0 < D → ∀ x : ℝ,
        volume.withDensity (fun y => ENNReal.ofReal (foldedOccupationDensity L D x T ω y)) =
          brownianOccupationMeasure (foldedTrajectory L D x brownianDyadicPath) T ω := by
  filter_upwards [brownianLocalTimeTimeMeasureRegular_all_times_ae] with ω hω
  intro T L hL D hD x
  exact foldedOccupationDensity_measure_eq L hL D hD x (hω T)

theorem foldedOccupationDensity_lintegral_all_times_ae :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ T : ℝ≥0, ∀ L : ℝ, 0 < L →
      ∀ D : ℝ, 0 < D → ∀ x : ℝ, ∀ g : ℝ → ℝ≥0∞, Measurable g →
        (∫⁻ y, g y * ENNReal.ofReal (foldedOccupationDensity L D x T ω y)) =
          ∫⁻ s, g (foldedTrajectory L D x brownianDyadicPath s.toNNReal ω)
            ∂volume.restrict (Ioc (0 : ℝ) T.val) := by
  filter_upwards [brownianLocalTimeTimeMeasureRegular_all_times_ae] with ω hω
  intro T L hL D hD x g hg
  exact foldedOccupationDensity_lintegral L hL D hD x (hω T) hg

theorem foldedOccupationDensity_bounded_occupation_all_times_ae :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ T : ℝ≥0, ∀ L : ℝ, 0 < L →
      ∀ D : ℝ, 0 < D → ∀ x : ℝ, ∀ g : ℝ → ℝ, Measurable g →
        ∀ M : ℝ, (∀ y, |g y| ≤ M) →
          Integrable (fun y => g y * foldedOccupationDensity L D x T ω y) volume ∧
            IntervalIntegrable
              (fun s => g (foldedTrajectory L D x brownianDyadicPath s.toNNReal ω)) volume 0 T.val ∧
            (∫ y, g y * foldedOccupationDensity L D x T ω y) =
              ∫ s in (0 : ℝ)..T.val, g (foldedTrajectory L D x brownianDyadicPath s.toNNReal ω) := by
  filter_upwards [brownianLocalTimeTimeMeasureRegular_all_times_ae] with ω hω
  intro T L hL D hD x g hg M hb
  exact foldedOccupationDensity_bounded_occupation L hL D hD x (hω T) hg hb

end TimeTraps.Probability
